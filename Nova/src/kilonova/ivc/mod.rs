//! Non-uniform IVC on the native-field HFS v2 with CycleFold (PLAN.md P5, D1 = (a)).
//!
//! This is the recursive layer of `kilonova::hfs`. It replaces the v1 recursion
//! (`kilonova::{PublicParams, RecursiveSNARK}`, B15) without modifying it:
//!
//! - one **primary augmented circuit per predicate** over `E1::Scalar` ([`circuit`]); all K
//!   are padded to common dimensions and form the HFS family;
//! - one fixed **CycleFold circuit** over `E2::Scalar = E1::Base` ([`cyclefold`]) that performs
//!   the E1 group operations of each fold; its instances are folded with Nova's relaxed-R1CS
//!   NIFS inside the primary circuit ([`gadgets`]);
//! - a native [`RecursiveSNARK`] (`new`, `prove_step`, `verify`). `verify` checks only the final
//!   accumulators (link hash, HFS decider, CycleFold relaxed R1CS, last incoming instance), so
//!   every earlier step is authenticated through the recursion alone.
//!
//! P4 (`docs/P4-plan.md`, IVC version 2): the predicates form an authenticated
//! [`PredicateFamily`](crate::kilonova::family::PredicateFamily) (stable ids, canonical matrix
//! encoding, selector descriptor) whose digest is the HFS transcript digest and enters
//! `pp_digest` and every link hash. Each circuit evaluates the program's selection function φ
//! ([`program::PredicateProgram`]) on its input state and enforces `φ(i, z_i) = k` (G4), and
//! extends the in-circuit Poseidon trace chain `trace_{i+1} = H(TAG_TRACE, trace_i, k)` with its
//! constant k. [`RecursiveSNARK::verify`] takes no schedule: it recovers the trace hash from the
//! proof through the final link hash and returns it (G3); [`RecursiveSNARK::verify_schedule`]
//! compares it with an expected schedule.
use crate::{
  constants::NUM_HASH_BITS,
  digest::{DigestComputer, SimpleDigestible},
  errors::NovaError,
  frontend::{shape_cs::ShapeCS, solver::SatisfyingAssignment, ConstraintSystem, SynthesisError},
  gadgets::utils::{scalar_as_base, to_bignat_repr},
  kilonova::{
    count_constraints,
    family::{FamilyMeta, PredicateFamily},
    hfs::{
      decide, num_vars, CcsShape, Direct, HfsError, HfsParams, HfsProof, IncomingInstance, Layer,
      RunningInstance, RunningWitness, Span, Variant, NIFS,
    },
    shape_cs_to_shape,
    transcript::v2::absorb_commitment,
    CountingSummary, MAX_SETUP_CONSTRAINTS, MAX_SETUP_ITERATIONS,
  },
  r1cs::{R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness},
  traits::{
    commitment::{CommitmentEngineTrait, CommitmentTrait},
    Engine, RO2ConstantsCircuit, ROConstants, ROConstantsCircuit, ROTrait,
  },
  Commitment, CommitmentKey,
};
use core::marker::PhantomData;
use ff::Field;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

pub mod breakdown;
pub(crate) mod circuit;
pub mod cyclefold;
pub mod fixtures;
pub(crate) mod gadgets;
pub mod program;
pub mod shape;
#[cfg(test)]
mod tests;

use circuit::{PrimaryCircuit, PrimaryInputs, PrimaryParams};
use cyclefold::{
  cf_fold_prove, cyclefold_instance_witness, num_inputs, Coords, CycleFoldCircuit, CycleFoldInputs,
};
pub use program::{PredicateProgram, Scheduled};
use shape::{ccs_is_satisfied, KnShapeCS};
pub use shape::{enforce_pow5, PrimaryTemplate, KN_NATIVE_POW5};

/// Version of the recursive layer (link hash, trace chain, CycleFold layout). Version 2 (P4):
/// the link hash's digest slot carries the family digest, and every circuit enforces φ.
pub const IVC_VERSION: u64 = 2;
/// Tag of the link hash: "KNIVC" ‖ v2 ‖ 1.
pub const TAG_LINK: u64 = 0x4b4e_4956_4302_0001;
/// Tag of the trace chain: "KNIVC" ‖ v2 ‖ 2.
pub const TAG_TRACE: u64 = 0x4b4e_4956_4302_0002;
/// Label of the CycleFold commitment key.
pub const CF_CK_LABEL: &[u8] = b"kn-ivc-cf-ck";

/// How the running index is carried, as needed by the recursive layer.
pub trait IvcVariant<E: Engine>: Variant<E> {
  /// Direct (committed λ, group operations in CycleFold) or Span (public λ).
  const DIRECT: bool;
  /// The index commitments (Direct) or nothing (Span).
  fn index_commitments(idx: &Self::Index) -> Vec<Commitment<E>>;
  /// λ (Span) or nothing (Direct).
  fn index_scalars(idx: &Self::Index) -> Vec<E::Scalar>;
  /// Index of the default (trivially satisfied) running instance.
  fn default_index(t: usize, k: usize) -> Self::Index;
  /// Coordinates of the index commitments.
  fn index_coords(idx: &Self::Index) -> Vec<Coords<E::Base>> {
    Self::index_commitments(idx)
      .iter()
      .map(|c| c.to_coordinates())
      .collect()
  }
}

impl<E: Engine> IvcVariant<E> for Direct {
  const DIRECT: bool = true;
  fn index_commitments(idx: &Self::Index) -> Vec<Commitment<E>> {
    idx.clone()
  }
  fn index_scalars(_idx: &Self::Index) -> Vec<E::Scalar> {
    Vec::new()
  }
  fn default_index(t: usize, _k: usize) -> Self::Index {
    vec![Commitment::<E>::default(); t]
  }
}

impl<E: Engine> IvcVariant<E> for Span {
  const DIRECT: bool = false;
  fn index_commitments(_idx: &Self::Index) -> Vec<Commitment<E>> {
    Vec::new()
  }
  fn index_scalars(idx: &Self::Index) -> Vec<E::Scalar> {
    idx.clone()
  }
  fn default_index(_t: usize, k: usize) -> Self::Index {
    vec![E::Scalar::ZERO; k]
  }
}

/// Where a rejection happens.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum IvcLayer {
  /// Arguments, lengths, predicate ids (before any cryptographic check).
  Input,
  /// Setup (fixed point, caps, template).
  Setup,
  /// Prover-side failure (synthesis or HFS input validation).
  Prover,
  /// Final link hash `u_n.io = H(pp, n, z_0, z_n, trace_n, U_n, cfU_n)`.
  LinkHash,
  /// HFS decider on the running ACCS (comm_W, comm_M openings, claims).
  Decider,
  /// CycleFold accumulator: relaxed R1CS satisfaction and commitment openings.
  CycleFold,
  /// Last incoming CCCS: CCS satisfaction of its predicate and comm_W opening.
  LastIncoming,
  /// The recovered trace differs from an expected schedule (`verify_schedule` only).
  Trace,
}

/// Errors of the recursive layer. [`IvcError::layer`] names the detection layer.
#[derive(Debug, thiserror::Error)]
pub enum IvcError {
  /// Bad arguments.
  #[error("input: {0}")]
  Input(String),
  /// Setup failed (e.g. no fixed point within the caps).
  #[error("setup: {0}")]
  Setup(String),
  /// The prover could not produce a step.
  #[error("prover: {0}")]
  Prover(String),
  /// The final link hash does not match.
  #[error("link hash: the last instance does not hash the claimed state")]
  LinkHash,
  /// The running ACCS fails the decider.
  #[error("decider: {0}")]
  Decider(HfsError),
  /// The CycleFold accumulator is not satisfied.
  #[error("cyclefold: {0}")]
  CycleFold(String),
  /// The last incoming instance is not satisfied.
  #[error("last incoming instance: {0}")]
  LastIncoming(String),
  /// The recovered trace is not the expected schedule's.
  #[error("trace: {0}")]
  Trace(String),
}

impl IvcError {
  /// The detection layer.
  pub fn layer(&self) -> IvcLayer {
    match self {
      IvcError::Input(_) => IvcLayer::Input,
      IvcError::Setup(_) => IvcLayer::Setup,
      IvcError::Prover(_) => IvcLayer::Prover,
      IvcError::LinkHash => IvcLayer::LinkHash,
      IvcError::Decider(_) => IvcLayer::Decider,
      IvcError::CycleFold(_) => IvcLayer::CycleFold,
      IvcError::LastIncoming(_) => IvcLayer::LastIncoming,
      IvcError::Trace(_) => IvcLayer::Trace,
    }
  }
}

impl From<SynthesisError> for IvcError {
  fn from(e: SynthesisError) -> Self {
    IvcError::Prover(format!("synthesis: {e}"))
  }
}

impl From<NovaError> for IvcError {
  fn from(e: NovaError) -> Self {
    IvcError::Prover(format!("{e}"))
  }
}

impl From<HfsError> for IvcError {
  fn from(e: HfsError) -> Self {
    match e.layer() {
      Layer::Decider => IvcError::Decider(e),
      _ => IvcError::Prover(format!("hfs: {e}")),
    }
  }
}

/// One iteration of the setup fixed point.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IvcSetupIteration {
  /// Sum-check rounds assumed by the circuits of this iteration.
  pub s: usize,
  /// Y-phase rounds assumed.
  pub s_prime: usize,
  /// Largest primary row count (constraints + native power rows).
  pub max_rows: usize,
  /// Largest primary witness length.
  pub max_aux: usize,
}

/// Raw size of one primary circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimarySize {
  /// R1CS rows.
  pub r1cs_rows: usize,
  /// Native power rows.
  pub pow_rows: usize,
  /// Witness length.
  pub num_aux: usize,
  /// Public outputs.
  pub num_io: usize,
}

/// What `setup` measured. Not part of the public parameters.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IvcSetupReport {
  /// Fixed-point history; the last entry is the converged one.
  pub iterations: Vec<IvcSetupIteration>,
  /// Raw sizes per predicate.
  pub primary_raw: Vec<PrimarySize>,
  /// Common padded rows m.
  pub primary_m: usize,
  /// Common padded witness length.
  pub primary_num_w: usize,
  /// CycleFold constraints, variables and inputs before padding.
  pub cyclefold_raw: (usize, usize, usize),
  /// CycleFold shape after `R1CSShape::pad` (constraints, variables).
  pub cyclefold_padded: (usize, usize),
}

#[derive(Serialize)]
struct PpDigestView<'a> {
  version: u64,
  variant: &'a str,
  template: PrimaryTemplate,
  arity: usize,
  k: usize,
  family_digest: String,
  cf_shape_digest: String,
  cf_ck_label: &'a [u8],
  cf_ck_len: usize,
}

impl SimpleDigestible for PpDigestView<'_> {}

/// Public parameters of the v2 recursion for a family of K predicates.
pub struct PublicParams<E1, E2, V>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  V: IvcVariant<E1>,
{
  arity: usize,
  tpl: PrimaryTemplate,
  hfs: HfsParams<E1>,
  cf_shape: R1CSShape<E2>,
  ck_cf: CommitmentKey<E2>,
  ro_consts_cf: ROConstants<E2>,
  primary: PrimaryParams<E1, E2>,
  iota: Vec<Vec<Coords<E1::Base>>>,
  family: FamilyMeta<E1::Scalar>,
  pp_digest: E1::Scalar,
  _p: PhantomData<V>,
}

impl<E1, E2, V> PublicParams<E1, E2, V>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  V: IvcVariant<E1>,
{
  /// Builds the parameters: CycleFold shape, the primary fixed point on the sum-check sizes,
  /// the padded [`PredicateFamily`] (stable ids, selector, digest) and the keys. Fails (never
  /// raises a cap) if the fixed point does not converge within `MAX_SETUP_ITERATIONS` or a
  /// circuit exceeds `MAX_SETUP_CONSTRAINTS`.
  pub fn setup<PS: PredicateProgram<E1::Scalar>>(
    predicates: &PS,
    tpl: PrimaryTemplate,
  ) -> Result<(Self, IvcSetupReport), IvcError> {
    Self::setup_impl(predicates, tpl, None)
  }

  /// [`Self::setup`] for a pinned family: rejects (layer Setup) unless the family digest is
  /// `expected` (a reordered member or a substituted matrix changes it).
  pub fn setup_pinned<PS: PredicateProgram<E1::Scalar>>(
    predicates: &PS,
    tpl: PrimaryTemplate,
    expected: E1::Scalar,
  ) -> Result<(Self, IvcSetupReport), IvcError> {
    Self::setup_impl(predicates, tpl, Some(expected))
  }

  fn setup_impl<PS: PredicateProgram<E1::Scalar>>(
    predicates: &PS,
    tpl: PrimaryTemplate,
    expected: Option<E1::Scalar>,
  ) -> Result<(Self, IvcSetupReport), IvcError> {
    let k = predicates.num_predicates();
    let arity = predicates.arity();
    if k == 0 || arity == 0 {
      return Err(IvcError::Input("empty family or zero arity".into()));
    }
    let template = tpl.template::<E1::Scalar>();
    let t = template.t();

    // ι depends only on (K, t) and the index key label, not on the shapes.
    let dummy = HfsParams::<E1>::new(
      template.clone(),
      vec![CcsShape::new(1, 1, 1, vec![Vec::new(); t])?; k],
    )?;
    let iota: Vec<Vec<Coords<E1::Base>>> = (0..k)
      .map(|i| dummy.iota(i).iter().map(|c| c.to_coordinates()).collect())
      .collect();

    // CycleFold shape.
    let t_idx = if V::DIRECT { t } else { 0 };
    let cf = CycleFoldCircuit::<E1> {
      iota: &iota,
      t_idx,
      inputs: None,
    };
    let mut cs = ShapeCS::<E2>::new();
    cf.synthesize(&mut cs)?;
    let cf_raw = shape_cs_to_shape(&cs);
    let n_cf = num_inputs(t_idx);
    if cf_raw.num_io != n_cf {
      return Err(IvcError::Setup(format!(
        "CycleFold has {} inputs, expected {n_cf}",
        cf_raw.num_io
      )));
    }
    let cf_shape = cf_raw.pad();
    let ck_cf = E2::CE::setup(CF_CK_LABEL, cf_shape.num_cons.max(cf_shape.num_vars));

    // Primary fixed point on (s, s').
    let ro2_consts = RO2ConstantsCircuit::<E1>::default();
    let ro_cf_consts = ROConstantsCircuit::<E2>::default();
    let num_io = 1;
    let mut dims = (1usize, 1usize);
    let mut iterations = Vec::new();
    let (primary, raw) = loop {
      let params = PrimaryParams::<E1, E2> {
        template: template.clone(),
        tag_input: V::TAG_INPUT,
        k,
        s: dims.0,
        s_prime: dims.1,
        arity,
        num_io,
        direct: V::DIRECT,
        iota: iota.clone(),
        n_cf,
        ro2_consts: ro2_consts.clone(),
        ro_cf_consts: ro_cf_consts.clone(),
      };
      for id in 0..k {
        let c = count_primary::<E1, E2, PS, V>(&params, predicates, id)?;
        if c.num_constraints > MAX_SETUP_CONSTRAINTS {
          return Err(IvcError::Setup(format!(
            "predicate {id}: {} constraints > MAX_SETUP_CONSTRAINTS at iteration {}",
            c.num_constraints,
            iterations.len() + 1
          )));
        }
      }
      let raw: Vec<KnShapeCS<E1::Scalar>> = (0..k)
        .into_par_iter()
        .map(|id| {
          let mut cs = KnShapeCS::<E1::Scalar>::default();
          PrimaryCircuit::<E1, E2, PS, V> {
            params: &params,
            predicates,
            k: id,
            inputs: None,
          }
          .synthesize(&mut cs)
          .map(|_| cs)
        })
        .collect::<Result<_, _>>()?;
      let max_rows = raw.iter().map(KnShapeCS::num_rows).max().unwrap_or(0);
      let max_aux = raw.iter().map(KnShapeCS::num_aux).max().unwrap_or(0);
      iterations.push(IvcSetupIteration {
        s: dims.0,
        s_prime: dims.1,
        max_rows,
        max_aux,
      });
      let next = (num_vars(max_rows), num_vars(max_aux + 1 + num_io));
      if next == dims {
        break (params, raw);
      }
      if iterations.len() >= MAX_SETUP_ITERATIONS {
        return Err(IvcError::Setup(format!(
          "no fixed point after {} iterations: {iterations:?}",
          iterations.len()
        )));
      }
      dims = next;
    };

    let last = *iterations.last().expect("at least one iteration");
    let (m, num_w) = (last.max_rows, last.max_aux);
    let shapes = raw
      .iter()
      .map(|cs| cs.to_ccs(tpl, m, num_w))
      .collect::<Result<Vec<_>, _>>()?;
    let family = PredicateFamily::new(
      predicates.family_label(),
      (0..k).map(|i| predicates.member_id(i)).collect(),
      arity,
      predicates.selector_descriptor(),
      template,
      shapes,
    )
    .map_err(|e| IvcError::Setup(format!("family: {e}")))?;
    if let Some(d) = expected {
      family
        .meta()
        .check_digest(d)
        .map_err(|e| IvcError::Setup(format!("{e}")))?;
    }
    let (hfs, family) = family.into_hfs_params::<E1>()?;
    if (hfs.s(), hfs.s_prime()) != (primary.s, primary.s_prime) {
      return Err(IvcError::Setup(
        "HFS dimensions differ from the fixed point".into(),
      ));
    }
    for (i, io) in iota.iter().enumerate() {
      let again: Vec<Coords<E1::Base>> = hfs.iota(i).iter().map(|c| c.to_coordinates()).collect();
      if &again != io {
        return Err(IvcError::Setup("index commitments changed".into()));
      }
    }

    // the HFS transcript digest is the family digest (`HfsParams` built from the family)
    debug_assert_eq!(hfs.digest(), family.digest());
    let view = PpDigestView {
      version: IVC_VERSION,
      variant: V::NAME,
      template: tpl,
      arity,
      k,
      family_digest: format!("{:?}", family.digest()),
      cf_shape_digest: format!("{:?}", cf_shape.digest()),
      cf_ck_label: CF_CK_LABEL,
      cf_ck_len: cf_shape.num_cons.max(cf_shape.num_vars),
    };
    let pp_digest = DigestComputer::<E1::Scalar, _>::new(&view)
      .digest()
      .map_err(|e| IvcError::Setup(format!("digest: {e}")))?;

    let report = IvcSetupReport {
      iterations,
      primary_raw: raw
        .iter()
        .map(|cs| PrimarySize {
          r1cs_rows: cs.num_rows() - cs.num_pow_rows(),
          pow_rows: cs.num_pow_rows(),
          num_aux: cs.num_aux(),
          num_io: cs.num_io(),
        })
        .collect(),
      primary_m: m,
      primary_num_w: num_w,
      cyclefold_raw: (cf_raw.num_cons, cf_raw.num_vars, cf_raw.num_io),
      cyclefold_padded: (cf_shape.num_cons, cf_shape.num_vars),
    };
    Ok((
      Self {
        arity,
        tpl,
        hfs,
        cf_shape,
        ck_cf,
        ro_consts_cf: ROConstants::<E2>::default(),
        primary,
        iota,
        family,
        pp_digest,
        _p: PhantomData,
      },
      report,
    ))
  }

  /// The authenticated family (stable ids, member digests, family digest).
  pub fn family(&self) -> &FamilyMeta<E1::Scalar> {
    &self.family
  }

  /// Digest of all public parameters (bound by every link hash).
  pub fn digest(&self) -> E1::Scalar {
    self.pp_digest
  }

  /// The HFS family parameters (primary shapes, keys, family digest).
  pub fn hfs(&self) -> &HfsParams<E1> {
    &self.hfs
  }

  /// The padded CycleFold shape.
  pub fn cyclefold_shape(&self) -> &R1CSShape<E2> {
    &self.cf_shape
  }

  /// The primary template.
  pub fn template(&self) -> PrimaryTemplate {
    self.tpl
  }

  /// Number of CycleFold public inputs.
  pub fn cyclefold_num_inputs(&self) -> usize {
    self.primary.n_cf
  }

  fn cf_circuit(&self, inputs: Option<CycleFoldInputs<E1>>) -> CycleFoldCircuit<'_, E1> {
    CycleFoldCircuit {
      iota: &self.iota,
      t_idx: if V::DIRECT { self.hfs.t() } else { 0 },
      inputs,
    }
  }

  /// `trace_{i+1} = H(TAG_TRACE, trace_i, k)`, `trace_0 = 0`.
  pub fn trace_next(&self, trace: E1::Scalar, k: usize) -> E1::Scalar {
    let mut ro = E1::RO2::new(Default::default());
    ro.absorb(E1::Scalar::from(TAG_TRACE));
    ro.absorb(trace);
    ro.absorb(E1::Scalar::from(k as u64));
    ro.squeeze(NUM_HASH_BITS)
  }

  /// The trace hash of a schedule.
  pub fn trace_of(&self, ids: &[usize]) -> E1::Scalar {
    ids
      .iter()
      .fold(E1::Scalar::ZERO, |t, &k| self.trace_next(t, k))
  }

  /// The link hash (native twin of `circuit::link_hash`).
  #[allow(clippy::too_many_arguments)]
  pub fn link_hash(
    &self,
    i: usize,
    z0: &[E1::Scalar],
    zi: &[E1::Scalar],
    trace: E1::Scalar,
    run: &RunningInstance<E1, V>,
    cf: &RelaxedR1CSInstance<E2>,
  ) -> E1::Scalar {
    let mut ro = E1::RO2::new(Default::default());
    ro.absorb(E1::Scalar::from(TAG_LINK));
    ro.absorb(self.pp_digest);
    ro.absorb(self.hfs.digest());
    ro.absorb(E1::Scalar::from(i as u64));
    z0.iter().chain(zi).for_each(|z| ro.absorb(*z));
    ro.absorb(trace);
    absorb_commitment::<E1>(&mut ro, &run.comm_w);
    V::absorb_running_index(&mut ro, &run.index);
    ro.absorb(run.u);
    run
      .io
      .iter()
      .chain(&run.r_x)
      .chain(&run.r_y)
      .chain(&run.v)
      .for_each(|x| ro.absorb(*x));
    for c in [&cf.comm_W, &cf.comm_E] {
      let (x, y, inf) = c.to_coordinates();
      ro.absorb(x);
      ro.absorb(y);
      ro.absorb(if inf {
        E1::Scalar::ONE
      } else {
        E1::Scalar::ZERO
      });
    }
    ro.absorb(scalar_as_base::<E2>(cf.u));
    for x in &cf.X {
      for l in to_bignat_repr::<E2::Scalar, E1::Scalar>(x) {
        ro.absorb(l);
      }
    }
    ro.squeeze(NUM_HASH_BITS)
  }

  fn default_running(&self) -> (RunningInstance<E1, V>, RunningWitness<E1>) {
    let (t, k) = (self.hfs.t(), self.hfs.k());
    (
      RunningInstance {
        comm_w: Commitment::<E1>::default(),
        index: V::default_index(t, k),
        u: E1::Scalar::ZERO,
        io: vec![E1::Scalar::ZERO; self.hfs.num_io()],
        r_x: vec![E1::Scalar::ZERO; self.hfs.s()],
        r_y: vec![E1::Scalar::ZERO; self.hfs.s_prime()],
        v: vec![E1::Scalar::ZERO; t + 1],
      },
      RunningWitness {
        w: vec![E1::Scalar::ZERO; self.hfs.num_w()],
        lambda: vec![E1::Scalar::ZERO; k],
      },
    )
  }

  fn dummy_proof(&self) -> HfsProof<E1> {
    let (s, sp, t) = (self.hfs.s(), self.hfs.s_prime(), self.hfs.t());
    let d = self.hfs.template().deg_x();
    let z = E1::Scalar::ZERO;
    HfsProof {
      sc_x: vec![vec![z; d + 1]; s],
      sigma: vec![vec![z; t]],
      tau: vec![vec![z; t]],
      sc_y: vec![vec![z; 3]; sp],
      eps: vec![vec![z; t + 1]],
      theta: vec![vec![z; t + 1]],
    }
  }

  /// Synthesizes predicate `k`'s circuit on `inputs`; returns the new incoming instance, its
  /// witness (padded) and `z_{i+1}`.
  #[allow(clippy::type_complexity)]
  fn synthesize_step<PS: PredicateProgram<E1::Scalar>>(
    &self,
    predicates: &PS,
    k: usize,
    inputs: PrimaryInputs<E1, E2, V>,
  ) -> Result<(IncomingInstance<E1>, Vec<E1::Scalar>, Vec<E1::Scalar>), IvcError> {
    let mut cs = SatisfyingAssignment::<E1>::new();
    let z = PrimaryCircuit::<E1, E2, PS, V> {
      params: &self.primary,
      predicates,
      k,
      inputs: Some(inputs),
    }
    .synthesize(&mut cs)?;
    let mut w = cs.aux_assignment().to_vec();
    if w.len() > self.hfs.num_w() {
      return Err(IvcError::Prover(
        "witness longer than the padded shape".into(),
      ));
    }
    w.resize(self.hfs.num_w(), E1::Scalar::ZERO);
    let io = cs.input_assignment()[1..].to_vec();
    let inc = IncomingInstance::new(&self.hfs, k, &w, io)?;
    let z = z
      .iter()
      .map(|v| v.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<_>, _>>()?;
    Ok((inc, w, z))
  }
}

/// Synthesizes predicate `id`'s primary circuit into a `CountingCS`.
fn count_primary<E1, E2, PS, V>(
  params: &PrimaryParams<E1, E2>,
  predicates: &PS,
  id: usize,
) -> Result<CountingSummary, IvcError>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  PS: PredicateProgram<E1::Scalar>,
  V: IvcVariant<E1>,
{
  Ok(count_constraints::<E1::Scalar, _>(|cs| {
    PrimaryCircuit::<E1, E2, PS, V> {
      params,
      predicates,
      k: id,
      inputs: None,
    }
    .synthesize(cs)
  })?)
}

/// Test hooks that make the prover deviate (rejection tests). Never set in production.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Tamper {
  /// Honest step.
  #[default]
  None,
  /// The circuit receives `z_i + 1` instead of `z_i` (broken state link).
  StateLink,
  /// The circuit receives the counter `i − 1` (repeated counter).
  Counter,
  /// The HFS folds the incoming instance as predicate `(k_prev + 1) mod K` (wrong predicate).
  IncomingPredicate,
  /// The folded witness commitment hint is replaced by `2 · hint` (hint not bound).
  HintW,
  /// The CycleFold witness is generated for a wrong ρ.
  CycleFoldWitness,
}

/// What [`RecursiveSNARK::verify`] establishes about a chain of n steps from `z_0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainOutput<F> {
  /// The final state `z_n`.
  pub zn: Vec<F>,
  /// The trace hash `H_trace*(k_0, …, k_{n−1})` of the ids the circuits executed (each
  /// `k_i = φ(i, z_i)`, enforced in-circuit), recovered from the proof.
  pub trace: F,
  /// The predicate of the last step.
  pub last_id: usize,
}

/// The non-uniform recursive SNARK (uncompressed; `verify` needs the final witnesses, G2).
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RecursiveSNARK<E1, E2, V>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  V: IvcVariant<E1>,
{
  z0: Vec<E1::Scalar>,
  zi: Vec<E1::Scalar>,
  i: usize,
  trace: E1::Scalar,
  r_u: RunningInstance<E1, V>,
  r_w: RunningWitness<E1>,
  l_u: IncomingInstance<E1>,
  l_w: Vec<E1::Scalar>,
  cf_u: RelaxedR1CSInstance<E2>,
  cf_w: RelaxedR1CSWitness<E2>,
}

impl<E1, E2, V> RecursiveSNARK<E1, E2, V>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  V: IvcVariant<E1>,
{
  /// Base step: applies the predicate `k0 = φ(0, z0)` selected by the program to `z0`.
  pub fn new<PS: PredicateProgram<E1::Scalar>>(
    pp: &PublicParams<E1, E2, V>,
    predicates: &PS,
    z0: &[E1::Scalar],
  ) -> Result<Self, IvcError> {
    Self::new_tampered(pp, predicates, z0, None)
  }

  /// [`Self::new`] with a host-forced predicate (`Some(k0)`, test hook: a choice that disagrees
  /// with φ makes the circuit unsatisfied). `None` is the honest prover.
  #[doc(hidden)]
  pub fn new_tampered<PS: PredicateProgram<E1::Scalar>>(
    pp: &PublicParams<E1, E2, V>,
    predicates: &PS,
    z0: &[E1::Scalar],
    forced: Option<usize>,
  ) -> Result<Self, IvcError> {
    if z0.len() != pp.arity {
      return Err(IvcError::Input(format!(
        "|z0| = {} (arity {})",
        z0.len(),
        pp.arity
      )));
    }
    let k0 = match forced {
      Some(k) => k,
      None => predicates
        .select(0, z0)
        .ok_or_else(|| IvcError::Input("φ(0, z0) selects no predicate".into()))?,
    };
    if k0 >= pp.hfs.k() {
      return Err(IvcError::Input(format!(
        "predicate {k0} (K = {}) or |z0| = {} (arity {})",
        pp.hfs.k(),
        z0.len(),
        pp.arity
      )));
    }
    let (r_u, r_w) = pp.default_running();
    let cf_u = RelaxedR1CSInstance::<E2>::default(&pp.ck_cf, &pp.cf_shape);
    let cf_w = RelaxedR1CSWitness::<E2>::default(&pp.cf_shape);
    let dummy_inc = IncomingInstance {
      k: 0,
      comm_w: Commitment::<E1>::default(),
      io: vec![E1::Scalar::ZERO; pp.hfs.num_io()],
    };
    let inputs = PrimaryInputs {
      pp_digest: pp.pp_digest,
      hfs_digest: pp.hfs.digest(),
      i: E1::Scalar::ZERO,
      z0: z0.to_vec(),
      zi: z0.to_vec(),
      trace: E1::Scalar::ZERO,
      run: r_u.clone(),
      inc: dummy_inc,
      proof: pp.dummy_proof(),
      hint_w: Commitment::<E1>::default(),
      hint_m: vec![Commitment::<E1>::default(); if V::DIRECT { pp.hfs.t() } else { 0 }],
      cf_run: cf_u.clone(),
      cf_w: Commitment::<E2>::default(),
      cf_t: Commitment::<E2>::default(),
    };
    let (l_u, l_w, zi) = pp.synthesize_step(predicates, k0, inputs)?;
    Ok(Self {
      z0: z0.to_vec(),
      zi,
      i: 1,
      trace: pp.trace_next(E1::Scalar::ZERO, k0),
      r_u,
      r_w,
      l_u,
      l_w,
      cf_u,
      cf_w,
    })
  }

  /// Applies the predicate `k = φ(i, z_i)` selected by the program to the current state.
  pub fn prove_step<PS: PredicateProgram<E1::Scalar>>(
    &mut self,
    pp: &PublicParams<E1, E2, V>,
    predicates: &PS,
  ) -> Result<(), IvcError> {
    self.prove_step_tampered(pp, predicates, None, Tamper::None)
  }

  /// The predicate φ selects for the next step (`None`: the program has halted).
  pub fn next_predicate<PS: PredicateProgram<E1::Scalar>>(&self, predicates: &PS) -> Option<usize> {
    predicates.select(self.i, &self.zi)
  }

  /// [`Self::prove_step`] with test hooks: `forced = Some(k)` makes the host choose predicate k
  /// regardless of φ, and `tamper` makes the prover deviate (`None`/`Tamper::None` is honest).
  #[doc(hidden)]
  pub fn prove_step_tampered<PS: PredicateProgram<E1::Scalar>>(
    &mut self,
    pp: &PublicParams<E1, E2, V>,
    predicates: &PS,
    forced: Option<usize>,
    tamper: Tamper,
  ) -> Result<(), IvcError> {
    let k = match forced {
      Some(k) => k,
      None => self.next_predicate(predicates).ok_or_else(|| {
        IvcError::Input(format!("φ({}, z_{}) selects no predicate", self.i, self.i))
      })?,
    };
    if k >= pp.hfs.k() {
      return Err(IvcError::Input(format!(
        "predicate {k} out of range (K = {})",
        pp.hfs.k()
      )));
    }
    // 1. HFS fold of (U_i, u_i).
    let mut inc = self.l_u.clone();
    if tamper == Tamper::IncomingPredicate {
      inc.k = (inc.k + 1) % pp.hfs.k();
    }
    let out = NIFS::<E1, V>::prove(
      &pp.hfs,
      std::slice::from_ref(&self.r_u),
      std::slice::from_ref(&self.r_w),
      std::slice::from_ref(&inc),
      std::slice::from_ref(&self.l_w),
    )?;
    let new_u = out.instance;

    // 2. CycleFold instance for the group operations of this fold.
    let m: Vec<(Coords<E1::Base>, Coords<E1::Base>)> = V::index_coords(&self.r_u.index)
      .into_iter()
      .zip(V::index_coords(&new_u.index))
      .collect();
    let mut hint_w = new_u.comm_w;
    if tamper == Tamper::HintW {
      hint_w = hint_w + hint_w;
    }
    let cf_rho = if tamper == Tamper::CycleFoldWitness {
      out.challenges.rho + E1::Scalar::ONE
    } else {
      out.challenges.rho
    };
    let cf_in = CycleFoldInputs::<E1> {
      rho: cf_rho,
      k: inc.k,
      w: [
        self.r_u.comm_w.to_coordinates(),
        inc.comm_w.to_coordinates(),
        new_u.comm_w.to_coordinates(),
      ],
      m,
    };
    let honest_x = (tamper == Tamper::CycleFoldWitness).then(|| {
      let mut honest = cf_in.clone();
      honest.rho = out.challenges.rho;
      pp.cf_circuit(None).public_inputs(&honest)
    });
    let (mut cf_inst, cf_wit) =
      cyclefold_instance_witness::<E1, E2>(&pp.cf_circuit(Some(cf_in)), &pp.cf_shape, &pp.ck_cf)?;
    if let Some(x) = honest_x {
      // The instance keeps the public inputs the primary circuit builds; only the witness is
      // for a wrong ρ, so the CycleFold instance is unsatisfied.
      cf_inst.X = x;
    }
    let (cf_proof, cf_u, cf_w) = cf_fold_prove(
      &pp.ck_cf,
      &pp.ro_consts_cf,
      pp.pp_digest,
      &pp.cf_shape,
      &self.cf_u,
      &self.cf_w,
      &cf_inst,
      &cf_wit,
    )?;

    // 3. Primary circuit of predicate k.
    let mut zi = self.zi.clone();
    if tamper == Tamper::StateLink {
      zi[0] += E1::Scalar::ONE;
    }
    let i = if tamper == Tamper::Counter {
      self.i - 1
    } else {
      self.i
    };
    let inputs = PrimaryInputs {
      pp_digest: pp.pp_digest,
      hfs_digest: pp.hfs.digest(),
      i: E1::Scalar::from(i as u64),
      z0: self.z0.clone(),
      zi,
      trace: self.trace,
      run: self.r_u.clone(),
      inc,
      proof: out.proof,
      hint_w,
      hint_m: V::index_commitments(&new_u.index),
      cf_run: self.cf_u.clone(),
      cf_w: cf_inst.comm_W,
      cf_t: cf_proof.comm_t,
    };
    let (l_u, l_w, z_next) = pp.synthesize_step(predicates, k, inputs)?;

    self.r_u = new_u;
    self.r_w = out.witness;
    self.l_u = l_u;
    self.l_w = l_w;
    self.cf_u = cf_u;
    self.cf_w = cf_w;
    self.zi = z_next;
    self.trace = pp.trace_next(self.trace, k);
    self.i += 1;
    Ok(())
  }

  /// Verifies a chain of `num_steps` steps from `z0`. The verifier takes **no schedule**: the
  /// schedule is fixed by the program's φ inside the circuits, and the trace hash is recovered
  /// from the proof (bound by the final link hash) and returned with `z_n` and the last
  /// predicate. Only final accumulators are checked; the chain is authenticated by the recursion.
  pub fn verify(
    &self,
    pp: &PublicParams<E1, E2, V>,
    num_steps: usize,
    z0: &[E1::Scalar],
  ) -> Result<ChainOutput<E1::Scalar>, IvcError> {
    if num_steps == 0 || z0.len() != pp.arity {
      return Err(IvcError::Input(format!(
        "{num_steps} steps, |z0| = {} (arity {})",
        z0.len(),
        pp.arity
      )));
    }
    let last = self.l_u.k;
    if last >= pp.hfs.k() || self.l_u.io.len() != 1 {
      return Err(IvcError::Input(format!(
        "the last instance claims predicate {last} (K = {})",
        pp.hfs.k()
      )));
    }
    // 1. Link hash (binds n, z_0, z_n, the trace hash and the accumulators).
    let h = pp.link_hash(num_steps, z0, &self.zi, self.trace, &self.r_u, &self.cf_u);
    if self.l_u.io[0] != h {
      return Err(IvcError::LinkHash);
    }
    // 2. Running ACCS.
    decide(&pp.hfs, &self.r_u, &self.r_w).map_err(IvcError::Decider)?;
    // 3. CycleFold accumulator.
    if self.cf_w.W.len() != pp.cf_shape.num_vars
      || self.cf_w.E.len() != pp.cf_shape.num_cons
      || self.cf_u.X.len() != pp.cf_shape.num_io
    {
      return Err(IvcError::CycleFold("lengths".into()));
    }
    pp.cf_shape
      .is_sat_relaxed(&pp.ck_cf, &self.cf_u, &self.cf_w)
      .map_err(|e| IvcError::CycleFold(format!("{e}")))?;
    // 4. Last incoming instance.
    let shape = pp.hfs.shape(last);
    if self.l_w.len() != shape.num_w() || pp.hfs.commit_w(&self.l_w)? != self.l_u.comm_w {
      return Err(IvcError::LastIncoming("comm_W does not open".into()));
    }
    let z = [self.l_w.as_slice(), &[E1::Scalar::ONE], &self.l_u.io].concat();
    if !ccs_is_satisfied(pp.hfs.template(), shape, &z) {
      return Err(IvcError::LastIncoming(format!(
        "not satisfied for predicate {last}"
      )));
    }
    Ok(ChainOutput {
      zn: self.zi.clone(),
      trace: self.trace,
      last_id: last,
    })
  }

  /// [`Self::verify`], then compares the recovered trace with an expected schedule (layer
  /// Trace). The schedule is only a check on the recovered digest, never an input to it.
  pub fn verify_schedule(
    &self,
    pp: &PublicParams<E1, E2, V>,
    num_steps: usize,
    z0: &[E1::Scalar],
    expected: &[usize],
  ) -> Result<ChainOutput<E1::Scalar>, IvcError> {
    let out = self.verify(pp, num_steps, z0)?;
    if expected.len() != num_steps || pp.trace_of(expected) != out.trace {
      return Err(IvcError::Trace(format!(
        "the proven trace is not the expected schedule of length {}",
        expected.len()
      )));
    }
    Ok(out)
  }

  /// Test access to the trace hash and the last instance's predicate (forged-id tests).
  #[doc(hidden)]
  pub fn forge(&mut self) -> (&mut E1::Scalar, &mut usize) {
    (&mut self.trace, &mut self.l_u.k)
  }

  /// Number of steps proven.
  pub fn num_steps(&self) -> usize {
    self.i
  }

  /// Current state `z_i`.
  pub fn outputs(&self) -> &[E1::Scalar] {
    &self.zi
  }

  /// Test access to the running witnesses (tamper tests).
  #[doc(hidden)]
  pub fn running_mut(
    &mut self,
  ) -> (
    &mut RunningInstance<E1, V>,
    &mut RunningWitness<E1>,
    &mut RelaxedR1CSInstance<E2>,
    &mut RelaxedR1CSWitness<E2>,
  ) {
    (&mut self.r_u, &mut self.r_w, &mut self.cf_u, &mut self.cf_w)
  }

  /// The running ACCS and its witness (oracle checks in tests).
  #[doc(hidden)]
  pub fn running(&self) -> (&RunningInstance<E1, V>, &RunningWitness<E1>) {
    (&self.r_u, &self.r_w)
  }

  /// The last incoming instance and witness.
  #[doc(hidden)]
  pub fn last_incoming(&self) -> (&IncomingInstance<E1>, &[E1::Scalar]) {
    (&self.l_u, &self.l_w)
  }
}

/// Counts predicate `id`'s primary circuit at the parameters' dimensions.
pub fn primary_constraint_counts<E1, E2, PS, V>(
  pp: &PublicParams<E1, E2, V>,
  predicates: &PS,
  id: usize,
) -> Result<CountingSummary, IvcError>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  PS: PredicateProgram<E1::Scalar>,
  V: IvcVariant<E1>,
{
  count_primary::<E1, E2, PS, V>(&pp.primary, predicates, id)
}

/// Commitment-key size check used by tests: the primary key covers the padded witness.
#[doc(hidden)]
pub fn ck_covers_padded<E1, E2, V>(pp: &PublicParams<E1, E2, V>) -> bool
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  V: IvcVariant<E1>,
{
  use crate::traits::commitment::Len;
  pp.ck_cf.length() >= pp.cf_shape.num_cons.max(pp.cf_shape.num_vars)
    && pp
      .hfs
      .commit_w(&vec![E1::Scalar::ONE; pp.hfs.num_w()])
      .is_ok()
}

/// Re-export for tests and kn-run.
pub type CycleFoldKey<E2> = CommitmentKey<E2>;
