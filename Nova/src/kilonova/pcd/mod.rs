//! Tree-shaped proof-carrying data on HFS v2 with CycleFold (PLAN.md P6, W4).
//!
//! The family has `K = K_leaf + 2` members ([`circuit`]): one **leaf** circuit per leaf
//! predicate (the P4 chain members), one **merge** circuit with a predecessors and one **dummy**
//! circuit for padding. Leaves and dummies are the recursion base case (no verifier inside;
//! default accumulators). A merge node verifies, in-circuit, one HFS v2 fold of
//! **μ = a running and ν = a incoming instances** (its children's accumulators and their own
//! CCCS instances) and folds the a children's CycleFold accumulators plus one fresh CycleFold
//! instance. Every node outputs one public value, the link hash of its statement
//! `(lo, hi, r, h)` under the task context `(task_id, L)` and of its accumulators.
//!
//! The root verifier ([`NodeProof::verify_root`]) takes no tree structure: it checks the root's
//! statement range, the link hash, the HFS decider, the CycleFold accumulator and the root's
//! own CCCS, and returns the [`RootStatement`] (task id, L, a, range, result R, tree hash).
//! [`TreeParams::root_statement`] computes the expected statement from the task alone.
//!
//! Spec: `docs/protocol-spec.md` §11. Plan: `docs/P6-plan.md`.
use crate::{
  constants::NUM_HASH_BITS,
  digest::{DigestComputer, SimpleDigestible},
  errors::NovaError,
  frontend::{shape_cs::ShapeCS, solver::SatisfyingAssignment, ConstraintSystem, SynthesisError},
  kilonova::{
    count_constraints,
    family::{FamilyMeta, PredicateFamily},
    hfs::{
      decide, num_vars, CcsShape, HfsError, HfsParams, IncomingInstance, Layer, RunningInstance,
      RunningWitness, NIFS,
    },
    ivc::{
      cyclefold::Coords,
      gadgets::limbs_of,
      shape::{ccs_is_satisfied, KnShapeCS},
      IvcSetupIteration, IvcVariant, PrimarySize, PrimaryTemplate,
    },
    shape_cs_to_shape,
    transcript::v2::absorb_commitment,
    CountingSummary, PredicateSet, MAX_SETUP_CONSTRAINTS, MAX_SETUP_ITERATIONS,
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
use std::{collections::HashMap, time::Instant};

pub mod breakdown;
pub(crate) mod circuit;
pub mod cyclefold;
pub(crate) mod gadgets;
pub mod task;
#[cfg(test)]
mod tests;

pub use circuit::NodeRole;
use circuit::{ChildIn, Ctx, NodeCircuit, NodeInputs, NodeParams, RoleIn};
use cyclefold::{
  cf_fold_fresh_prove, cf_fold_relaxed_prove, cyclefold_instance_witness_n, num_inputs_n,
  CycleFoldCircuitN, CycleFoldInputsN,
};
pub use task::{depth_for, LayoutNode, LayoutRole, LeafTask, TreeLayout, TreeTask};

/// Version of the tree PCD layer (link hash, tree hash, CycleFold accumulator layout).
pub const PCD_VERSION: u64 = 1;
/// Tag of the node link hash: "KNPCD" ‖ v1 ‖ 1.
pub const TAG_TREE_LINK: u64 = 0x4b4e_5043_4401_0001;
/// Tag of a leaf's tree hash.
pub const TAG_TREE_LEAF: u64 = 0x4b4e_5043_4401_0002;
/// Tag of a merge node's tree hash.
pub const TAG_TREE_NODE: u64 = 0x4b4e_5043_4401_0003;
/// Tag of a dummy node's tree hash.
pub const TAG_TREE_DUMMY: u64 = 0x4b4e_5043_4401_0004;
/// Position weight of the target result `R = Σ β^p F_{k_p}(x_p)`.
pub const BETA: u64 = 7;
/// Positions, ranges and L are below 2^RANGE_BITS (range-checked in-circuit).
pub const RANGE_BITS: usize = 32;
/// Label of the tree CycleFold commitment key.
pub const TREE_CF_CK_LABEL: &[u8] = b"kn-pcd-cf-ck";

/// Where a rejection happens.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TreeLayer {
  /// Arguments: tree shape, ranges, task context, lengths (before any cryptographic check).
  Input,
  /// Setup (fixed point, caps).
  Setup,
  /// Prover-side failure (synthesis, HFS input validation).
  Prover,
  /// The root statement: range `[0, a^d)` for L, or a mismatch with an expected statement.
  Statement,
  /// The root's link hash does not hash the claimed statement and accumulators.
  LinkHash,
  /// HFS decider on the root's running ACCS.
  Decider,
  /// The root's CycleFold accumulator.
  CycleFold,
  /// The root's own CCCS (its circuit is not satisfied; in-circuit checks of every node end here).
  RootIncoming,
}

/// Errors of the tree PCD layer. [`TreeError::layer`] names the detection layer.
#[derive(Debug, thiserror::Error)]
pub enum TreeError {
  /// Bad arguments.
  #[error("input: {0}")]
  Input(String),
  /// Setup failed.
  #[error("setup: {0}")]
  Setup(String),
  /// The prover could not produce a node.
  #[error("prover: {0}")]
  Prover(String),
  /// The root statement is malformed or not the expected one.
  #[error("statement: {0}")]
  Statement(String),
  /// The root link hash does not match.
  #[error("link hash: the root instance does not hash the claimed statement")]
  LinkHash,
  /// The running ACCS fails the decider.
  #[error("decider: {0}")]
  Decider(HfsError),
  /// The CycleFold accumulator is not satisfied.
  #[error("cyclefold: {0}")]
  CycleFold(String),
  /// The root's own CCCS is not satisfied.
  #[error("root incoming instance: {0}")]
  RootIncoming(String),
}

impl TreeError {
  /// The detection layer.
  pub fn layer(&self) -> TreeLayer {
    match self {
      TreeError::Input(_) => TreeLayer::Input,
      TreeError::Setup(_) => TreeLayer::Setup,
      TreeError::Prover(_) => TreeLayer::Prover,
      TreeError::Statement(_) => TreeLayer::Statement,
      TreeError::LinkHash => TreeLayer::LinkHash,
      TreeError::Decider(_) => TreeLayer::Decider,
      TreeError::CycleFold(_) => TreeLayer::CycleFold,
      TreeError::RootIncoming(_) => TreeLayer::RootIncoming,
    }
  }
}

impl From<SynthesisError> for TreeError {
  fn from(e: SynthesisError) -> Self {
    TreeError::Prover(format!("synthesis: {e}"))
  }
}

impl From<NovaError> for TreeError {
  fn from(e: NovaError) -> Self {
    TreeError::Prover(format!("{e}"))
  }
}

impl From<HfsError> for TreeError {
  fn from(e: HfsError) -> Self {
    match e.layer() {
      Layer::Decider => TreeError::Decider(e),
      _ => TreeError::Prover(format!("hfs: {e}")),
    }
  }
}

/// What `setup` measured. Not part of the public parameters.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TreeSetupReport {
  /// PCD arity a.
  pub a: usize,
  /// HFS running inputs per merge fold (μ = a).
  pub mu: usize,
  /// HFS incoming inputs per merge fold (ν = a).
  pub nu: usize,
  /// Fixed-point history; the last entry is the converged one.
  pub iterations: Vec<IvcSetupIteration>,
  /// Member ids and raw sizes (leaf members, merge, dummy).
  pub members: Vec<(String, PrimarySize)>,
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
  a: usize,
  k_leaf: usize,
  k: usize,
  arity: usize,
  beta: u64,
  range_bits: usize,
  family_digest: String,
  cf_shape_digest: String,
  cf_ck_label: &'a [u8],
  cf_ck_len: usize,
}

impl SimpleDigestible for PpDigestView<'_> {}

/// Public parameters of the tree PCD for a leaf family and arity a.
pub struct TreeParams<E1, E2, V>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  V: IvcVariant<E1>,
{
  a: usize,
  k_leaf: usize,
  arity: usize,
  tpl: PrimaryTemplate,
  hfs: HfsParams<E1>,
  cf_shape: R1CSShape<E2>,
  ck_cf: CommitmentKey<E2>,
  ro_consts_cf: ROConstants<E2>,
  node: NodeParams<E1, E2>,
  family: FamilyMeta<E1::Scalar>,
  pp_digest: E1::Scalar,
  _p: PhantomData<V>,
}

/// Task context shared by every node of one tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TaskCtx<F: ff::PrimeField> {
  /// Task identity.
  pub task_id: F,
  /// Number of real leaves L.
  pub num_leaves: u64,
}

impl<F: ff::PrimeField> TaskCtx<F> {
  /// The context of a task.
  pub fn of(task: &TreeTask<F>) -> Self {
    Self {
      task_id: task.task_id(),
      num_leaves: task.num_leaves() as u64,
    }
  }
}

/// A node's statement.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NodeStatement<F: ff::PrimeField> {
  /// Range start.
  pub lo: u64,
  /// Range end (exclusive).
  pub hi: u64,
  /// `r = Σ_{p ∈ [lo, hi) ∩ [0, L)} β^p F_{k_p}(x_p)`.
  pub result: Vec<F>,
  /// Tree hash of the subtree.
  pub tree_hash: F,
}

/// What [`NodeProof::verify_root`] establishes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RootStatement<F: ff::PrimeField> {
  /// Task identity.
  pub task_id: F,
  /// Number of real leaves L.
  pub num_leaves: u64,
  /// PCD arity a.
  pub arity: usize,
  /// Root range start (0).
  pub lo: u64,
  /// Root range end (a^d).
  pub hi: u64,
  /// Target result R.
  pub result: Vec<F>,
  /// Tree hash.
  pub tree_hash: F,
}

/// A node proof: statement, the node's running HFS accumulator, its own CCCS and its CycleFold
/// accumulator (uncompressed; the root verifier reads the witnesses, G2).
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct NodeProof<E1, E2, V>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  V: IvcVariant<E1>,
{
  ctx: TaskCtx<E1::Scalar>,
  stmt: NodeStatement<E1::Scalar>,
  r_u: RunningInstance<E1, V>,
  r_w: RunningWitness<E1>,
  l_u: IncomingInstance<E1>,
  l_w: Vec<E1::Scalar>,
  cf_u: RelaxedR1CSInstance<E2>,
  cf_w: RelaxedR1CSWitness<E2>,
}

/// Test hooks that make a merge prover deviate (rejection tests). Never set in production.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum NodeTamper {
  /// Honest node.
  #[default]
  None,
  /// The parent receives child c's result + 1 (forged predecessor statement).
  ChildResult(usize),
  /// Child c's CCCS is replaced by a commitment to a garbage witness with the same io (forged
  /// predecessor proof).
  ChildIncoming(usize),
  /// The parent receives the running accumulators of children 0 and 1 swapped.
  SwapRunning,
}

fn hash_native<E1: Engine>(tag: u64, xs: &[E1::Scalar]) -> E1::Scalar {
  let mut ro = E1::RO2::new(Default::default());
  ro.absorb(E1::Scalar::from(tag));
  xs.iter().for_each(|x| ro.absorb(*x));
  ro.squeeze(NUM_HASH_BITS)
}

impl<E1, E2, V> TreeParams<E1, E2, V>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  V: IvcVariant<E1>,
{
  /// Builds the parameters for the leaf predicates `leaf` (stable ids `leaf_ids`) and arity a:
  /// multi-input CycleFold shape, the fixed point on the sum-check sizes over all members, the
  /// padded family `[leaf/0 … leaf/K_leaf−1, merge, dummy]` and its digest, keys from padded
  /// shapes. Fails (never raises a cap) without a fixed point within `MAX_SETUP_ITERATIONS` or
  /// when a member exceeds `MAX_SETUP_CONSTRAINTS`.
  pub fn setup<P: PredicateSet<E1::Scalar>>(
    leaf: &P,
    leaf_ids: &[String],
    a: usize,
    tpl: PrimaryTemplate,
  ) -> Result<(Self, TreeSetupReport), TreeError> {
    let k_leaf = leaf.num_predicates();
    let arity = leaf.arity();
    if a < 2 || k_leaf == 0 || arity == 0 || leaf_ids.len() != k_leaf {
      return Err(TreeError::Input(format!(
        "a = {a}, K_leaf = {k_leaf}, arity = {arity}, {} ids",
        leaf_ids.len()
      )));
    }
    let k = k_leaf + 2;
    let template = tpl.template::<E1::Scalar>();
    let t = template.t();

    let dummy = HfsParams::<E1>::new(
      template.clone(),
      vec![CcsShape::new(1, 1, 1, vec![Vec::new(); t])?; k],
    )?;
    let iota: Vec<Vec<Coords<E1::Base>>> = (0..k)
      .map(|i| dummy.iota(i).iter().map(|c| c.to_coordinates()).collect())
      .collect();

    // Multi-input CycleFold shape (μ = ν = a).
    let t_idx = if V::DIRECT { t } else { 0 };
    let cf = CycleFoldCircuitN::<E1> {
      iota: &iota,
      mu: a,
      nu: a,
      t_idx,
      inputs: None,
    };
    let mut cs = ShapeCS::<E2>::new();
    cf.synthesize(&mut cs)?;
    let cf_raw = shape_cs_to_shape(&cs);
    let n_cf = num_inputs_n(a, a, t_idx);
    if cf_raw.num_io != n_cf {
      return Err(TreeError::Setup(format!(
        "CycleFold has {} inputs, expected {n_cf}",
        cf_raw.num_io
      )));
    }
    let cf_shape = cf_raw.pad();
    let ck_cf = E2::CE::setup(TREE_CF_CK_LABEL, cf_shape.num_cons.max(cf_shape.num_vars));

    let roles: Vec<NodeRole> = (0..k_leaf)
      .map(NodeRole::Leaf)
      .chain([NodeRole::Merge, NodeRole::Dummy])
      .collect();
    let num_io = 1;
    let mut dims = (1usize, 1usize);
    let mut iterations = Vec::new();
    let (node, raw) = loop {
      let params = NodeParams::<E1, E2> {
        template: template.clone(),
        tag_input: V::TAG_INPUT,
        k,
        a,
        s: dims.0,
        s_prime: dims.1,
        arity,
        num_io,
        direct: V::DIRECT,
        iota: iota.clone(),
        n_cf,
        ro2_consts: RO2ConstantsCircuit::<E1>::default(),
        ro_cf_consts: ROConstantsCircuit::<E2>::default(),
      };
      for (id, role) in roles.iter().enumerate() {
        let c = count_node::<E1, E2, P, V>(&params, leaf, *role)?;
        if c.num_constraints > MAX_SETUP_CONSTRAINTS {
          return Err(TreeError::Setup(format!(
            "member {id} ({role:?}): {} constraints > MAX_SETUP_CONSTRAINTS at iteration {}",
            c.num_constraints,
            iterations.len() + 1
          )));
        }
      }
      let raw: Vec<KnShapeCS<E1::Scalar>> = roles
        .par_iter()
        .map(|role| {
          let mut cs = KnShapeCS::<E1::Scalar>::default();
          NodeCircuit::<E1, E2, P, V> {
            params: &params,
            leaf,
            role: *role,
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
        return Err(TreeError::Setup(format!(
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
    let ids: Vec<String> = leaf_ids
      .iter()
      .map(|id| format!("tree/leaf/{id}"))
      .chain([format!("tree/merge-a{a}"), "tree/dummy".to_string()])
      .collect();
    let mut selector = b"kn-pcd-tree-v1".to_vec();
    for x in [
      a as u64,
      k_leaf as u64,
      BETA,
      RANGE_BITS as u64,
      PCD_VERSION,
    ] {
      selector.extend_from_slice(&x.to_le_bytes());
    }
    let family = PredicateFamily::new(
      format!("kn-p6-tree-a{a}"),
      ids.clone(),
      arity,
      selector,
      template,
      shapes,
    )
    .map_err(|e| TreeError::Setup(format!("family: {e}")))?;
    let (hfs, family) = family.into_hfs_params::<E1>()?;
    if (hfs.s(), hfs.s_prime()) != (node.s, node.s_prime) {
      return Err(TreeError::Setup(
        "HFS dimensions differ from the fixed point".into(),
      ));
    }
    for (i, io) in iota.iter().enumerate() {
      let again: Vec<Coords<E1::Base>> = hfs.iota(i).iter().map(|c| c.to_coordinates()).collect();
      if &again != io {
        return Err(TreeError::Setup("index commitments changed".into()));
      }
    }
    let view = PpDigestView {
      version: PCD_VERSION,
      variant: V::NAME,
      template: tpl,
      a,
      k_leaf,
      k,
      arity,
      beta: BETA,
      range_bits: RANGE_BITS,
      family_digest: format!("{:?}", family.digest()),
      cf_shape_digest: format!("{:?}", cf_shape.digest()),
      cf_ck_label: TREE_CF_CK_LABEL,
      cf_ck_len: cf_shape.num_cons.max(cf_shape.num_vars),
    };
    let pp_digest = DigestComputer::<E1::Scalar, _>::new(&view)
      .digest()
      .map_err(|e| TreeError::Setup(format!("digest: {e}")))?;

    let report = TreeSetupReport {
      a,
      mu: a,
      nu: a,
      iterations,
      members: ids
        .into_iter()
        .zip(&raw)
        .map(|(id, cs)| {
          (
            id,
            PrimarySize {
              r1cs_rows: cs.num_rows() - cs.num_pow_rows(),
              pow_rows: cs.num_pow_rows(),
              num_aux: cs.num_aux(),
              num_io: cs.num_io(),
            },
          )
        })
        .collect(),
      primary_m: m,
      primary_num_w: num_w,
      cyclefold_raw: (cf_raw.num_cons, cf_raw.num_vars, cf_raw.num_io),
      cyclefold_padded: (cf_shape.num_cons, cf_shape.num_vars),
    };
    Ok((
      Self {
        a,
        k_leaf,
        arity,
        tpl,
        hfs,
        cf_shape,
        ck_cf,
        ro_consts_cf: ROConstants::<E2>::default(),
        node,
        family,
        pp_digest,
        _p: PhantomData,
      },
      report,
    ))
  }

  /// PCD arity a.
  pub fn arity(&self) -> usize {
    self.a
  }

  /// HFS running inputs per merge fold (μ = a).
  pub fn mu(&self) -> usize {
    self.a
  }

  /// HFS incoming inputs per merge fold (ν = a).
  pub fn nu(&self) -> usize {
    self.a
  }

  /// Number of leaf predicates.
  pub fn k_leaf(&self) -> usize {
    self.k_leaf
  }

  /// Family position of the merge member.
  pub fn merge_id(&self) -> usize {
    self.k_leaf
  }

  /// Family position of the dummy member.
  pub fn dummy_id(&self) -> usize {
    self.k_leaf + 1
  }

  /// Role of family member `id`.
  pub fn role(&self, id: usize) -> Option<NodeRole> {
    match id {
      i if i < self.k_leaf => Some(NodeRole::Leaf(i)),
      i if i == self.k_leaf => Some(NodeRole::Merge),
      i if i == self.k_leaf + 1 => Some(NodeRole::Dummy),
      _ => None,
    }
  }

  fn id_of(&self, role: NodeRole) -> usize {
    match role {
      NodeRole::Leaf(k) => k,
      NodeRole::Merge => self.merge_id(),
      NodeRole::Dummy => self.dummy_id(),
    }
  }

  /// The authenticated family (stable ids, member digests, family digest).
  pub fn family(&self) -> &FamilyMeta<E1::Scalar> {
    &self.family
  }

  /// Digest of all public parameters (bound by every link hash).
  pub fn digest(&self) -> E1::Scalar {
    self.pp_digest
  }

  /// The HFS family parameters.
  pub fn hfs(&self) -> &HfsParams<E1> {
    &self.hfs
  }

  /// The padded CycleFold shape.
  pub fn cyclefold_shape(&self) -> &R1CSShape<E2> {
    &self.cf_shape
  }

  /// Number of CycleFold public inputs.
  pub fn cyclefold_num_inputs(&self) -> usize {
    self.node.n_cf
  }

  /// The primary template.
  pub fn template(&self) -> PrimaryTemplate {
    self.tpl
  }

  fn ctx(&self, c: &TaskCtx<E1::Scalar>) -> Ctx<E1::Scalar> {
    Ctx {
      pp_digest: self.pp_digest,
      hfs_digest: self.hfs.digest(),
      task_id: c.task_id,
      num_leaves: c.num_leaves,
    }
  }

  /// `H(TAG_LEAF, p, k, x)`.
  pub fn leaf_hash(&self, p: u64, k: usize, x: &[E1::Scalar]) -> E1::Scalar {
    let mut xs = vec![E1::Scalar::from(p), E1::Scalar::from(k as u64)];
    xs.extend_from_slice(x);
    hash_native::<E1>(TAG_TREE_LEAF, &xs)
  }

  /// `H(TAG_DUMMY, lo, hi)`.
  pub fn dummy_hash(&self, lo: u64, hi: u64) -> E1::Scalar {
    hash_native::<E1>(
      TAG_TREE_DUMMY,
      &[E1::Scalar::from(lo), E1::Scalar::from(hi)],
    )
  }

  /// `H(TAG_NODE, lo, hi, h_0, …, h_{a−1})`.
  pub fn node_hash(&self, lo: u64, hi: u64, hs: &[E1::Scalar]) -> E1::Scalar {
    let mut xs = vec![E1::Scalar::from(lo), E1::Scalar::from(hi)];
    xs.extend_from_slice(hs);
    hash_native::<E1>(TAG_TREE_NODE, &xs)
  }

  /// The node link hash (native twin of `circuit::link_hash`).
  pub fn link_hash(
    &self,
    ctx: &TaskCtx<E1::Scalar>,
    s: &NodeStatement<E1::Scalar>,
    run: &RunningInstance<E1, V>,
    cf: &RelaxedR1CSInstance<E2>,
  ) -> E1::Scalar {
    let mut ro = E1::RO2::new(Default::default());
    ro.absorb(E1::Scalar::from(TAG_TREE_LINK));
    for x in [
      self.pp_digest,
      self.hfs.digest(),
      ctx.task_id,
      E1::Scalar::from(ctx.num_leaves),
      E1::Scalar::from(s.lo),
      E1::Scalar::from(s.hi),
    ] {
      ro.absorb(x);
    }
    s.result.iter().for_each(|x| ro.absorb(*x));
    ro.absorb(s.tree_hash);
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
    for x in std::iter::once(&cf.u).chain(&cf.X) {
      for l in limbs_of::<E2::Scalar, E1::Scalar>(x) {
        ro.absorb(l);
      }
    }
    ro.squeeze(NUM_HASH_BITS)
  }

  /// The statement a correct tree for `task` must prove at its root (computed from the task
  /// alone: task id, L, the layout for a, R and the tree hash).
  pub fn root_statement(
    &self,
    task: &TreeTask<E1::Scalar>,
    eval: impl Fn(usize, &[E1::Scalar]) -> Vec<E1::Scalar>,
  ) -> RootStatement<E1::Scalar> {
    let layout = task.layout(self.a);
    let mut hashes: HashMap<(usize, u64), E1::Scalar> = HashMap::new();
    for (h, level) in layout.levels.iter().enumerate() {
      for n in level {
        let v = match n.role {
          LayoutRole::Leaf { p, k } => self.leaf_hash(p as u64, k, &task.leaves()[p].x),
          LayoutRole::Dummy => self.dummy_hash(n.lo, n.hi),
          LayoutRole::Merge => {
            let w = (n.hi - n.lo) / self.a as u64;
            let hs: Vec<E1::Scalar> = (0..self.a as u64)
              .map(|c| hashes[&(h - 1, n.lo + c * w)])
              .collect();
            self.node_hash(n.lo, n.hi, &hs)
          }
        };
        hashes.insert((h, n.lo), v);
      }
    }
    RootStatement {
      task_id: task.task_id(),
      num_leaves: task.num_leaves() as u64,
      arity: self.a,
      lo: 0,
      hi: layout.capacity,
      result: task.expected_result(eval),
      tree_hash: hashes[&(layout.depth, 0)],
    }
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

  /// Synthesizes a node circuit on `inputs`; returns the node's CCCS, its padded witness and the
  /// result r.
  #[allow(clippy::type_complexity)]
  fn synthesize_node<P: PredicateSet<E1::Scalar>>(
    &self,
    leaf: &P,
    role: NodeRole,
    inputs: &NodeInputs<E1, E2, V>,
  ) -> Result<(IncomingInstance<E1>, Vec<E1::Scalar>, Vec<E1::Scalar>), TreeError> {
    let mut cs = SatisfyingAssignment::<E1>::new();
    let r = NodeCircuit::<E1, E2, P, V> {
      params: &self.node,
      leaf,
      role,
      inputs: Some(inputs),
    }
    .synthesize(&mut cs)?;
    let mut w = cs.aux_assignment().to_vec();
    if w.len() > self.hfs.num_w() {
      return Err(TreeError::Prover(
        "witness longer than the padded shape".into(),
      ));
    }
    w.resize(self.hfs.num_w(), E1::Scalar::ZERO);
    let io = cs.input_assignment()[1..].to_vec();
    let inc = IncomingInstance::new(&self.hfs, self.id_of(role), &w, io)?;
    let r = r
      .iter()
      .map(|v| v.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<_>, _>>()?;
    Ok((inc, w, r))
  }

  fn base_proof(
    &self,
    ctx: TaskCtx<E1::Scalar>,
    stmt: NodeStatement<E1::Scalar>,
    l_u: IncomingInstance<E1>,
    l_w: Vec<E1::Scalar>,
  ) -> NodeProof<E1, E2, V> {
    let (r_u, r_w) = self.default_running();
    NodeProof {
      ctx,
      stmt,
      r_u,
      r_w,
      l_u,
      l_w,
      cf_u: RelaxedR1CSInstance::<E2>::default(&self.ck_cf, &self.cf_shape),
      cf_w: RelaxedR1CSWitness::<E2>::default(&self.cf_shape),
    }
  }
}

/// Synthesizes a node circuit into a `CountingCS`.
fn count_node<E1, E2, P, V>(
  params: &NodeParams<E1, E2>,
  leaf: &P,
  role: NodeRole,
) -> Result<CountingSummary, TreeError>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  P: PredicateSet<E1::Scalar>,
  V: IvcVariant<E1>,
{
  Ok(count_constraints::<E1::Scalar, _>(|cs| {
    NodeCircuit::<E1, E2, P, V> {
      params,
      leaf,
      role,
      inputs: None,
    }
    .synthesize(cs)
  })?)
}

/// Counts the circuit of family member `role` at the parameters' dimensions.
pub fn node_constraint_counts<E1, E2, P, V>(
  pp: &TreeParams<E1, E2, V>,
  leaf: &P,
  role: NodeRole,
) -> Result<CountingSummary, TreeError>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  P: PredicateSet<E1::Scalar>,
  V: IvcVariant<E1>,
{
  count_node::<E1, E2, P, V>(&pp.node, leaf, role)
}

impl<E1, E2, V> NodeProof<E1, E2, V>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  V: IvcVariant<E1>,
{
  /// Proves leaf p of `task` (base case).
  pub fn prove_leaf<P: PredicateSet<E1::Scalar>>(
    pp: &TreeParams<E1, E2, V>,
    leaf: &P,
    task: &TreeTask<E1::Scalar>,
    p: usize,
  ) -> Result<Self, TreeError> {
    let l = task
      .leaves()
      .get(p)
      .ok_or_else(|| TreeError::Input(format!("leaf {p} >= L = {}", task.num_leaves())))?;
    Self::prove_leaf_raw(pp, leaf, TaskCtx::of(task), p as u64, l.k, &l.x)
  }

  /// [`Self::prove_leaf`] for an explicit context and leaf (test hook: no check against a task;
  /// a position ≥ L gives an unsatisfied circuit).
  #[doc(hidden)]
  pub fn prove_leaf_raw<P: PredicateSet<E1::Scalar>>(
    pp: &TreeParams<E1, E2, V>,
    leaf: &P,
    ctx: TaskCtx<E1::Scalar>,
    p: u64,
    k: usize,
    x: &[E1::Scalar],
  ) -> Result<Self, TreeError> {
    if k >= pp.k_leaf || x.len() != pp.arity {
      return Err(TreeError::Input(format!(
        "leaf predicate {k} (K_leaf = {}) or |x| = {} (arity {})",
        pp.k_leaf,
        x.len(),
        pp.arity
      )));
    }
    let inputs = NodeInputs {
      ctx: pp.ctx(&ctx),
      role: RoleIn::Leaf { p, x: x.to_vec() },
    };
    let (l_u, l_w, r) = pp.synthesize_node(leaf, NodeRole::Leaf(k), &inputs)?;
    let stmt = NodeStatement {
      lo: p,
      hi: p + 1,
      result: r,
      tree_hash: pp.leaf_hash(p, k, x),
    };
    Ok(pp.base_proof(ctx, stmt, l_u, l_w))
  }

  /// Proves the padding subtree `[lo, hi)` of `task` (base case; requires `lo ≥ L`).
  pub fn prove_dummy<P: PredicateSet<E1::Scalar>>(
    pp: &TreeParams<E1, E2, V>,
    leaf: &P,
    task: &TreeTask<E1::Scalar>,
    lo: u64,
    hi: u64,
  ) -> Result<Self, TreeError> {
    if lo < task.num_leaves() as u64 || hi <= lo {
      return Err(TreeError::Input(format!(
        "dummy [{lo}, {hi}) overlaps the {} real leaves or is empty",
        task.num_leaves()
      )));
    }
    Self::prove_dummy_raw(pp, leaf, TaskCtx::of(task), lo, hi)
  }

  /// [`Self::prove_dummy`] without the native check (test hook: `lo < L` gives an unsatisfied
  /// circuit).
  #[doc(hidden)]
  pub fn prove_dummy_raw<P: PredicateSet<E1::Scalar>>(
    pp: &TreeParams<E1, E2, V>,
    leaf: &P,
    ctx: TaskCtx<E1::Scalar>,
    lo: u64,
    hi: u64,
  ) -> Result<Self, TreeError> {
    let inputs = NodeInputs {
      ctx: pp.ctx(&ctx),
      role: RoleIn::Dummy { lo, hi },
    };
    let (l_u, l_w, r) = pp.synthesize_node(leaf, NodeRole::Dummy, &inputs)?;
    let stmt = NodeStatement {
      lo,
      hi,
      result: r,
      tree_hash: pp.dummy_hash(lo, hi),
    };
    Ok(pp.base_proof(ctx, stmt, l_u, l_w))
  }

  /// Proves a merge node of `task` from its a children, in order. The honest API checks the
  /// children natively first (layer Input): count, task context, contiguous ordered equal-width
  /// ranges, and that each child's CCCS hashes its statement and accumulators.
  pub fn prove_node<P: PredicateSet<E1::Scalar>>(
    pp: &TreeParams<E1, E2, V>,
    leaf: &P,
    task: &TreeTask<E1::Scalar>,
    children: &[&Self],
  ) -> Result<Self, TreeError> {
    Self::prove_node_tampered(
      pp,
      leaf,
      TaskCtx::of(task),
      children,
      true,
      NodeTamper::None,
    )
  }

  /// [`Self::prove_node`] with test hooks: `check = false` skips the native checks (the circuit
  /// still enforces them), and `tamper` makes the prover deviate.
  #[doc(hidden)]
  pub fn prove_node_tampered<P: PredicateSet<E1::Scalar>>(
    pp: &TreeParams<E1, E2, V>,
    leaf: &P,
    ctx: TaskCtx<E1::Scalar>,
    children: &[&Self],
    check: bool,
    tamper: NodeTamper,
  ) -> Result<Self, TreeError> {
    let a = pp.a;
    if children.len() != a {
      return Err(TreeError::Input(format!(
        "{} children, arity {a}",
        children.len()
      )));
    }
    if check {
      Self::check_children(pp, &ctx, children)?;
    }
    let mut stmts: Vec<NodeStatement<E1::Scalar>> =
      children.iter().map(|c| c.stmt.clone()).collect();
    let mut run: Vec<RunningInstance<E1, V>> = children.iter().map(|c| c.r_u.clone()).collect();
    let mut run_w: Vec<RunningWitness<E1>> = children.iter().map(|c| c.r_w.clone()).collect();
    let mut inc: Vec<IncomingInstance<E1>> = children.iter().map(|c| c.l_u.clone()).collect();
    let mut inc_w: Vec<Vec<E1::Scalar>> = children.iter().map(|c| c.l_w.clone()).collect();
    match tamper {
      NodeTamper::None => {}
      NodeTamper::ChildResult(c) => stmts[c].result[0] += E1::Scalar::ONE,
      NodeTamper::ChildIncoming(c) => {
        let garbage: Vec<E1::Scalar> = inc_w[c]
          .iter()
          .enumerate()
          .map(|(i, x)| *x + E1::Scalar::from(i as u64 + 1))
          .collect();
        inc[c].comm_w = pp.hfs.commit_w(&garbage)?;
        inc_w[c] = garbage;
      }
      NodeTamper::SwapRunning => {
        run.swap(0, 1);
        run_w.swap(0, 1);
      }
    }

    // 1. HFS v2 fold of μ = a running and ν = a incoming instances.
    let out = NIFS::<E1, V>::prove(&pp.hfs, &run, &run_w, &inc, &inc_w)?;
    let new_u = out.instance;

    // 2. One CycleFold instance for all group operations of the fold.
    let idx_run: Vec<Vec<Coords<E1::Base>>> =
      run.iter().map(|u| V::index_coords(&u.index)).collect();
    let idx_out = V::index_coords(&new_u.index);
    let cf_in = CycleFoldInputsN::<E1> {
      rho: out.challenges.rho,
      ks: inc.iter().map(|i| i.k).collect(),
      w: run
        .iter()
        .map(|u| u.comm_w.to_coordinates())
        .chain(inc.iter().map(|i| i.comm_w.to_coordinates()))
        .collect(),
      w_out: new_u.comm_w.to_coordinates(),
      m: (0..idx_out.len())
        .map(|j| (idx_run.iter().map(|v| v[j]).collect(), idx_out[j]))
        .collect(),
    };
    let circuit = CycleFoldCircuitN::<E1> {
      iota: &pp.node.iota,
      mu: a,
      nu: a,
      t_idx: if V::DIRECT { pp.hfs.t() } else { 0 },
      inputs: Some(cf_in),
    };
    let (cf_inst, cf_wit) =
      cyclefold_instance_witness_n::<E1, E2>(&circuit, &pp.cf_shape, &pp.ck_cf)?;

    // 3. Fold the a CycleFold accumulators, then the fresh instance.
    let mut acc_u = children[0].cf_u.clone();
    let mut acc_w = children[0].cf_w.clone();
    let mut cf_t_relaxed = Vec::with_capacity(a - 1);
    for c in children.iter().skip(1) {
      let (t, u, w) = cf_fold_relaxed_prove(
        &pp.ck_cf,
        &pp.ro_consts_cf,
        pp.pp_digest,
        &pp.cf_shape,
        &acc_u,
        &acc_w,
        &c.cf_u,
        &c.cf_w,
      )?;
      cf_t_relaxed.push(t);
      acc_u = u;
      acc_w = w;
    }
    let (cf_t, cf_u, cf_w) = cf_fold_fresh_prove(
      &pp.ck_cf,
      &pp.ro_consts_cf,
      pp.pp_digest,
      &pp.cf_shape,
      &acc_u,
      &acc_w,
      &cf_inst,
      &cf_wit,
    )?;

    // 4. The merge circuit.
    let kids: Vec<ChildIn<E1, E2, V>> = (0..a)
      .map(|c| ChildIn {
        lo: stmts[c].lo,
        hi: stmts[c].hi,
        r: stmts[c].result.clone(),
        h: stmts[c].tree_hash,
        run: run[c].clone(),
        inc: inc[c].clone(),
        cf: children[c].cf_u.clone(),
      })
      .collect();
    let inputs = NodeInputs {
      ctx: pp.ctx(&ctx),
      role: RoleIn::Merge {
        children: kids,
        proof: out.proof,
        hint_w: new_u.comm_w,
        hint_m: V::index_commitments(&new_u.index),
        cf_t_relaxed,
        cf_w: cf_inst.comm_W,
        cf_t,
      },
    };
    let (l_u, l_w, r) = pp.synthesize_node(leaf, NodeRole::Merge, &inputs)?;
    let hs: Vec<E1::Scalar> = stmts.iter().map(|s| s.tree_hash).collect();
    let (lo, hi) = (stmts[0].lo, stmts[a - 1].hi);
    Ok(Self {
      ctx,
      stmt: NodeStatement {
        lo,
        hi,
        result: r,
        tree_hash: pp.node_hash(lo, hi, &hs),
      },
      r_u: new_u,
      r_w: out.witness,
      l_u,
      l_w,
      cf_u,
      cf_w,
    })
  }

  /// The native checks of the honest merge prover (layer Input).
  fn check_children(
    pp: &TreeParams<E1, E2, V>,
    ctx: &TaskCtx<E1::Scalar>,
    children: &[&Self],
  ) -> Result<(), TreeError> {
    let w0 = children[0].stmt.hi.checked_sub(children[0].stmt.lo);
    for (c, ch) in children.iter().enumerate() {
      if &ch.ctx != ctx {
        return Err(TreeError::Input(format!(
          "child {c} belongs to another task"
        )));
      }
      if ch.stmt.hi.checked_sub(ch.stmt.lo) != w0 || w0 == Some(0) || w0.is_none() {
        return Err(TreeError::Input(format!("child {c} has another width")));
      }
      if c > 0 && ch.stmt.lo != children[c - 1].stmt.hi {
        return Err(TreeError::Input(format!(
          "child {c} starts at {}, previous ends at {} (gap, overlap or order)",
          ch.stmt.lo,
          children[c - 1].stmt.hi
        )));
      }
      if ch.l_u.k >= pp.hfs.k()
        || ch.l_u.io.len() != 1
        || ch.l_u.io[0] != pp.link_hash(ctx, &ch.stmt, &ch.r_u, &ch.cf_u)
      {
        return Err(TreeError::Input(format!(
          "child {c}'s instance does not hash its statement"
        )));
      }
    }
    Ok(())
  }

  /// The node's statement.
  pub fn statement(&self) -> &NodeStatement<E1::Scalar> {
    &self.stmt
  }

  /// The node's task context.
  pub fn ctx(&self) -> &TaskCtx<E1::Scalar> {
    &self.ctx
  }

  /// The family member that produced this node.
  pub fn member(&self) -> usize {
    self.l_u.k
  }

  /// Checks the node's own CCCS: its commitment opens and the CCS of its member holds (layer
  /// RootIncoming). Tests use it to locate the node whose circuit a tampering breaks.
  pub fn check_incoming(&self, pp: &TreeParams<E1, E2, V>) -> Result<(), TreeError> {
    let k = self.l_u.k;
    if k >= pp.hfs.k() || self.l_u.io.len() != 1 {
      return Err(TreeError::Input(format!(
        "the node instance claims member {k} (K = {})",
        pp.hfs.k()
      )));
    }
    let shape = pp.hfs.shape(k);
    if self.l_w.len() != shape.num_w() || pp.hfs.commit_w(&self.l_w)? != self.l_u.comm_w {
      return Err(TreeError::RootIncoming("comm_W does not open".into()));
    }
    let z = [self.l_w.as_slice(), &[E1::Scalar::ONE], &self.l_u.io].concat();
    if !ccs_is_satisfied(pp.hfs.template(), shape, &z) {
      return Err(TreeError::RootIncoming(format!(
        "not satisfied for member {k} ({:?})",
        pp.role(k)
      )));
    }
    Ok(())
  }

  /// Verifies this proof as the root of a tree and returns the proven statement. Takes no tree
  /// structure: the range `[0, a^d)` follows from L, and everything below the root is
  /// authenticated by the recursion.
  pub fn verify_root(
    &self,
    pp: &TreeParams<E1, E2, V>,
  ) -> Result<RootStatement<E1::Scalar>, TreeError> {
    let l = self.ctx.num_leaves;
    if self.stmt.result.len() != pp.arity || self.l_u.k >= pp.hfs.k() || self.l_u.io.len() != 1 {
      return Err(TreeError::Input("malformed root proof".into()));
    }
    // 1. Statement: the root of a tree over L leaves covers [0, a^d).
    if l == 0 || l >= 1u64 << RANGE_BITS {
      return Err(TreeError::Statement(format!("L = {l} out of range")));
    }
    let cap = (pp.a as u64).pow(depth_for(l, pp.a) as u32);
    if self.stmt.lo != 0 || self.stmt.hi != cap {
      return Err(TreeError::Statement(format!(
        "root range [{}, {}) is not [0, {cap}) for L = {l}",
        self.stmt.lo, self.stmt.hi
      )));
    }
    // 2. Link hash.
    if self.l_u.io[0] != pp.link_hash(&self.ctx, &self.stmt, &self.r_u, &self.cf_u) {
      return Err(TreeError::LinkHash);
    }
    // 3. Running ACCS.
    decide(&pp.hfs, &self.r_u, &self.r_w).map_err(TreeError::Decider)?;
    // 4. CycleFold accumulator.
    if self.cf_w.W.len() != pp.cf_shape.num_vars
      || self.cf_w.E.len() != pp.cf_shape.num_cons
      || self.cf_u.X.len() != pp.cf_shape.num_io
    {
      return Err(TreeError::CycleFold("lengths".into()));
    }
    pp.cf_shape
      .is_sat_relaxed(&pp.ck_cf, &self.cf_u, &self.cf_w)
      .map_err(|e| TreeError::CycleFold(format!("{e}")))?;
    // 5. The root's own CCCS.
    self.check_incoming(pp)?;
    Ok(RootStatement {
      task_id: self.ctx.task_id,
      num_leaves: l,
      arity: pp.a,
      lo: self.stmt.lo,
      hi: self.stmt.hi,
      result: self.stmt.result.clone(),
      tree_hash: self.stmt.tree_hash,
    })
  }

  /// [`Self::verify_root`], then compares with an expected statement (layer Statement).
  pub fn verify_statement(
    &self,
    pp: &TreeParams<E1, E2, V>,
    expected: &RootStatement<E1::Scalar>,
  ) -> Result<RootStatement<E1::Scalar>, TreeError> {
    let got = self.verify_root(pp)?;
    if &got != expected {
      return Err(TreeError::Statement(
        "the proven root statement is not the expected one".into(),
      ));
    }
    Ok(got)
  }

  /// Test access to the accumulators (tamper tests).
  #[doc(hidden)]
  #[allow(clippy::type_complexity)]
  pub fn parts_mut(
    &mut self,
  ) -> (
    &mut NodeStatement<E1::Scalar>,
    &mut RunningInstance<E1, V>,
    &mut RunningWitness<E1>,
    &mut RelaxedR1CSInstance<E2>,
    &mut RelaxedR1CSWitness<E2>,
  ) {
    (
      &mut self.stmt,
      &mut self.r_u,
      &mut self.r_w,
      &mut self.cf_u,
      &mut self.cf_w,
    )
  }

  /// Test access to the running ACCS and its witness (oracle checks).
  #[doc(hidden)]
  pub fn running(&self) -> (&RunningInstance<E1, V>, &RunningWitness<E1>) {
    (&self.r_u, &self.r_w)
  }
}

/// Timing of one node proof.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct NodeTiming {
  /// The layout node.
  pub node: LayoutNode,
  /// Wall time of this node's own proof (synthesis, HFS, CycleFold, commitments), ms.
  pub prove_ms: f64,
}

/// What a tree run measured.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TreeRun {
  /// Per-node timings (sequential driver: in proving order).
  pub nodes: Vec<NodeTiming>,
  /// Wall time per level (level-parallel driver only), ms.
  pub level_wall_ms: Vec<f64>,
  /// Total wall time of the driver, ms.
  pub wall_ms: f64,
}

/// Proves the whole tree of `task` for the parameters' arity, **sequentially** and depth-first
/// (at most d·a proofs alive). Returns the root proof and per-node timings.
pub fn prove_tree<E1, E2, V, P>(
  pp: &TreeParams<E1, E2, V>,
  leaf: &P,
  task: &TreeTask<E1::Scalar>,
) -> Result<(NodeProof<E1, E2, V>, TreeRun), TreeError>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  V: IvcVariant<E1>,
  P: PredicateSet<E1::Scalar>,
{
  let layout = task.layout(pp.a);
  let index: HashMap<(usize, u64), LayoutNode> = layout
    .levels
    .iter()
    .flatten()
    .map(|n| ((n.level, n.lo), *n))
    .collect();
  let mut nodes = Vec::new();
  #[allow(clippy::type_complexity)]
  fn build<E1, E2, V, P>(
    pp: &TreeParams<E1, E2, V>,
    leaf: &P,
    task: &TreeTask<E1::Scalar>,
    index: &HashMap<(usize, u64), LayoutNode>,
    level: usize,
    lo: u64,
    out: &mut Vec<NodeTiming>,
  ) -> Result<NodeProof<E1, E2, V>, TreeError>
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
    V: IvcVariant<E1>,
    P: PredicateSet<E1::Scalar>,
  {
    let n = index[&(level, lo)];
    let (proof, ms) = match n.role {
      LayoutRole::Leaf { p, .. } => {
        let t = Instant::now();
        let pr = NodeProof::prove_leaf(pp, leaf, task, p)?;
        (pr, t.elapsed().as_secs_f64() * 1e3)
      }
      LayoutRole::Dummy => {
        let t = Instant::now();
        let pr = NodeProof::prove_dummy(pp, leaf, task, n.lo, n.hi)?;
        (pr, t.elapsed().as_secs_f64() * 1e3)
      }
      LayoutRole::Merge => {
        let w = (n.hi - n.lo) / pp.a as u64;
        let kids = (0..pp.a as u64)
          .map(|c| build(pp, leaf, task, index, level - 1, lo + c * w, out))
          .collect::<Result<Vec<_>, _>>()?;
        let refs: Vec<&NodeProof<E1, E2, V>> = kids.iter().collect();
        let t = Instant::now();
        let pr = NodeProof::prove_node(pp, leaf, task, &refs)?;
        (pr, t.elapsed().as_secs_f64() * 1e3)
      }
    };
    out.push(NodeTiming {
      node: n,
      prove_ms: ms,
    });
    Ok(proof)
  }
  let t = Instant::now();
  let root = build(pp, leaf, task, &index, layout.depth, 0, &mut nodes)?;
  Ok((
    root,
    TreeRun {
      nodes,
      level_wall_ms: Vec::new(),
      wall_ms: t.elapsed().as_secs_f64() * 1e3,
    },
  ))
}

/// Proves the tree level by level; with `parallel`, the nodes of one level are proven
/// concurrently on the current rayon pool (the measured wall time per level is then the
/// parallel latency). Keeps a whole level of proofs in memory.
pub fn prove_tree_levels<E1, E2, V, P>(
  pp: &TreeParams<E1, E2, V>,
  leaf: &P,
  task: &TreeTask<E1::Scalar>,
  parallel: bool,
) -> Result<(NodeProof<E1, E2, V>, TreeRun), TreeError>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  V: IvcVariant<E1>,
  P: PredicateSet<E1::Scalar>,
{
  let layout = task.layout(pp.a);
  let t_all = Instant::now();
  let mut prev: HashMap<u64, NodeProof<E1, E2, V>> = HashMap::new();
  let mut nodes = Vec::new();
  let mut level_wall_ms = Vec::new();
  for level in &layout.levels {
    let t = Instant::now();
    let one = |n: &LayoutNode| -> Result<(u64, NodeProof<E1, E2, V>, NodeTiming), TreeError> {
      let t = Instant::now();
      let pr = match n.role {
        LayoutRole::Leaf { p, .. } => NodeProof::prove_leaf(pp, leaf, task, p)?,
        LayoutRole::Dummy => NodeProof::prove_dummy(pp, leaf, task, n.lo, n.hi)?,
        LayoutRole::Merge => {
          let w = (n.hi - n.lo) / pp.a as u64;
          let refs: Vec<&NodeProof<E1, E2, V>> =
            (0..pp.a as u64).map(|c| &prev[&(n.lo + c * w)]).collect();
          NodeProof::prove_node(pp, leaf, task, &refs)?
        }
      };
      Ok((
        n.lo,
        pr,
        NodeTiming {
          node: *n,
          prove_ms: t.elapsed().as_secs_f64() * 1e3,
        },
      ))
    };
    let done: Vec<(u64, NodeProof<E1, E2, V>, NodeTiming)> = if parallel {
      level.par_iter().map(one).collect::<Result<_, _>>()?
    } else {
      level.iter().map(one).collect::<Result<_, _>>()?
    };
    level_wall_ms.push(t.elapsed().as_secs_f64() * 1e3);
    let mut next = HashMap::new();
    for (lo, pr, tm) in done {
      nodes.push(tm);
      next.insert(lo, pr);
    }
    prev = next;
  }
  let root = prev
    .remove(&0)
    .ok_or_else(|| TreeError::Prover("no root".into()))?;
  Ok((
    root,
    TreeRun {
      nodes,
      level_wall_ms,
      wall_ms: t_all.elapsed().as_secs_f64() * 1e3,
    },
  ))
}

/// Commitment-key size check used by tests: both keys cover the padded shapes.
#[doc(hidden)]
pub fn ck_covers_padded<E1, E2, V>(pp: &TreeParams<E1, E2, V>) -> bool
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
