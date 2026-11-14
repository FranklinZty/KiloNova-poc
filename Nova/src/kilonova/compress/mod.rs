//! P7a: independent final verification and compression, **`reference-basis-decider`**
//! (PLAN.md P7, `docs/P7-plan.md`, spec `docs/protocol-spec.md` §12).
//!
//! [`compress_chain`] / [`compress_tree`] turn a [`RecursiveSNARK`] or a root [`NodeProof`] into a
//! [`CompressedProof`] that [`verify_final_chain`] / [`verify_final_tree`] check from the
//! **declared public material** ([`FinalVerifierKey`], built from a material file by
//! [`FinalVerifierKey::read_material`]) and the proof bytes alone. No witness is read:
//!
//! 1. the last incoming CCCS (chain: last step; tree: the root's own CCCS) is folded into the
//!    running ACCS by one more HFS v2 fold (μ = ν = 1), verified natively with `NIFS::verify`
//!    (the verifier does that fold's group operations itself, so no CycleFold instance is
//!    needed), giving `U*`;
//! 2. index: Direct reveals λ* and the verifier checks `comm_M*[j] = Com(ck_index_j, λ*)`;
//!    Span carries λ* in `U*`;
//! 3. matrix evaluation, **reference basis**: the verifier evaluates `M̃_{k,j}(r_x*, r_y*)` for
//!    every base matrix of the family (O(Σ_k nnz), i.e. O(K·N) in the index) and checks
//!    `Σ_k λ*_k M̃_{k,j} = v*_j`;
//! 4. witness opening: an inner-product argument (`provider::ipa_pc`) shows that `comm_W*`
//!    opens to a vector a with `⟨a, b⟩ = v*_t − (public part of z̃*(r_y*))`, where b is the
//!    eq vector of `r_y*` **masked to the first num_w entries** (entries beyond num_w never enter
//!    an evaluation, so a commitment with a tail cannot shift u or io);
//! 5. the CycleFold accumulator (relaxed R1CS over E2) is proven by the inherited Spartan
//!    `RelaxedR1CSSNARK` with the IPA evaluation engine.
//!
//! Instantiated for Pallas (E1) / Vesta (E2), Pedersen + IPA. The compression transcript is new
//! (`kn-compress-v1`, [`TAG_COMPRESS`], [`COMPRESS_VERSION`]); the HFS transcript v2 is unchanged.
//! P7b (sparse holographic evaluation) is **not** implemented.
use crate::{
  errors::NovaError,
  kilonova::{
    family::{FamilyMeta, PredicateFamily},
    hfs::{num_vars, HfsError, HfsParams, HfsProof, IncomingInstance, Layer, RunningInstance, NIFS},
    ivc::{
      chain_link_hash, chain_pp_digest, ChainOutput, IvcVariant, PrimaryTemplate, PublicParams,
      RecursiveSNARK, CF_CK_LABEL,
    },
    pcd::{
      depth_for, tree_link_hash, tree_pp_digest, NodeProof, NodeStatement, RootStatement, TaskCtx,
      TreeParams, RANGE_BITS, TREE_CF_CK_LABEL,
    },
  },
  provider::{
    ipa_pc::{EvaluationEngine, InnerProductArgument, InnerProductInstance, InnerProductWitness},
    PallasEngine, VestaEngine,
  },
  r1cs::{R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness},
  spartan::snark::{ProverKey as SpartanPk, RelaxedR1CSSNARK, VerifierKey as SpartanVk},
  traits::{
    commitment::CommitmentEngineTrait, snark::RelaxedR1CSSNARKTrait, Engine,
    TranscriptEngineTrait,
  },
  CommitmentKey,
};
use core::marker::PhantomData;
use ff::{Field, PrimeField};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

pub mod format;
#[cfg(test)]
mod tests;

pub use format::{AccountItem, ProofAccount};

/// The first curve (running ACCS, HFS).
pub type E1 = PallasEngine;
/// The second curve (CycleFold accumulator).
pub type E2 = VestaEngine;
/// Scalar field of E1.
pub type F1 = <E1 as Engine>::Scalar;
/// Spartan SNARK for the CycleFold relaxed R1CS (IPA evaluation engine on E2).
pub type CfSnark = RelaxedR1CSSNARK<E2, EvaluationEngine<E2>>;

/// Version of the compressed proof format and of the compression transcript.
pub const COMPRESS_VERSION: u16 = 1;
/// Domain tag of the compression transcript: "KNCP" ‖ v1 ‖ 1.
pub const TAG_COMPRESS: u64 = 0x4b4e_4350_0001_0001;
/// Label of the compression transcript (Keccak, `E1::TE`).
pub const COMPRESS_TRANSCRIPT_LABEL: &[u8] = b"kn-compress-v1";
/// Label of the IPA's inner-product generator (as `ipa_pc::EvaluationEngine::setup`).
pub const IPA_CK_LABEL: &[u8] = b"ipa";
/// The name of this decider in every report and record.
pub const DECIDER: &str = "reference-basis-decider";

/// Chain or tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofKind {
  /// `kilonova::ivc` chain (IVC version 2).
  Chain,
  /// `kilonova::pcd` tree root (PCD version 1).
  Tree,
}

impl ProofKind {
  pub(crate) fn code(self) -> u8 {
    match self {
      ProofKind::Chain => 1,
      ProofKind::Tree => 2,
    }
  }
}

/// Where `verify-final` (or loading the material) rejects. The order is the order of the checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompressLayer {
  /// The public material file is malformed, or does not hash to the pinned pp digest.
  Material,
  /// The proof file: magic, version, kind, variant, sections, lengths, canonical encodings.
  Format,
  /// The proof was made for other public parameters (pp digest or family digest).
  Binding,
  /// The public statement: step count / z_0 against the expected ones (chain), range `[0, a^d)`,
  /// L, a, or an expected root statement (tree).
  Statement,
  /// The last incoming instance does not hash the statement and the accumulators.
  LinkHash,
  /// The final HFS fold of the last incoming instance into the running ACCS.
  FinalFold,
  /// Direct: the folded index commitments do not open to the revealed λ*.
  IndexOpening,
  /// `Σ_k λ*_k M̃_{k,j}(r_x*, r_y*) ≠ v*_j` (reference-basis matrix evaluation).
  MatrixEval,
  /// The inner-product argument for the z claim against `comm_W*`.
  WitnessOpening,
  /// The Spartan proof of the CycleFold accumulator.
  CycleFold,
  /// Prover-side failure (compress).
  Prover,
}

/// Every way compression and final verification fail. [`CompressError::layer`] names the layer.
#[derive(Debug, thiserror::Error)]
pub enum CompressError {
  /// See [`CompressLayer::Material`].
  #[error("material: {0}")]
  Material(String),
  /// See [`CompressLayer::Format`].
  #[error("format: {0}")]
  Format(String),
  /// See [`CompressLayer::Binding`].
  #[error("binding: {0}")]
  Binding(String),
  /// See [`CompressLayer::Statement`].
  #[error("statement: {0}")]
  Statement(String),
  /// See [`CompressLayer::LinkHash`].
  #[error("link hash: the last incoming instance does not hash the statement")]
  LinkHash,
  /// See [`CompressLayer::FinalFold`].
  #[error("final fold: {0}")]
  FinalFold(HfsError),
  /// See [`CompressLayer::IndexOpening`].
  #[error("index opening: comm_M*[{j}] does not open to the revealed lambda*")]
  IndexOpening {
    /// Matrix slot.
    j: usize,
  },
  /// See [`CompressLayer::MatrixEval`].
  #[error("matrix evaluation: v*[{j}] != sum_k lambda*_k M~_(k,{j})(r_x*, r_y*)")]
  MatrixEval {
    /// Matrix slot.
    j: usize,
  },
  /// See [`CompressLayer::WitnessOpening`].
  #[error("witness opening: {0}")]
  WitnessOpening(String),
  /// See [`CompressLayer::CycleFold`].
  #[error("cyclefold snark: {0}")]
  CycleFold(String),
  /// See [`CompressLayer::Prover`].
  #[error("prover: {0}")]
  Prover(String),
}

impl CompressError {
  /// The detection layer.
  pub fn layer(&self) -> CompressLayer {
    match self {
      CompressError::Material(_) => CompressLayer::Material,
      CompressError::Format(_) => CompressLayer::Format,
      CompressError::Binding(_) => CompressLayer::Binding,
      CompressError::Statement(_) => CompressLayer::Statement,
      CompressError::LinkHash => CompressLayer::LinkHash,
      CompressError::FinalFold(_) => CompressLayer::FinalFold,
      CompressError::IndexOpening { .. } => CompressLayer::IndexOpening,
      CompressError::MatrixEval { .. } => CompressLayer::MatrixEval,
      CompressError::WitnessOpening(_) => CompressLayer::WitnessOpening,
      CompressError::CycleFold(_) => CompressLayer::CycleFold,
      CompressError::Prover(_) => CompressLayer::Prover,
    }
  }
}

impl From<NovaError> for CompressError {
  fn from(e: NovaError) -> Self {
    CompressError::Prover(format!("{e}"))
  }
}

/// How the running index is transmitted and opened (on top of [`IvcVariant`]).
pub trait FinalVariant: IvcVariant<E1> {
  /// Variant byte of the proof header (Direct 0, Span 1).
  const CODE: u8;
  /// Elements of the revealed λ* (Direct K, Span 0).
  fn revealed_len(k: usize) -> usize;
  /// What the proof reveals of the folded λ (Direct: λ*; Span: nothing, λ* is in U*).
  fn reveal(lambda: &[F1]) -> Vec<F1>;
  /// λ* after the index check (layer IndexOpening for Direct).
  fn lambda_star(
    hfs: &HfsParams<E1>,
    index: &Self::Index,
    revealed: &[F1],
  ) -> Result<Vec<F1>, CompressError>;
  /// Writes a running index.
  fn write_index(w: &mut format::Writer, idx: &Self::Index);
  /// Reads a running index of `t` commitments (Direct) or `k` scalars (Span).
  fn read_index(
    r: &mut format::Reader<'_>,
    t: usize,
    k: usize,
  ) -> Result<Self::Index, CompressError>;
  /// Bytes of a running index.
  fn index_bytes(t: usize, k: usize) -> usize;
}

impl FinalVariant for crate::kilonova::hfs::Direct {
  const CODE: u8 = 0;
  fn revealed_len(k: usize) -> usize {
    k
  }
  fn reveal(lambda: &[F1]) -> Vec<F1> {
    lambda.to_vec()
  }
  fn lambda_star(
    hfs: &HfsParams<E1>,
    index: &Self::Index,
    revealed: &[F1],
  ) -> Result<Vec<F1>, CompressError> {
    for (j, c) in index.iter().enumerate() {
      let again = hfs
        .commit_index(j, revealed)
        .map_err(|e| CompressError::Format(format!("{e}")))?;
      if again != *c {
        return Err(CompressError::IndexOpening { j });
      }
    }
    Ok(revealed.to_vec())
  }
  fn write_index(w: &mut format::Writer, idx: &Self::Index) {
    idx.iter().for_each(|c| w.point::<E1>(c));
  }
  fn read_index(
    r: &mut format::Reader<'_>,
    t: usize,
    _k: usize,
  ) -> Result<Self::Index, CompressError> {
    (0..t).map(|_| r.point::<E1>()).collect()
  }
  fn index_bytes(t: usize, _k: usize) -> usize {
    32 * t
  }
}

impl FinalVariant for crate::kilonova::hfs::Span {
  const CODE: u8 = 1;
  fn revealed_len(_k: usize) -> usize {
    0
  }
  fn reveal(_lambda: &[F1]) -> Vec<F1> {
    Vec::new()
  }
  fn lambda_star(
    _hfs: &HfsParams<E1>,
    index: &Self::Index,
    _revealed: &[F1],
  ) -> Result<Vec<F1>, CompressError> {
    Ok(index.clone())
  }
  fn write_index(w: &mut format::Writer, idx: &Self::Index) {
    idx.iter().for_each(|x| w.scalar(x));
  }
  fn read_index(
    r: &mut format::Reader<'_>,
    _t: usize,
    k: usize,
  ) -> Result<Self::Index, CompressError> {
    (0..k).map(|_| r.scalar::<F1>()).collect()
  }
  fn index_bytes(_t: usize, k: usize) -> usize {
    32 * k
  }
}

/// The public statement carried by a compressed proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FinalStatement {
  /// Chain: n steps from `z_0` to `z_n` with trace hash `trace`.
  Chain {
    /// Step count n.
    n: u64,
    /// Initial state.
    z0: Vec<F1>,
    /// Final state.
    zn: Vec<F1>,
    /// `H_trace*(k_0, …, k_{n−1})`.
    trace: F1,
  },
  /// Tree root: task context, arity and the root's statement.
  Tree {
    /// Task id and L.
    ctx: TaskCtx<F1>,
    /// PCD arity a.
    a: u64,
    /// `(lo, hi, R, h)`.
    stmt: NodeStatement<F1>,
  },
}

/// Everything in a compressed proof before the two opening arguments (sections 1–7).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofHead<V: FinalVariant> {
  /// Chain or tree.
  pub kind: ProofKind,
  /// pp digest of the parameters the proof was made for.
  pub pp_digest: F1,
  /// Family digest (also the HFS transcript digest).
  pub family_digest: F1,
  /// The public statement.
  pub statement: FinalStatement,
  /// The final running ACCS `U_n` (instance only).
  pub running: RunningInstance<E1, V>,
  /// The last incoming CCCS `u_n` (instance only).
  pub incoming: IncomingInstance<E1>,
  /// The CycleFold accumulator `cfU_n` (instance only).
  pub cf: RelaxedR1CSInstance<E2>,
  /// The final HFS fold of `u_n` into `U_n` (μ = ν = 1).
  pub fold: HfsProof<E1>,
  /// Direct: λ* (K elements); Span: empty.
  pub lambda: Vec<F1>,
}

/// A compressed proof: the head, the IPA for the z claim and the Spartan proof of the CycleFold
/// accumulator. Every field is public; there is no witness field.
#[derive(Debug)]
pub struct CompressedProof<V: FinalVariant> {
  /// Sections 1–7.
  pub head: ProofHead<V>,
  /// Section 8: inner-product argument for `⟨W*, b_mask⟩ = y` against `comm_W*`.
  pub w_open: InnerProductArgument<E1>,
  /// Section 9: Spartan proof of `cfU_n`.
  pub cf_snark: CfSnark,
}

/// `eq(p, ·)` over `{0,1}^{|p|}`, index bit i ↔ `p[i]` (the decider's convention), O(2^{|p|}).
pub(crate) fn eq_table<F: PrimeField>(p: &[F]) -> Vec<F> {
  let mut t = Vec::with_capacity(1 << p.len());
  t.push(F::ONE);
  for r in p {
    let n = t.len();
    t.resize(2 * n, F::ZERO);
    for b in 0..n {
      let v = t[b];
      t[b + n] = v * r;
      t[b] = v - t[b + n];
    }
  }
  t
}

/// Reference-basis evaluation: `M̃_{k,j}(r_x, r_y)` for **every** member k and matrix j
/// (`[k][j]`). O(2^s + 2^{s'} + Σ_k nnz(M_k)).
pub fn reference_basis_eval(hfs: &HfsParams<E1>, r_x: &[F1], r_y: &[F1]) -> Vec<Vec<F1>> {
  let (ex, ey) = rayon::join(|| eq_table(r_x), || eq_table(r_y));
  hfs
    .shapes()
    .par_iter()
    .map(|sh| {
      sh.matrices()
        .iter()
        .map(|mat| {
          mat
            .iter()
            .fold(F1::ZERO, |acc, &(r, c, v)| acc + v * ex[r] * ey[c])
        })
        .collect()
    })
    .collect()
}

/// The masked vector b (`b_i = eq(i, r_y)` for i < num_w, 0 otherwise, length 2^{s'}) and the
/// target `y = v_t − u·eq(num_w, r_y) − Σ_j io_j·eq(num_w + 1 + j, r_y)`.
fn z_claim_target<V: FinalVariant>(
  num_w: usize,
  u: &RunningInstance<E1, V>,
  t: usize,
) -> (Vec<F1>, F1) {
  let mut b = eq_table(&u.r_y);
  let mut y = u.v[t] - u.u * b[num_w];
  for (j, x) in u.io.iter().enumerate() {
    y -= *x * b[num_w + 1 + j];
  }
  b[num_w..].iter_mut().for_each(|x| *x = F1::ZERO);
  (b, y)
}

/// SHA3-256 of the canonical head bytes, as a 250-bit scalar.
fn head_digest(head_bytes: &[u8]) -> F1 {
  use sha3::{Digest, Sha3_256};
  let mut d: [u8; 32] = Sha3_256::digest(head_bytes).into();
  d[31] &= 0x03;
  let mut repr = <F1 as PrimeField>::Repr::default();
  repr.as_mut().copy_from_slice(&d);
  Option::from(F1::from_repr(repr)).expect("250-bit value is canonical")
}

fn compress_transcript(pp_digest: F1, head: F1) -> <E1 as Engine>::TE {
  let mut tr = <E1 as Engine>::TE::new(COMPRESS_TRANSCRIPT_LABEL);
  tr.absorb(b"tag", &F1::from(TAG_COMPRESS));
  tr.absorb(b"pp", &pp_digest);
  tr.absorb(b"head", &head);
  tr
}

// ---------------------------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------------------------

/// The compressor's keys: the witness key extended to 2^{s'} generators, the IPA generator and
/// the Spartan prover key of the CycleFold shape.
pub struct CompressorKey {
  ck_w: CommitmentKey<E1>,
  ck_c: CommitmentKey<E1>,
  cf_pk: SpartanPk<E2, EvaluationEngine<E2>>,
}

impl CompressorKey {
  fn build(hfs: &HfsParams<E1>, cf_shape: &R1CSShape<E2>, ck_cf: &CommitmentKey<E2>) -> Result<Self, CompressError> {
    let n = 1usize << hfs.s_prime();
    let (cf_pk, _) = CfSnark::setup(ck_cf, cf_shape)?;
    Ok(Self {
      ck_w: <E1 as Engine>::CE::setup(crate::kilonova::hfs::CK_LABEL, n),
      ck_c: <E1 as Engine>::CE::setup(IPA_CK_LABEL, 1),
      cf_pk,
    })
  }

  /// Keys for a chain's parameters.
  pub fn chain<V: FinalVariant>(pp: &PublicParams<E1, E2, V>) -> Result<Self, CompressError> {
    Self::build(pp.hfs(), pp.cyclefold_shape(), pp.cyclefold_key())
  }

  /// Keys for a tree's parameters.
  pub fn tree<V: FinalVariant>(pp: &TreeParams<E1, E2, V>) -> Result<Self, CompressError> {
    Self::build(pp.hfs(), pp.cyclefold_shape(), pp.cyclefold_key())
  }
}

#[allow(clippy::too_many_arguments)]
fn compress_common<V: FinalVariant>(
  hfs: &HfsParams<E1>,
  cf_shape: &R1CSShape<E2>,
  ck_cf: &CommitmentKey<E2>,
  key: &CompressorKey,
  kind: ProofKind,
  pp_digest: F1,
  statement: FinalStatement,
  (r_u, r_w): (&RunningInstance<E1, V>, &crate::kilonova::hfs::RunningWitness<E1>),
  (l_u, l_w): (&IncomingInstance<E1>, &[F1]),
  (cf_u, cf_w): (&RelaxedR1CSInstance<E2>, &RelaxedR1CSWitness<E2>),
) -> Result<CompressedProof<V>, CompressError> {
  // 1. final HFS fold of the last incoming instance (μ = ν = 1)
  let out = NIFS::<E1, V>::prove(
    hfs,
    std::slice::from_ref(r_u),
    std::slice::from_ref(r_w),
    std::slice::from_ref(l_u),
    std::slice::from_ref(&l_w.to_vec()),
  )
  .map_err(|e| CompressError::Prover(format!("final fold: {e}")))?;
  let head = ProofHead {
    kind,
    pp_digest,
    family_digest: hfs.digest(),
    statement,
    running: r_u.clone(),
    incoming: l_u.clone(),
    cf: cf_u.clone(),
    fold: out.proof,
    lambda: V::reveal(&out.witness.lambda),
  };
  // 2. z claim: IPA on the masked eq vector
  let u_star = &out.instance;
  let n = 1usize << hfs.s_prime();
  let (b, y) = z_claim_target(hfs.num_w(), u_star, hfs.t());
  let mut a = out.witness.w.clone();
  a.resize(n, F1::ZERO);
  let c = a.iter().zip(&b).fold(F1::ZERO, |acc, (x, y)| acc + *x * y);
  if c != y {
    return Err(CompressError::Prover(
      "the folded witness does not satisfy the z claim (the recursive proof is invalid)".into(),
    ));
  }
  let head_bytes = format::encode_head(&head);
  let mut tr = compress_transcript(pp_digest, head_digest(&head_bytes));
  let w_open = InnerProductArgument::prove(
    &key.ck_w,
    &key.ck_c,
    &InnerProductInstance::new(&u_star.comm_w, &b, &y),
    &InnerProductWitness::new(&a),
    &mut tr,
  )?;
  // 3. CycleFold accumulator: Spartan
  let cf_snark = CfSnark::prove(ck_cf, &key.cf_pk, cf_shape, cf_u, cf_w)?;
  Ok(CompressedProof {
    head,
    w_open,
    cf_snark,
  })
}

/// Compresses a chain after its last step.
pub fn compress_chain<V: FinalVariant>(
  pp: &PublicParams<E1, E2, V>,
  key: &CompressorKey,
  snark: &RecursiveSNARK<E1, E2, V>,
) -> Result<CompressedProof<V>, CompressError> {
  let statement = FinalStatement::Chain {
    n: snark.num_steps() as u64,
    z0: snark.z0().to_vec(),
    zn: snark.outputs().to_vec(),
    trace: snark.trace(),
  };
  compress_common(
    pp.hfs(),
    pp.cyclefold_shape(),
    pp.cyclefold_key(),
    key,
    ProofKind::Chain,
    pp.digest(),
    statement,
    snark.running(),
    snark.last_incoming(),
    snark.cyclefold(),
  )
}

/// Compresses a tree root.
pub fn compress_tree<V: FinalVariant>(
  pp: &TreeParams<E1, E2, V>,
  key: &CompressorKey,
  root: &NodeProof<E1, E2, V>,
) -> Result<CompressedProof<V>, CompressError> {
  let statement = FinalStatement::Tree {
    ctx: *root.ctx(),
    a: pp.pcd_arity() as u64,
    stmt: root.statement().clone(),
  };
  compress_common(
    pp.hfs(),
    pp.cyclefold_shape(),
    pp.cyclefold_key(),
    key,
    ProofKind::Tree,
    pp.digest(),
    statement,
    root.running(),
    root.own_incoming(),
    root.cyclefold(),
  )
}

// ---------------------------------------------------------------------------------------------
// Verifier key (from the public material only)
// ---------------------------------------------------------------------------------------------

/// The verifier's declared public material, decoded and authenticated: the family (matrices,
/// ids, digest), the HFS parameters with the witness key extended to the IPA size, the index key
/// and ι, the IPA generator, the CycleFold shape and its Spartan verifier key, and the pp digest.
/// Nothing in it comes from a prover's run.
pub struct FinalVerifierKey<V: FinalVariant> {
  kind: ProofKind,
  arity: usize,
  a: usize,
  hfs: HfsParams<E1>,
  family: FamilyMeta<F1>,
  ck_c: CommitmentKey<E1>,
  cf_shape: R1CSShape<E2>,
  cf_vk: SpartanVk<E2, EvaluationEngine<E2>>,
  pp_digest: F1,
  _p: PhantomData<V>,
}

/// What the material says, before keys are derived (see [`format::write_material_chain`]).
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct MaterialHeader {
  /// Material layout version (= [`COMPRESS_VERSION`]).
  pub version: u64,
  /// 1 chain, 2 tree.
  pub kind: u8,
  /// "direct" or "span".
  pub variant: String,
  /// The primary template.
  pub template: PrimaryTemplate,
  /// State arity (chain) or leaf arity (tree).
  pub arity: u64,
  /// Tree arity a (0 for chains).
  pub a: u64,
  /// Leaf predicates (0 for chains).
  pub k_leaf: u64,
  /// Family label.
  pub label: String,
  /// Stable member ids (K).
  pub ids: Vec<String>,
  /// Selector descriptor.
  pub selector: Vec<u8>,
  /// Padded CycleFold R1CS shape.
  pub cf_shape: R1CSShape<E2>,
}

impl<V: FinalVariant> FinalVerifierKey<V> {
  /// Builds the key from a decoded material header and the members' canonical encodings,
  /// recomputes every digest and compares the pp digest with `expected` (the one recorded at
  /// setup) when given. Layer Material on any failure.
  pub fn from_parts(
    header: MaterialHeader,
    members: Vec<(crate::kilonova::hfs::CcsTemplate<F1>, crate::kilonova::hfs::CcsShape<F1>)>,
    expected: Option<F1>,
  ) -> Result<Self, CompressError> {
    let bad = |m: String| CompressError::Material(m);
    let kind = match header.kind {
      1 => ProofKind::Chain,
      2 => ProofKind::Tree,
      k => return Err(bad(format!("kind {k}"))),
    };
    if header.version != COMPRESS_VERSION as u64 || header.variant != V::NAME {
      return Err(bad(format!(
        "material v{} {} for a {} verifier",
        header.version,
        header.variant,
        V::NAME
      )));
    }
    let tpl = header.template.template::<F1>();
    let mut shapes = Vec::with_capacity(members.len());
    for (k, (t, sh)) in members.into_iter().enumerate() {
      if t != tpl {
        return Err(bad(format!("member {k} has another template")));
      }
      shapes.push(sh);
    }
    let k = shapes.len();
    let arity = header.arity as usize;
    let family = PredicateFamily::new(
      header.label,
      header.ids,
      arity,
      header.selector,
      tpl,
      shapes,
    )
    .map_err(|e| bad(format!("family: {e}")))?;
    let n_ipa = 1usize << num_vars(family.shapes()[0].n());
    let cf_shape = header.cf_shape;
    if !cf_shape.is_regular_shape() {
      return Err(bad("CycleFold shape is not padded".into()));
    }
    let fam_digest = family.digest();
    let pp_digest = match kind {
      ProofKind::Chain => {
        chain_pp_digest::<E1, E2>(V::NAME, header.template, arity, k, fam_digest, &cf_shape)
      }
      ProofKind::Tree => {
        if header.a < 2 || header.k_leaf as usize + 2 != k {
          return Err(bad(format!("tree a = {}, K_leaf = {}, K = {k}", header.a, header.k_leaf)));
        }
        tree_pp_digest::<E1, E2>(
          V::NAME,
          header.template,
          header.a as usize,
          header.k_leaf as usize,
          arity,
          fam_digest,
          &cf_shape,
        )
      }
    }
    .map_err(|e| bad(format!("pp digest: {e}")))?;
    if let Some(d) = expected {
      if d != pp_digest {
        return Err(bad(
          "the material does not hash to the pinned pp digest".into(),
        ));
      }
    }
    let (hfs, family) = family
      .into_hfs_params_with_ck_len::<E1>(n_ipa)
      .map_err(|e| bad(format!("hfs: {e}")))?;
    let label = match kind {
      ProofKind::Chain => CF_CK_LABEL,
      ProofKind::Tree => TREE_CF_CK_LABEL,
    };
    let ck_cf = <E2 as Engine>::CE::setup(label, cf_shape.num_cons.max(cf_shape.num_vars));
    let (_, cf_vk) = CfSnark::setup(&ck_cf, &cf_shape).map_err(|e| bad(format!("spartan: {e}")))?;
    Ok(Self {
      kind,
      arity,
      a: header.a as usize,
      hfs,
      family,
      ck_c: <E1 as Engine>::CE::setup(IPA_CK_LABEL, 1),
      cf_shape,
      cf_vk,
      pp_digest,
      _p: PhantomData,
    })
  }

  /// Reads a material file (see [`format::write_material_chain`]) and builds the key.
  pub fn read_material(r: &mut impl std::io::Read, expected: Option<F1>) -> Result<Self, CompressError> {
    let (header, members) = format::read_material(r)?;
    Self::from_parts(header, members, expected)
  }

  /// The recomputed pp digest.
  pub fn pp_digest(&self) -> F1 {
    self.pp_digest
  }

  /// The authenticated family.
  pub fn family(&self) -> &FamilyMeta<F1> {
    &self.family
  }

  /// The HFS parameters (matrices, index key, ι).
  pub fn hfs(&self) -> &HfsParams<E1> {
    &self.hfs
  }

  /// Chain or tree.
  pub fn kind(&self) -> ProofKind {
    self.kind
  }

  /// State arity.
  pub fn arity(&self) -> usize {
    self.arity
  }

  /// Tree arity (0 for chains).
  pub fn tree_arity(&self) -> usize {
    self.a
  }

  /// The CycleFold shape.
  pub fn cyclefold_shape(&self) -> &R1CSShape<E2> {
    &self.cf_shape
  }

  /// Key record of this transparent setup ("SRS"): (key, generators, SHA3-256 of the
  /// bincode-serialized generators or, for Spartan, the vk digest).
  pub fn key_record(&self) -> Vec<(String, usize, String)> {
    use crate::traits::{commitment::Len, snark::DigestHelperTrait};
    use sha3::{Digest, Sha3_256};
    fn hex(b: &[u8]) -> String {
      b.iter().map(|x| format!("{x:02x}")).collect()
    }
    fn sha<T: Serialize>(v: &T) -> String {
      hex(&Sha3_256::digest(
        bincode::serde::encode_to_vec(v, bincode::config::legacy()).unwrap_or_default(),
      ))
    }
    vec![
      (
        "kn-hfs-v2-ck (extended to 2^s')".into(),
        self.hfs.ck().length(),
        sha(self.hfs.ck()),
      ),
      ("ipa".into(), self.ck_c.length(), sha(&self.ck_c)),
      (
        "spartan vk (CycleFold key and shape), digest".into(),
        self.cf_shape.num_cons.max(self.cf_shape.num_vars),
        hex(self.cf_vk.digest().to_repr().as_ref()),
      ),
    ]
  }
}

// ---------------------------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------------------------

/// Index check, matrix evaluation, witness opening and CycleFold on a folded `U*` (the terminal
/// checks 5–8 of spec §12.3). Split out so tests can show each layer catches its own tampering.
pub(crate) fn check_index<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  u_star: &RunningInstance<E1, V>,
  revealed: &[F1],
) -> Result<Vec<F1>, CompressError> {
  V::lambda_star(&vk.hfs, &u_star.index, revealed)
}

pub(crate) fn check_matrix_eval<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  u_star: &RunningInstance<E1, V>,
  lambda: &[F1],
) -> Result<(), CompressError> {
  let evals = reference_basis_eval(&vk.hfs, &u_star.r_x, &u_star.r_y);
  for j in 0..vk.hfs.t() {
    let v = evals
      .iter()
      .zip(lambda)
      .fold(F1::ZERO, |acc, (e, l)| acc + *l * e[j]);
    if v != u_star.v[j] {
      return Err(CompressError::MatrixEval { j });
    }
  }
  Ok(())
}

pub(crate) fn check_witness_opening<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  head_bytes: &[u8],
  u_star: &RunningInstance<E1, V>,
  arg: &InnerProductArgument<E1>,
) -> Result<(), CompressError> {
  let n = 1usize << vk.hfs.s_prime();
  let (b, y) = z_claim_target(vk.hfs.num_w(), u_star, vk.hfs.t());
  let mut tr = compress_transcript(vk.pp_digest, head_digest(head_bytes));
  arg
    .verify(
      vk.hfs.ck(),
      &vk.ck_c,
      n,
      &InnerProductInstance::new(&u_star.comm_w, &b, &y),
      &mut tr,
    )
    .map_err(|e| CompressError::WitnessOpening(format!("{e}")))
}

pub(crate) fn check_cyclefold<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  cf: &RelaxedR1CSInstance<E2>,
  snark: &CfSnark,
) -> Result<(), CompressError> {
  // the inherited Spartan verifier asserts on some malformed inputs; a panic is a rejection
  let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| snark.verify(&vk.cf_vk, cf)));
  match res {
    Ok(Ok(())) => Ok(()),
    Ok(Err(e)) => Err(CompressError::CycleFold(format!("{e}"))),
    Err(_) => Err(CompressError::CycleFold("malformed proof (verifier panicked)".into())),
  }
}

/// Checks 4–8 (final fold, index, matrices, witness opening, CycleFold) on a decoded proof.
fn verify_terminal<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  p: &CompressedProof<V>,
) -> Result<(), CompressError> {
  let h = &p.head;
  let (u_star, _) = NIFS::<E1, V>::verify(
    &vk.hfs,
    std::slice::from_ref(&h.running),
    std::slice::from_ref(&h.incoming),
    &h.fold,
  )
  .map_err(|e| match e.layer() {
    Layer::Input => CompressError::Format(format!("final fold input: {e}")),
    _ => CompressError::FinalFold(e),
  })?;
  let lambda = check_index(vk, &u_star, &h.lambda)?;
  check_matrix_eval(vk, &u_star, &lambda)?;
  check_witness_opening(vk, &format::encode_head(h), &u_star, &p.w_open)?;
  check_cyclefold(vk, &h.cf, &p.cf_snark)
}

fn check_binding<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  h: &ProofHead<V>,
  kind: ProofKind,
) -> Result<(), CompressError> {
  if vk.kind != kind || h.kind != kind {
    return Err(CompressError::Binding(format!(
      "a {:?} proof for a {:?} verifier",
      h.kind, vk.kind
    )));
  }
  if h.pp_digest != vk.pp_digest {
    return Err(CompressError::Binding(
      "the proof was made for other public parameters (pp digest)".into(),
    ));
  }
  if h.family_digest != vk.hfs.digest() {
    return Err(CompressError::Binding(
      "the proof was made for another family (family digest)".into(),
    ));
  }
  Ok(())
}

/// Verifies a decoded chain proof against the public input `(num_steps, z0)`.
pub fn verify_final_chain_proof<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  p: &CompressedProof<V>,
  num_steps: usize,
  z0: &[F1],
) -> Result<ChainOutput<F1>, CompressError> {
  check_binding(vk, &p.head, ProofKind::Chain)?;
  let h = &p.head;
  let FinalStatement::Chain { n, z0: pz0, zn, trace } = &h.statement else {
    return Err(CompressError::Format("not a chain statement".into()));
  };
  if num_steps == 0 || *n != num_steps as u64 || pz0.as_slice() != z0 {
    return Err(CompressError::Statement(format!(
      "the proof is for {n} steps from its own z_0; expected {num_steps} steps from the given z_0"
    )));
  }
  if zn.len() != vk.arity || z0.len() != vk.arity {
    return Err(CompressError::Format("state length".into()));
  }
  if h.incoming.k >= vk.hfs.k() || h.incoming.io.len() != 1 {
    return Err(CompressError::Format("last incoming instance".into()));
  }
  let link = chain_link_hash::<E1, E2, V>(
    vk.pp_digest,
    vk.hfs.digest(),
    num_steps,
    z0,
    zn,
    *trace,
    &h.running,
    &h.cf,
  );
  if h.incoming.io[0] != link {
    return Err(CompressError::LinkHash);
  }
  verify_terminal(vk, p)?;
  Ok(ChainOutput {
    zn: zn.clone(),
    trace: *trace,
    last_id: h.incoming.k,
  })
}

/// `verify-final` for a chain: decodes the proof file against the material, then
/// [`verify_final_chain_proof`].
pub fn verify_final_chain<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  proof: &[u8],
  num_steps: usize,
  z0: &[F1],
) -> Result<ChainOutput<F1>, CompressError> {
  let p = format::decode(vk, proof)?;
  verify_final_chain_proof(vk, &p, num_steps, z0)
}

/// Verifies a decoded tree root proof; returns the proven root statement.
pub fn verify_final_tree_proof<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  p: &CompressedProof<V>,
) -> Result<RootStatement<F1>, CompressError> {
  check_binding(vk, &p.head, ProofKind::Tree)?;
  let h = &p.head;
  let FinalStatement::Tree { ctx, a, stmt } = &h.statement else {
    return Err(CompressError::Format("not a tree statement".into()));
  };
  let l = ctx.num_leaves;
  if *a != vk.a as u64 {
    return Err(CompressError::Statement(format!("a = {a}, parameters for a = {}", vk.a)));
  }
  if l == 0 || l >= 1u64 << RANGE_BITS {
    return Err(CompressError::Statement(format!("L = {l} out of range")));
  }
  let cap = (vk.a as u64).pow(depth_for(l, vk.a) as u32);
  if stmt.lo != 0 || stmt.hi != cap {
    return Err(CompressError::Statement(format!(
      "root range [{}, {}) is not [0, {cap}) for L = {l}",
      stmt.lo, stmt.hi
    )));
  }
  if stmt.result.len() != vk.arity || h.incoming.k >= vk.hfs.k() || h.incoming.io.len() != 1 {
    return Err(CompressError::Format("root statement or instance".into()));
  }
  let link = tree_link_hash::<E1, E2, V>(vk.pp_digest, vk.hfs.digest(), ctx, stmt, &h.running, &h.cf);
  if h.incoming.io[0] != link {
    return Err(CompressError::LinkHash);
  }
  verify_terminal(vk, p)?;
  Ok(RootStatement {
    task_id: ctx.task_id,
    num_leaves: l,
    arity: vk.a,
    lo: stmt.lo,
    hi: stmt.hi,
    result: stmt.result.clone(),
    tree_hash: stmt.tree_hash,
  })
}

/// `verify-final` for a tree root: decodes the proof file, then [`verify_final_tree_proof`].
pub fn verify_final_tree<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  proof: &[u8],
) -> Result<RootStatement<F1>, CompressError> {
  let p = format::decode(vk, proof)?;
  verify_final_tree_proof(vk, &p)
}

/// [`verify_final_tree`], then compares with the statement expected from the task (layer
/// Statement).
pub fn verify_final_tree_statement<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  proof: &[u8],
  expected: &RootStatement<F1>,
) -> Result<RootStatement<F1>, CompressError> {
  let got = verify_final_tree(vk, proof)?;
  if &got != expected {
    return Err(CompressError::Statement(
      "the proven root statement is not the expected one".into(),
    ));
  }
  Ok(got)
}
