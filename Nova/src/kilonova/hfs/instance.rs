//! Running (ACCS) and incoming (CCCS) instances, and the two index representations.
use super::{check_len, HfsError, HfsParams};
use crate::{
  kilonova::transcript::v2::{absorb_commitment, TAG_INPUT_DIRECT, TAG_INPUT_SPAN},
  traits::{Engine, ROTrait},
  Commitment,
};
use core::fmt::Debug;
use serde::{de::DeserializeOwned, Deserialize, Serialize};

/// How the running instance carries the predicate index λ ∈ F^K.
pub trait Variant<E: Engine>:
  Clone + Copy + Debug + Default + PartialEq + Eq + Send + Sync + 'static
{
  /// The index part of a running instance.
  type Index: Clone + Debug + PartialEq + Eq + Send + Sync + Serialize + DeserializeOwned;
  /// Name used in reports.
  const NAME: &'static str;
  /// First transcript tag.
  const TAG_INPUT: u64;

  /// The index of a fresh instance of predicate `k`.
  fn incoming_index(pp: &HfsParams<E>, k: usize) -> Self::Index;
  /// Length checks.
  fn check_index(pp: &HfsParams<E>, idx: &Self::Index, what: &str) -> Result<(), HfsError>;
  /// Transcript absorption of a running index.
  fn absorb_running_index(ro: &mut E::RO2, idx: &Self::Index);
  /// Transcript absorption of the index of an incoming instance of predicate `k` (after `k`).
  fn absorb_incoming_index(ro: &mut E::RO2, pp: &HfsParams<E>, k: usize);
  /// `acc ← acc + w · idx`.
  fn scale_add(acc: &mut Self::Index, idx: &Self::Index, w: E::Scalar);
  /// Decider: the index of the folded instance opens to the witness λ.
  fn check_opening(
    pp: &HfsParams<E>,
    idx: &Self::Index,
    lambda: &[E::Scalar],
  ) -> Result<(), HfsError>;
}

/// Committed index: the running instance carries `comm_M[j] = Com(ck_index_j, λ)` for j < t,
/// and an incoming instance of predicate k contributes ι_k. λ stays in the witness.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Direct;

/// Public index (index-span ablation): the running instance carries λ ∈ F^K in the clear, and
/// an incoming instance of predicate k contributes e_k. O(K) public state, no group operations.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Span;

impl<E: Engine> Variant<E> for Direct {
  type Index = Vec<Commitment<E>>;
  const NAME: &'static str = "direct";
  const TAG_INPUT: u64 = TAG_INPUT_DIRECT;

  fn incoming_index(pp: &HfsParams<E>, k: usize) -> Self::Index {
    pp.iota(k).to_vec()
  }

  fn check_index(pp: &HfsParams<E>, idx: &Self::Index, what: &str) -> Result<(), HfsError> {
    check_len(format!("{what}.comm_M"), pp.t(), idx.len())
  }

  fn absorb_running_index(ro: &mut E::RO2, idx: &Self::Index) {
    idx.iter().for_each(|c| absorb_commitment::<E>(ro, c));
  }

  fn absorb_incoming_index(ro: &mut E::RO2, pp: &HfsParams<E>, k: usize) {
    pp.iota(k)
      .iter()
      .for_each(|c| absorb_commitment::<E>(ro, c));
  }

  fn scale_add(acc: &mut Self::Index, idx: &Self::Index, w: E::Scalar) {
    for (a, b) in acc.iter_mut().zip(idx) {
      *a = *a + *b * w;
    }
  }

  fn check_opening(
    pp: &HfsParams<E>,
    idx: &Self::Index,
    lambda: &[E::Scalar],
  ) -> Result<(), HfsError> {
    for (j, c) in idx.iter().enumerate() {
      if *c != pp.commit_index(j, lambda)? {
        return Err(HfsError::IndexCommitment { j });
      }
    }
    Ok(())
  }
}

impl<E: Engine> Variant<E> for Span {
  type Index = Vec<E::Scalar>;
  const NAME: &'static str = "span";
  const TAG_INPUT: u64 = TAG_INPUT_SPAN;

  fn incoming_index(pp: &HfsParams<E>, k: usize) -> Self::Index {
    pp.e_k(k)
  }

  fn check_index(pp: &HfsParams<E>, idx: &Self::Index, what: &str) -> Result<(), HfsError> {
    check_len(format!("{what}.lambda"), pp.k(), idx.len())
  }

  fn absorb_running_index(ro: &mut E::RO2, idx: &Self::Index) {
    idx.iter().for_each(|l| ro.absorb(*l));
  }

  /// e_k is fixed by the absorbed predicate id, so nothing more is absorbed (as in v1).
  fn absorb_incoming_index(_ro: &mut E::RO2, _pp: &HfsParams<E>, _k: usize) {}

  fn scale_add(acc: &mut Self::Index, idx: &Self::Index, w: E::Scalar) {
    for (a, b) in acc.iter_mut().zip(idx) {
      *a += *b * w;
    }
  }

  fn check_opening(
    _pp: &HfsParams<E>,
    idx: &Self::Index,
    lambda: &[E::Scalar],
  ) -> Result<(), HfsError> {
    if idx.as_slice() == lambda {
      Ok(())
    } else {
      Err(HfsError::SpanIndex)
    }
  }
}

/// Running ACCS instance: `comm_W`, the index (`comm_M` or λ), `u`, `io`, the points
/// `(r_x, r_y)` and the claims `v = (v_0..v_{t−1}, v_t)` with `v_j = Σ_i λ_i M̃_{i,j}(r_x, r_y)`
/// and `v_t = z̃(r_y)`, `z = (W ‖ u ‖ io)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RunningInstance<E: Engine, V: Variant<E>> {
  /// Witness commitment.
  pub comm_w: Commitment<E>,
  /// Index: `comm_M[0..t]` (Direct) or λ (Span).
  pub index: V::Index,
  /// Relaxation scalar.
  pub u: E::Scalar,
  /// Public io.
  pub io: Vec<E::Scalar>,
  /// Row point (s entries; entry i pairs with index bit i).
  pub r_x: Vec<E::Scalar>,
  /// Column point (s' entries).
  pub r_y: Vec<E::Scalar>,
  /// Claims (t + 1 entries).
  pub v: Vec<E::Scalar>,
}

/// Witness of a running instance.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RunningWitness<E: Engine> {
  /// Folded witness.
  pub w: Vec<E::Scalar>,
  /// Folded index λ (also public in the Span variant).
  pub lambda: Vec<E::Scalar>,
}

/// Incoming CCCS instance of predicate `k` (u = 1, λ = e_k).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct IncomingInstance<E: Engine> {
  /// Predicate id.
  pub k: usize,
  /// Witness commitment.
  pub comm_w: Commitment<E>,
  /// Public io.
  pub io: Vec<E::Scalar>,
}

impl<E: Engine> IncomingInstance<E> {
  /// Commits to `w` and builds the instance (no satisfiability check).
  pub fn new(
    pp: &HfsParams<E>,
    k: usize,
    w: &[E::Scalar],
    io: Vec<E::Scalar>,
  ) -> Result<Self, HfsError> {
    Ok(Self {
      k,
      comm_w: pp.commit_w(w)?,
      io,
    })
  }
}
