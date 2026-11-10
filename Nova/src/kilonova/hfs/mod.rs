//! Native-field holographic folding scheme (HFS), transcript **v2** (PLAN.md P3).
//!
//! This is the P3 replacement of the v1 HFS in `kilonova::nifs` / `kilonova::span::nifs`:
//!
//! - it folds over **`E::Scalar`, the native field of the folded relation** (no `field_switch`
//!   projection), which fixes B15 for native folding;
//! - it is generic over the CCS template (t matrices, q product terms given as multisets with
//!   repeats, coefficients, degree d), described by [`CcsTemplate`] (the reference description is
//!   `kn_ccs::Template`);
//! - it folds μ running ACCS instances and ν incoming CCCS instances in one step (μ + ν ≥ 1);
//! - it has both index representations: [`Direct`] (committed λ via `comm_M[t]`) and [`Span`]
//!   (public λ);
//! - its transcript is Poseidon over `E::Scalar` (`E::RO2`), with commitments absorbed as
//!   4 × 64-bit limbs per coordinate (`transcript::v2`, `docs/protocol-spec.md` §8).
//!
//! There is no recursion here. The v1 recursion path (`RecursiveSNARK`, the augmented circuits
//! and their gadget) keeps transcript v1 until P5 moves it onto this module.
//!
//! The verifier ([`NIFS::verify`]) is succinct: it reads only instances, proof messages and
//! public parameters, never a witness or a matrix. The ε/θ claims are deferred by design and
//! checked by the [`decide`] relation check, together with the commitment openings.
use core::fmt;

mod decider;
mod instance;
mod nifs;
mod structure;
mod sumcheck;

#[cfg(test)]
mod tests;

pub use decider::decide;
pub use instance::{Direct, IncomingInstance, RunningInstance, RunningWitness, Span, Variant};
pub use nifs::{Challenges, HfsProof, ProverOutput, NIFS};
pub use structure::{num_vars, CcsShape, CcsTemplate, HfsParams};
pub(crate) use structure::{CK_INDEX_LABEL, CK_LABEL};

/// Sum-check phase of the HFS.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
  /// Row variables (degree d + 1).
  X,
  /// Column variables (degree 2).
  Y,
}

impl fmt::Display for Phase {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Phase::X => write!(f, "X"),
      Phase::Y => write!(f, "Y"),
    }
  }
}

/// Where a rejection happens.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layer {
  /// Parameter, shape or input validation (before any transcript work).
  Input,
  /// The bare (succinct) folding verifier: sum-check rounds and end checks.
  Verifier,
  /// The terminal relation check on the folded instance and its witness.
  Decider,
}

/// Every way the v2 HFS rejects. The variant names the failed condition, and [`HfsError::layer`]
/// names the detection layer.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum HfsError {
  /// The template (t, multisets, coefficients) is malformed.
  #[error("invalid template: {0}")]
  InvalidTemplate(String),
  /// The predicate family is malformed (empty, mixed templates or dimensions, bad entries).
  #[error("invalid family: {0}")]
  InvalidFamily(String),
  /// A count or length does not match.
  #[error("shape mismatch for {what}: expected {expected}, got {got}")]
  Shape {
    /// The object whose length is wrong.
    what: String,
    /// Expected length.
    expected: usize,
    /// Actual length.
    got: usize,
  },
  /// An incoming predicate id is not in the family.
  #[error("predicate id {id} out of range (K = {k})")]
  PredicateId {
    /// The id.
    id: usize,
    /// Family size.
    k: usize,
  },
  /// A sum-check round message does not match the running claim.
  #[error("{phase} sum-check round {round}: p(0) + p(1) != claim")]
  SumcheckRound {
    /// Phase.
    phase: Phase,
    /// Round index (round i binds variable i).
    round: usize,
  },
  /// The final sum-check claim does not equal the value recomputed from the helper claims.
  #[error("{phase} end check failed")]
  EndCheck {
    /// Phase.
    phase: Phase,
  },
  /// Decider: `comm_W` does not open to `W`.
  #[error("decider: comm_W does not open to W")]
  Commitment,
  /// Decider (Direct): `comm_M[j]` does not open to λ.
  #[error("decider: comm_M[{j}] does not open to lambda")]
  IndexCommitment {
    /// Matrix index.
    j: usize,
  },
  /// Decider (Span): the public λ of the instance differs from the witness λ.
  #[error("decider: public lambda differs from the witness lambda")]
  SpanIndex,
  /// Decider: evaluation claim `v[index]` is wrong (index t is the z-claim).
  #[error("decider: claim v[{index}] is wrong")]
  Claim {
    /// Claim index.
    index: usize,
  },
}

impl HfsError {
  /// The layer that detected the error.
  pub fn layer(&self) -> Layer {
    match self {
      HfsError::InvalidTemplate(_)
      | HfsError::InvalidFamily(_)
      | HfsError::Shape { .. }
      | HfsError::PredicateId { .. } => Layer::Input,
      HfsError::SumcheckRound { .. } | HfsError::EndCheck { .. } => Layer::Verifier,
      HfsError::Commitment
      | HfsError::IndexCommitment { .. }
      | HfsError::SpanIndex
      | HfsError::Claim { .. } => Layer::Decider,
    }
  }
}

pub(crate) fn check_len(
  what: impl Into<String>,
  expected: usize,
  got: usize,
) -> Result<(), HfsError> {
  if expected == got {
    Ok(())
  } else {
    Err(HfsError::Shape {
      what: what.into(),
      expected,
      got,
    })
  }
}
