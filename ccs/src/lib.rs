//! KiloNova P2: native CCS construction and an independent ACCS/CCCS reference checker.
//!
//! This crate is a slow correctness oracle. It is generic over `ff::PrimeField` and has no
//! dependency on the protocol code it checks (`Nova/src/kilonova/`). Conventions are the
//! frozen ones of `docs/protocol-spec.md`:
//!
//! - assignment layout `z = (w ‖ u ‖ io)` (N2); column `num_w` holds `u`;
//! - multilinear extensions pair index bit `i` (little-endian) with `point[i]` (N9);
//! - row / column variable counts are `max(1, ⌈log₂ m⌉)` and `max(1, ⌈log₂ n⌉)`;
//! - padding mirrors `R1CSShape::pad` (see [`pad`]).
#![forbid(unsafe_code)]
#![allow(non_snake_case)]

pub mod accs;
pub mod builder;
pub mod ccs;
pub mod encode;
pub mod r#gen;
pub mod layout;
pub mod matrix;
pub mod mle;
pub mod pad;

pub use accs::{AccsInstance, CccsInstance, Family};
pub use builder::{Assignment, NativeCcsBuilder, Var};
pub use ccs::{Ccs, Template};
pub use matrix::SparseMatrix;

/// Every way the builder or the checker can reject an input. The variant names the failed
/// condition, so negative tests can assert the detection layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CcsError {
  /// The template (t, multisets, coefficients) is malformed.
  InvalidTemplate(String),
  /// A length or dimension does not match.
  Dimension {
    what: String,
    expected: usize,
    got: usize,
  },
  /// A matrix entry lies outside the matrix.
  IndexOutOfRange {
    row: usize,
    col: usize,
    rows: usize,
    cols: usize,
  },
  /// An encoding is not the unique canonical one.
  NonCanonical(String),
  /// The CCS relation fails at this row.
  Unsatisfied { row: usize },
  /// The witness does not open the commitment.
  Commitment,
  /// ACCS evaluation claim `v[index]` is wrong (index `t` is the z-claim).
  Claim { index: usize },
  /// The family members do not share a template and dimensions.
  Family(String),
}

impl core::fmt::Display for CcsError {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      CcsError::InvalidTemplate(s) => write!(f, "invalid template: {s}"),
      CcsError::Dimension {
        what,
        expected,
        got,
      } => write!(
        f,
        "dimension mismatch for {what}: expected {expected}, got {got}"
      ),
      CcsError::IndexOutOfRange {
        row,
        col,
        rows,
        cols,
      } => write!(f, "entry ({row}, {col}) outside a {rows}x{cols} matrix"),
      CcsError::NonCanonical(s) => write!(f, "non-canonical encoding: {s}"),
      CcsError::Unsatisfied { row } => write!(f, "CCS relation fails at row {row}"),
      CcsError::Commitment => write!(f, "witness does not open the commitment"),
      CcsError::Claim { index } => write!(f, "ACCS claim v[{index}] is wrong"),
      CcsError::Family(s) => write!(f, "invalid family: {s}"),
    }
  }
}

impl std::error::Error for CcsError {}

pub(crate) fn dim(what: &str, expected: usize, got: usize) -> Result<(), CcsError> {
  if expected == got {
    Ok(())
  } else {
    Err(CcsError::Dimension {
      what: what.to_string(),
      expected,
      got,
    })
  }
}
