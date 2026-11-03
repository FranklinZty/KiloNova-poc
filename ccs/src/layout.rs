//! Adapter between the `folding/` layout `(u ‖ io ‖ w)` and the frozen layout `(w ‖ u ‖ io)`
//! (spec N2), so vectors and matrices taken from `folding/` can be checked here.
use crate::{dim, CcsError, SparseMatrix};
use ff::PrimeField;

/// Column of the frozen layout for column `c` of the `folding/` layout.
pub fn col_from_folding(c: usize, num_w: usize, num_io: usize) -> usize {
  match c {
    0 => num_w,
    c if c <= num_io => num_w + c,
    c => c - 1 - num_io,
  }
}

/// `(u ‖ io ‖ w)` → `(w ‖ u ‖ io)`.
pub fn z_from_folding<F: PrimeField>(
  z: &[F],
  num_w: usize,
  num_io: usize,
) -> Result<Vec<F>, CcsError> {
  dim("z", num_w + 1 + num_io, z.len())?;
  Ok([&z[1 + num_io..], &z[..1 + num_io]].concat())
}

/// `(w ‖ u ‖ io)` → `(u ‖ io ‖ w)`.
pub fn z_to_folding<F: PrimeField>(
  z: &[F],
  num_w: usize,
  num_io: usize,
) -> Result<Vec<F>, CcsError> {
  dim("z", num_w + 1 + num_io, z.len())?;
  Ok([&z[num_w..], &z[..num_w]].concat())
}

/// Renumbers the columns of a matrix written for the `folding/` layout.
pub fn matrix_from_folding<F: PrimeField>(
  m: &SparseMatrix<F>,
  num_w: usize,
  num_io: usize,
) -> Result<SparseMatrix<F>, CcsError> {
  dim("matrix columns", num_w + 1 + num_io, m.cols())?;
  m.remap(m.rows(), m.cols(), |c| col_from_folding(c, num_w, num_io))
}
