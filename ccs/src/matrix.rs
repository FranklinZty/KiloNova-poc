//! Sparse matrices in canonical form.
use crate::{dim, CcsError};
use ff::PrimeField;

/// A sparse matrix in canonical form: entries sorted by (row, col), no duplicate positions and
/// no explicit zeros. Two equal matrices therefore have identical entry lists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseMatrix<F: PrimeField> {
  rows: usize,
  cols: usize,
  entries: Vec<(usize, usize, F)>,
}

impl<F: PrimeField> SparseMatrix<F> {
  /// The all-zero `rows × cols` matrix.
  pub fn zero(rows: usize, cols: usize) -> Self {
    Self {
      rows,
      cols,
      entries: Vec::new(),
    }
  }

  /// Builds a matrix from arbitrary triplets: out-of-range positions are rejected, duplicates
  /// are summed and zeros dropped.
  pub fn from_triplets(
    rows: usize,
    cols: usize,
    triplets: impl IntoIterator<Item = (usize, usize, F)>,
  ) -> Result<Self, CcsError> {
    let mut all = Vec::new();
    for (row, col, val) in triplets {
      if row >= rows || col >= cols {
        return Err(CcsError::IndexOutOfRange {
          row,
          col,
          rows,
          cols,
        });
      }
      all.push((row, col, val));
    }
    all.sort_by_key(|e| (e.0, e.1));
    let mut entries: Vec<(usize, usize, F)> = Vec::with_capacity(all.len());
    for (row, col, val) in all {
      match entries.last_mut() {
        Some(last) if last.0 == row && last.1 == col => last.2 += val,
        _ => entries.push((row, col, val)),
      }
    }
    entries.retain(|e| !bool::from(e.2.is_zero()));
    Ok(Self {
      rows,
      cols,
      entries,
    })
  }

  /// Accepts only entries that are already canonical (strictly increasing positions, no
  /// zeros, in range). Used by the decoder, which must reject every other encoding.
  pub fn from_canonical(
    rows: usize,
    cols: usize,
    entries: Vec<(usize, usize, F)>,
  ) -> Result<Self, CcsError> {
    for (i, &(row, col, val)) in entries.iter().enumerate() {
      if row >= rows || col >= cols {
        return Err(CcsError::IndexOutOfRange {
          row,
          col,
          rows,
          cols,
        });
      }
      if bool::from(val.is_zero()) {
        return Err(CcsError::NonCanonical(format!(
          "explicit zero at ({row}, {col})"
        )));
      }
      if i > 0 {
        let (prow, pcol, _) = entries[i - 1];
        if (prow, pcol) >= (row, col) {
          return Err(CcsError::NonCanonical(format!(
            "entry ({row}, {col}) is not after ({prow}, {pcol})"
          )));
        }
      }
    }
    Ok(Self {
      rows,
      cols,
      entries,
    })
  }

  pub fn rows(&self) -> usize {
    self.rows
  }

  pub fn cols(&self) -> usize {
    self.cols
  }

  pub fn nnz(&self) -> usize {
    self.entries.len()
  }

  pub fn entries(&self) -> &[(usize, usize, F)] {
    &self.entries
  }

  /// `M · z`.
  pub fn mul_vec(&self, z: &[F]) -> Result<Vec<F>, CcsError> {
    dim("z in M·z", self.cols, z.len())?;
    let mut out = vec![F::ZERO; self.rows];
    for &(row, col, val) in &self.entries {
      out[row] += val * z[col];
    }
    Ok(out)
  }

  /// Dense row-major copy, for naive cross-checks on small matrices.
  pub fn to_dense(&self) -> Vec<Vec<F>> {
    let mut d = vec![vec![F::ZERO; self.cols]; self.rows];
    for &(row, col, val) in &self.entries {
      d[row][col] = val;
    }
    d
  }

  /// Same entries in a matrix of the given (larger or equal) size, with columns renumbered by
  /// `col_map`.
  pub(crate) fn remap(
    &self,
    rows: usize,
    cols: usize,
    col_map: impl Fn(usize) -> usize,
  ) -> Result<Self, CcsError> {
    Self::from_triplets(
      rows,
      cols,
      self.entries.iter().map(|&(r, c, v)| (r, col_map(c), v)),
    )
  }
}
