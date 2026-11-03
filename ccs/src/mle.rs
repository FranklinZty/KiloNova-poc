//! Multilinear extensions with the kilonova conventions (spec N9): index bit `i`
//! (little-endian) pairs with `point[i]`, and indices beyond a vector's length are zero.
use crate::{dim, CcsError, SparseMatrix};
use ff::PrimeField;

/// `max(1, ⌈log₂ len⌉)`: the number of variables of an MLE over `len` entries. Matches
/// kilonova's `s = log₂(num_cons).max(1)` and `s' = log₂(next_pow2(z_len)).max(1)`.
pub fn num_vars(len: usize) -> usize {
  (len.max(1).next_power_of_two().trailing_zeros() as usize).max(1)
}

pub fn bits_le(mut idx: usize, len: usize) -> Vec<bool> {
  (0..len)
    .map(|_| {
      let b = idx & 1 == 1;
      idx >>= 1;
      b
    })
    .collect()
}

/// `eq(bits, point) = Π_i (bit_i ? point_i : 1 − point_i)`.
pub fn eq_eval<F: PrimeField>(bits: &[bool], point: &[F]) -> F {
  bits
    .iter()
    .zip(point)
    .fold(F::ONE, |acc, (b, r)| acc * if *b { *r } else { F::ONE - r })
}

fn check_point<F>(what: &str, len: usize, point: &[F]) -> Result<(), CcsError> {
  if point.len() < usize::BITS as usize && len <= 1usize << point.len() {
    Ok(())
  } else {
    Err(CcsError::Dimension {
      what: format!("{what}: point too short for {len} entries"),
      expected: num_vars(len),
      got: point.len(),
    })
  }
}

/// Sparse evaluation `M̃(r_x, r_y) = Σ_{(i,j,v)} v · eq(i, r_x) · eq(j, r_y)`.
pub fn eval_matrix_mle<F: PrimeField>(
  m: &SparseMatrix<F>,
  r_x: &[F],
  r_y: &[F],
) -> Result<F, CcsError> {
  check_point("r_x", m.rows(), r_x)?;
  check_point("r_y", m.cols(), r_y)?;
  Ok(m.entries().iter().fold(F::ZERO, |acc, &(i, j, v)| {
    acc + v * eq_eval(&bits_le(i, r_x.len()), r_x) * eq_eval(&bits_le(j, r_y.len()), r_y)
  }))
}

/// Sparse evaluation `z̃(r) = Σ_i z_i · eq(i, r)`.
pub fn eval_vec_mle<F: PrimeField>(z: &[F], r: &[F]) -> Result<F, CcsError> {
  check_point("r", z.len(), r)?;
  Ok(z.iter().enumerate().fold(F::ZERO, |acc, (i, v)| {
    acc + *v * eq_eval(&bits_le(i, r.len()), r)
  }))
}

/// Independent dense evaluator: zero-pads `table` to `2^point.len()` and folds it variable by
/// variable (`T'[j] = (1 − r_k)·T[2j] + r_k·T[2j+1]`). It shares no code with the sparse path.
pub fn dense_mle_eval<F: PrimeField>(table: &[F], point: &[F]) -> Result<F, CcsError> {
  check_point("point", table.len(), point)?;
  let mut t = table.to_vec();
  t.resize(1usize << point.len(), F::ZERO);
  for r in point {
    t = t.chunks(2).map(|p| p[0] + (p[1] - p[0]) * r).collect();
  }
  Ok(t[0])
}

/// Dense matrix MLE: the full table indexed by `row + (col << r_x.len())`, evaluated at
/// `r_x ‖ r_y` with [`dense_mle_eval`].
pub fn dense_matrix_mle_eval<F: PrimeField>(
  m: &SparseMatrix<F>,
  r_x: &[F],
  r_y: &[F],
) -> Result<F, CcsError> {
  check_point("r_x", m.rows(), r_x)?;
  check_point("r_y", m.cols(), r_y)?;
  let sx = r_x.len();
  let mut table = vec![F::ZERO; 1usize << (sx + r_y.len())];
  for (i, row) in m.to_dense().iter().enumerate() {
    for (j, v) in row.iter().enumerate() {
      table[i + (j << sx)] = *v;
    }
  }
  dense_mle_eval(&table, &[r_x, r_y].concat())
}

/// Checks that a point has exactly the expected number of variables.
pub fn check_exact(what: &str, expected: usize, point: &[impl Sized]) -> Result<(), CcsError> {
  dim(what, expected, point.len())
}
