//! Padding and template embedding, with the exact semantics kept and the overhead reported.
use crate::{dim, Ccs, CcsError, SparseMatrix, Template};
use ff::PrimeField;

/// Size counters used to report the cost of a transformation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Overhead {
  pub m: (usize, usize),
  pub n: (usize, usize),
  pub nnz: (usize, usize),
  pub t: (usize, usize),
  pub q: (usize, usize),
  pub d: (usize, usize),
}

pub fn overhead<F: PrimeField>(before: &Ccs<F>, after: &Ccs<F>) -> Overhead {
  Overhead {
    m: (before.m, after.m),
    n: (before.n(), after.n()),
    nnz: (before.nnz(), after.nnz()),
    t: (before.t(), after.t()),
    q: (before.q(), after.q()),
    d: (before.degree(), after.degree()),
  }
}

/// True iff the shape already satisfies `R1CSShape::is_regular_shape`.
pub fn is_regular<F: PrimeField>(ccs: &Ccs<F>) -> bool {
  ccs.m.is_power_of_two() && ccs.num_w.is_power_of_two() && ccs.num_io < ccs.num_w
}

/// Pads exactly like `R1CSShape::pad`: a regular shape is unchanged; otherwise
/// `p = next_pow2(max(num_w, m, num_io))`, `m := p`, and if `num_w ≠ p` then `num_w := p` with
/// the u/io columns shifted right by `p − num_w`. New rows are empty, new witness entries 0.
pub fn pad<F: PrimeField>(ccs: &Ccs<F>) -> Result<Ccs<F>, CcsError> {
  ccs.validate()?;
  if is_regular(ccs) {
    return Ok(ccs.clone());
  }
  let p = ccs.num_w.max(ccs.m).max(ccs.num_io).next_power_of_two();
  let shift = p - ccs.num_w;
  let n_new = p + 1 + ccs.num_io;
  let num_w = ccs.num_w;
  let matrices = ccs
    .matrices
    .iter()
    .map(|mat| mat.remap(p, n_new, |c| if c >= num_w { c + shift } else { c }))
    .collect::<Result<Vec<_>, _>>()?;
  Ccs::new(p, p, ccs.num_io, ccs.template.clone(), matrices)
}

/// The assignment of `orig` mapped to `padded`: `(w ‖ 0…0 ‖ u ‖ io)`.
pub fn pad_z<F: PrimeField>(orig: &Ccs<F>, padded: &Ccs<F>, z: &[F]) -> Result<Vec<F>, CcsError> {
  dim("z", orig.n(), z.len())?;
  dim("padded io", orig.num_io, padded.num_io)?;
  let mut out = z[..orig.num_w].to_vec();
  out.resize(padded.num_w, F::ZERO);
  out.extend_from_slice(&z[orig.num_w..]);
  Ok(out)
}

/// Extends the template with `extra_matrices` all-zero matrices and `extra_terms`. Each extra
/// term must contain at least one new (zero) matrix, so it contributes 0 on every row and the
/// relation is unchanged for every z. Used to place a CCS in a larger family template.
pub fn embed_zero_terms<F: PrimeField>(
  ccs: &Ccs<F>,
  extra_matrices: usize,
  extra_terms: Vec<(F, Vec<usize>)>,
) -> Result<Ccs<F>, CcsError> {
  ccs.validate()?;
  let t_old = ccs.t();
  let mut template = ccs.template.clone();
  template.t += extra_matrices;
  for (k, (c, s)) in extra_terms.into_iter().enumerate() {
    if !s.iter().any(|&j| j >= t_old) {
      return Err(CcsError::InvalidTemplate(format!(
        "extra term {k} contains no zero matrix, so it would change the relation"
      )));
    }
    template.multisets.push(s);
    template.coeffs.push(c);
  }
  let mut matrices = ccs.matrices.clone();
  matrices.extend((0..extra_matrices).map(|_| SparseMatrix::zero(ccs.m, ccs.n())));
  Ccs::new(ccs.m, ccs.num_w, ccs.num_io, template, matrices)
}

/// Raises every term to degree `d` by multiplying it with a new matrix `U` that selects the u
/// column on every row (`(U z)_i = u`). For `u = 1` (fresh instances) this preserves the
/// relation exactly. For a relaxed `u ≠ 1` it does **not**, because terms get different powers
/// of u. Callers must only use it on fresh instances.
pub fn lift_degree<F: PrimeField>(ccs: &Ccs<F>, d: usize) -> Result<Ccs<F>, CcsError> {
  ccs.validate()?;
  if d < ccs.degree() {
    return Err(CcsError::InvalidTemplate(format!(
      "target degree {d} is below the current degree {}",
      ccs.degree()
    )));
  }
  let u_idx = ccs.t();
  let multisets = ccs
    .template
    .multisets
    .iter()
    .map(|s| {
      let mut s = s.clone();
      s.resize(d, u_idx);
      s
    })
    .collect();
  let template = Template {
    t: ccs.t() + 1,
    multisets,
    coeffs: ccs.template.coeffs.clone(),
  };
  let u_sel =
    SparseMatrix::from_triplets(ccs.m, ccs.n(), (0..ccs.m).map(|i| (i, ccs.u_col(), F::ONE)))?;
  let mut matrices = ccs.matrices.clone();
  matrices.push(u_sel);
  Ccs::new(ccs.m, ccs.num_w, ccs.num_io, template, matrices)
}
