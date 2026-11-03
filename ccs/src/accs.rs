//! Reference relations for the HFS inputs and output (`docs/protocol-spec.md` §1).
//!
//! - CCCS (incoming): `(comm_w, io)` with witness `w`; `comm_w = Com(w)` and the CCS holds on
//!   `z = (w ‖ 1 ‖ io)`.
//! - ACCS (running), over a family of K CCS sharing one template and one size:
//!   `comm_w = Com(w)`, `v_j = Σ_i λ_i · M̃_{i,j}(r_x, r_y)` for `j < t`, and
//!   `v_t = z̃(r_y)` with `z = (w ‖ u ‖ io)`. λ = e_k is a single predicate.
//!
//! The commitment is supplied by the caller (`commit(w)`), so this crate stays independent of
//! curves. Checks run in a fixed order and the error names the first failed condition.
use crate::{
  dim,
  mle::{check_exact, eval_matrix_mle, eval_vec_mle, num_vars},
  Ccs, CcsError,
};
use ff::PrimeField;

/// K CCS with one template and identical dimensions (PLAN.md P4: shared interface, padded
/// dimensions and template).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Family<F: PrimeField> {
  members: Vec<Ccs<F>>,
}

impl<F: PrimeField> Family<F> {
  pub fn new(members: Vec<Ccs<F>>) -> Result<Self, CcsError> {
    let first = members
      .first()
      .ok_or_else(|| CcsError::Family("empty family".into()))?;
    for (i, c) in members.iter().enumerate() {
      c.validate()?;
      if c.template != first.template {
        return Err(CcsError::Family(format!(
          "member {i} has a different template"
        )));
      }
      if (c.m, c.num_w, c.num_io) != (first.m, first.num_w, first.num_io) {
        return Err(CcsError::Family(format!(
          "member {i} is {}x({}+1+{}), member 0 is {}x({}+1+{})",
          c.m, c.num_w, c.num_io, first.m, first.num_w, first.num_io
        )));
      }
    }
    Ok(Self { members })
  }

  pub fn k(&self) -> usize {
    self.members.len()
  }

  pub fn member(&self, i: usize) -> &Ccs<F> {
    &self.members[i]
  }

  /// Row variables `s` and column variables `s'` of the family.
  pub fn point_dims(&self) -> (usize, usize) {
    let c = &self.members[0];
    (num_vars(c.m), num_vars(c.n()))
  }

  /// Honest claims `v` for (λ, z) at (r_x, r_y).
  pub fn claims(&self, lambda: &[F], z: &[F], r_x: &[F], r_y: &[F]) -> Result<Vec<F>, CcsError> {
    dim("lambda", self.k(), lambda.len())?;
    let t = self.members[0].t();
    let mut v = Vec::with_capacity(t + 1);
    for j in 0..t {
      let mut acc = F::ZERO;
      for (c, l) in self.members.iter().zip(lambda) {
        acc += *l * eval_matrix_mle(&c.matrices[j], r_x, r_y)?;
      }
      v.push(acc);
    }
    v.push(eval_vec_mle(z, r_y)?);
    Ok(v)
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CccsInstance<C, F> {
  pub comm_w: C,
  pub io: Vec<F>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccsInstance<C, F> {
  pub comm_w: C,
  pub u: F,
  pub io: Vec<F>,
  pub lambda: Vec<F>,
  pub r_x: Vec<F>,
  pub r_y: Vec<F>,
  pub v: Vec<F>,
}

/// Checks a CCCS instance–witness pair.
pub fn check_cccs<F: PrimeField, C: PartialEq>(
  ccs: &Ccs<F>,
  inst: &CccsInstance<C, F>,
  w: &[F],
  commit: impl Fn(&[F]) -> C,
) -> Result<(), CcsError> {
  ccs.validate()?;
  let z = ccs.z(w, F::ONE, &inst.io)?;
  if commit(w) != inst.comm_w {
    return Err(CcsError::Commitment);
  }
  ccs.is_satisfied(&z)
}

/// Checks an ACCS instance–witness pair against a family.
pub fn check_accs<F: PrimeField, C: PartialEq>(
  family: &Family<F>,
  inst: &AccsInstance<C, F>,
  w: &[F],
  commit: impl Fn(&[F]) -> C,
) -> Result<(), CcsError> {
  let c0 = family.member(0);
  let (s, s_prime) = family.point_dims();
  dim("lambda", family.k(), inst.lambda.len())?;
  check_exact("r_x", s, &inst.r_x)?;
  check_exact("r_y", s_prime, &inst.r_y)?;
  dim("v", c0.t() + 1, inst.v.len())?;
  let z = c0.z(w, inst.u, &inst.io)?;
  if commit(w) != inst.comm_w {
    return Err(CcsError::Commitment);
  }
  let expected = family.claims(&inst.lambda, &z, &inst.r_x, &inst.r_y)?;
  match expected.iter().zip(&inst.v).position(|(a, b)| a != b) {
    None => Ok(()),
    Some(index) => Err(CcsError::Claim { index }),
  }
}

/// The honest ACCS for a fresh CCCS of predicate `k` at (r_x, r_y): u = 1, λ = e_k. This is
/// the base case of the HFS (`from_r1cs_instance_witness` with fixed points).
pub fn accs_from_cccs<F: PrimeField, C: Clone>(
  family: &Family<F>,
  k: usize,
  inst: &CccsInstance<C, F>,
  w: &[F],
  r_x: Vec<F>,
  r_y: Vec<F>,
) -> Result<AccsInstance<C, F>, CcsError> {
  if k >= family.k() {
    return Err(CcsError::Family(format!(
      "predicate {k} >= K = {}",
      family.k()
    )));
  }
  let mut lambda = vec![F::ZERO; family.k()];
  lambda[k] = F::ONE;
  let z = family.member(k).z(w, F::ONE, &inst.io)?;
  let v = family.claims(&lambda, &z, &r_x, &r_y)?;
  Ok(AccsInstance {
    comm_w: inst.comm_w.clone(),
    u: F::ONE,
    io: inst.io.clone(),
    lambda,
    r_x,
    r_y,
    v,
  })
}
