//! Decider: the terminal ACCS relation check on a folded instance and its witness.
//!
//! It checks, in this order: lengths, `comm_W = Com(W)`, the index opening (Direct:
//! `comm_M[j] = Com(ck_index_j, λ)`; Span: public λ = witness λ), and the claims
//! `v_j = Σ_k λ_k M̃_{k,j}(r_x, r_y)` and `v_t = z̃(r_y)` with `z = (W ‖ u ‖ io)`.
//!
//! The evaluation here is a direct sparse sum with per-entry `eq` products computed bit by bit.
//! It shares no code with the prover's tables. The tests also run the independent kn-ccs
//! oracle on every output.
use super::{check_len, HfsError, HfsParams, RunningInstance, RunningWitness, Variant};
use crate::traits::Engine;
use ff::{Field, PrimeField};

/// `eq(bits(idx), p) = Π_i (bit_i(idx) ? p_i : 1 − p_i)`.
fn eq_at_index<F: PrimeField>(idx: usize, p: &[F]) -> F {
  p.iter().enumerate().fold(F::ONE, |acc, (i, r)| {
    acc * if (idx >> i) & 1 == 1 { *r } else { F::ONE - r }
  })
}

/// Checks `(U, W)` against the family. The error names the first failed condition.
pub fn decide<E: Engine, V: Variant<E>>(
  pp: &HfsParams<E>,
  u: &RunningInstance<E, V>,
  w: &RunningWitness<E>,
) -> Result<(), HfsError> {
  let t = pp.t();
  check_len("instance.io", pp.num_io(), u.io.len())?;
  check_len("instance.r_x", pp.s(), u.r_x.len())?;
  check_len("instance.r_y", pp.s_prime(), u.r_y.len())?;
  check_len("instance.v", t + 1, u.v.len())?;
  V::check_index(pp, &u.index, "instance")?;
  check_len("witness.w", pp.num_w(), w.w.len())?;
  check_len("witness.lambda", pp.k(), w.lambda.len())?;

  if pp.commit_w(&w.w)? != u.comm_w {
    return Err(HfsError::Commitment);
  }
  V::check_opening(pp, &u.index, &w.lambda)?;

  for j in 0..t {
    let mut acc = E::Scalar::ZERO;
    for (sh, l) in pp.shapes().iter().zip(&w.lambda) {
      for &(r, c, val) in &sh.matrices()[j] {
        acc += *l * val * eq_at_index(r, &u.r_x) * eq_at_index(c, &u.r_y);
      }
    }
    if acc != u.v[j] {
      return Err(HfsError::Claim { index: j });
    }
  }
  let z = [w.w.as_slice(), &[u.u], &u.io].concat();
  let vz = z
    .iter()
    .enumerate()
    .fold(E::Scalar::ZERO, |a, (i, x)| a + *x * eq_at_index(i, &u.r_y));
  if vz != u.v[t] {
    return Err(HfsError::Claim { index: t });
  }
  Ok(())
}
