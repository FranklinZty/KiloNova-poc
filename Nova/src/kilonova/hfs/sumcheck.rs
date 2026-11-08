//! Sum-check over product terms of multilinear tables, transcript v2.
//!
//! Round i binds variable i, i.e. bit i of the table index (least significant first), so the
//! resulting point is directly the MLE point in the kn-ccs / spec N9 bit order (no reversal,
//! unlike v1). A round message is the evaluations of the round polynomial at 0, 1, …, deg.
use super::{HfsError, Phase};
use crate::{constants::NUM_CHALLENGE_BITS, traits::ROTrait};
use ff::PrimeField;

/// `coefficient × Π tables[idx]`.
pub(crate) type Term<F> = (F, Vec<usize>);

/// `eq(p, ·)` over the hypercube: entry `b` is `Π_i (b_i ? p_i : 1 − p_i)`.
pub(crate) fn eq_table<F: PrimeField>(p: &[F]) -> Vec<F> {
  let mut t = vec![F::ONE];
  for r in p {
    let n = t.len();
    let mut next = vec![F::ZERO; 2 * n];
    for (j, v) in t.iter().enumerate() {
      next[j + n] = *v * r;
      next[j] = *v - next[j + n];
    }
    t = next;
  }
  t
}

/// `eq(a, b) = Π_i (a_i b_i + (1 − a_i)(1 − b_i))`.
pub(crate) fn eq_eval<F: PrimeField>(a: &[F], b: &[F]) -> F {
  a.iter().zip(b).fold(F::ONE, |acc, (x, y)| {
    acc * (*x * y + (F::ONE - x) * (F::ONE - y))
  })
}

/// `1, x, x², …` (`n` entries).
pub(crate) fn powers<F: PrimeField>(x: F, n: usize) -> Vec<F> {
  let mut out = Vec::with_capacity(n);
  let mut acc = F::ONE;
  for _ in 0..n {
    out.push(acc);
    acc *= x;
  }
  out
}

/// Value at `r` of the degree-`(len − 1)` polynomial with the given evaluations at 0..len.
pub(crate) fn interpolate<F: PrimeField>(evals: &[F], r: F) -> F {
  let n = evals.len();
  let pts: Vec<F> = (0..n as u64).map(F::from).collect();
  (0..n).fold(F::ZERO, |acc, i| {
    let (num, den) = (0..n)
      .filter(|&j| j != i)
      .fold((F::ONE, F::ONE), |(nu, de), j| {
        (nu * (r - pts[j]), de * (pts[i] - pts[j]))
      });
    // den ≠ 0: the points 0..n are distinct for n far below the characteristic.
    acc + evals[i] * num * den.invert().unwrap()
  })
}

/// Proves `Σ_b Σ_terms c · Π tables(b)`. Returns the round messages, the point and the tables
/// evaluated at the point.
pub(crate) fn prove<F: PrimeField, RO: ROTrait<F>>(
  mut tables: Vec<Vec<F>>,
  terms: &[Term<F>],
  deg: usize,
  ro: &mut RO,
) -> (Vec<Vec<F>>, Vec<F>, Vec<F>) {
  let rounds = tables
    .first()
    .map_or(0, |t| t.len().trailing_zeros() as usize);
  debug_assert!(tables.iter().all(|t| t.len() == 1 << rounds));
  let mut msgs = Vec::with_capacity(rounds);
  let mut point = Vec::with_capacity(rounds);
  let ts: Vec<F> = (0..=deg as u64).map(F::from).collect();
  for _ in 0..rounds {
    let half = tables[0].len() / 2;
    let mut evals = vec![F::ZERO; deg + 1];
    for b in 0..half {
      for (e, t) in evals.iter_mut().zip(&ts) {
        for (c, idx) in terms {
          *e += idx.iter().fold(*c, |p, &k| {
            let (lo, hi) = (tables[k][2 * b], tables[k][2 * b + 1]);
            p * (lo + (hi - lo) * t)
          });
        }
      }
    }
    evals.iter().for_each(|e| ro.absorb(*e));
    let r = ro.squeeze(NUM_CHALLENGE_BITS);
    for tab in tables.iter_mut() {
      *tab = (0..half)
        .map(|b| tab[2 * b] + (tab[2 * b + 1] - tab[2 * b]) * r)
        .collect();
    }
    msgs.push(evals);
    point.push(r);
  }
  let finals = tables.into_iter().map(|t| t[0]).collect();
  (msgs, point, finals)
}

/// Checks the round messages against `claim` and returns the final claim and the point. The
/// message shape (number of rounds and `deg + 1` evaluations each) is checked by the caller.
pub(crate) fn verify<F: PrimeField, RO: ROTrait<F>>(
  mut claim: F,
  msgs: &[Vec<F>],
  phase: Phase,
  ro: &mut RO,
) -> Result<(F, Vec<F>), HfsError> {
  let mut point = Vec::with_capacity(msgs.len());
  for (round, p) in msgs.iter().enumerate() {
    if p[0] + p[1] != claim {
      return Err(HfsError::SumcheckRound { phase, round });
    }
    p.iter().for_each(|e| ro.absorb(*e));
    let r = ro.squeeze(NUM_CHALLENGE_BITS);
    claim = interpolate(p, r);
    point.push(r);
  }
  Ok((claim, point))
}

#[cfg(test)]
mod tests {
  use super::*;
  use halo2curves::pasta::Fq as F;

  #[test]
  fn eq_table_bit_order_and_interpolation() {
    let p = [F::from(3), F::from(5), F::from(7)];
    let t = eq_table(&p);
    for (b, v) in t.iter().enumerate() {
      let bits: Vec<F> = (0..3).map(|i| F::from(((b >> i) & 1) as u64)).collect();
      assert_eq!(*v, eq_eval(&bits, &p));
    }
    // p(x) = 2x³ − x + 4 from its values at 0..=3.
    let f = |x: F| x.square() * x * F::from(2) - x + F::from(4);
    let evals: Vec<F> = (0..4u64).map(|i| f(F::from(i))).collect();
    assert_eq!(interpolate(&evals, F::from(11)), f(F::from(11)));
  }
}
