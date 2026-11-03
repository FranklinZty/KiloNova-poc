#![allow(dead_code)]
use ff::PrimeField;
use kn_ccs::{mle::num_vars, Ccs};
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};

pub fn rng(seed: u64) -> ChaCha20Rng {
  ChaCha20Rng::seed_from_u64(seed)
}

/// A toy binding-for-tests commitment: a fixed random linear form of `w`, plus `len(w)`.
/// Only the checker's wiring is under test here; P3 plugs in Pedersen.
pub fn toy_commit<F: PrimeField>(w: &[F]) -> (F, usize) {
  let mut r = rng(0xC0FFEE);
  (
    w.iter()
      .fold(F::ZERO, |acc, x| acc + *x * F::random(&mut r)),
    w.len(),
  )
}

pub fn random_point<F: PrimeField>(len: usize, r: &mut impl RngCore) -> Vec<F> {
  (0..len).map(|_| F::random(&mut *r)).collect()
}

/// Random points sized for a CCS (s, s').
pub fn points<F: PrimeField>(ccs: &Ccs<F>, r: &mut impl RngCore) -> (Vec<F>, Vec<F>) {
  (
    random_point(num_vars(ccs.m), r),
    random_point(num_vars(ccs.n()), r),
  )
}

/// Naive dense residual, independent of `Ccs::residual`'s sparse mat-vec.
pub fn dense_residual<F: PrimeField>(ccs: &Ccs<F>, z: &[F]) -> Vec<F> {
  let dense: Vec<Vec<Vec<F>>> = ccs.matrices.iter().map(|m| m.to_dense()).collect();
  (0..ccs.m)
    .map(|row| {
      let mz = |j: usize| -> F {
        dense[j][row]
          .iter()
          .zip(z)
          .fold(F::ZERO, |acc, (a, b)| acc + *a * b)
      };
      ccs
        .template
        .multisets
        .iter()
        .zip(&ccs.template.coeffs)
        .map(|(s, c)| s.iter().fold(*c, |acc, &j| acc * mz(j)))
        .fold(F::ZERO, |acc, x| acc + x)
    })
    .collect()
}
