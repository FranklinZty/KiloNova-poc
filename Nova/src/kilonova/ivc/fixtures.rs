//! P5 predicate family for the v2 recursion tests and `kn-run` (arity 2, K ≤ 4).
//!
//! The members change the wiring, use negative coefficients and constants:
//!
//! - 0: `(x, y) ↦ (x³ + y + 5, x)`, or with `pow5`: `(x⁵ + y, x)` where `x⁵` is **one native
//!   degree-5 row** ([`super::enforce_pow5`], template [`super::PrimaryTemplate::R1csPow5`]);
//! - 1: `(x, y) ↦ (x² − y + 7, y + 1)`;
//! - 2: `(x, y) ↦ (x·y + 9, x² − 3)`;
//! - 3: `(x, y) ↦ (y² − x, x + y + 11)`.
use crate::{
  frontend::{num::AllocatedNum, ConstraintSystem, SynthesisError},
  kilonova::PredicateSet,
};
use core::marker::PhantomData;
use ff::PrimeField;

/// The P5 chain family.
#[derive(Clone, Debug)]
pub struct ChainPredicates<F: PrimeField> {
  k: usize,
  pow5: bool,
  _p: PhantomData<F>,
}

impl<F: PrimeField> ChainPredicates<F> {
  /// The first `k` members (1 ≤ k ≤ 4); `pow5` makes member 0 the native degree-5 one.
  pub fn new(k: usize, pow5: bool) -> Self {
    assert!((1..=4).contains(&k), "1 <= K <= 4");
    Self {
      k,
      pow5,
      _p: PhantomData,
    }
  }

  /// Native evaluation of member `id`.
  pub fn output(&self, id: usize, z: &[F]) -> Vec<F> {
    let (x, y) = (z[0], z[1]);
    match id {
      0 if self.pow5 => vec![x.square().square() * x + y, x],
      0 => vec![x.square() * x + y + F::from(5), x],
      1 => vec![x.square() - y + F::from(7), y + F::ONE],
      2 => vec![x * y + F::from(9), x.square() - F::from(3)],
      _ => vec![y.square() - x, x + y + F::from(11)],
    }
  }

  /// Native evaluation of a schedule.
  pub fn run(&self, z0: &[F], ids: &[usize]) -> Vec<F> {
    ids.iter().fold(z0.to_vec(), |z, &k| self.output(k, &z))
  }
}

/// `out = c + Σ k_i a_i` as one constraint.
fn lin<F: PrimeField, CS: ConstraintSystem<F>>(
  cs: &mut CS,
  name: &str,
  terms: &[(F, &AllocatedNum<F>)],
  c: F,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let v = terms
    .iter()
    .try_fold(c, |acc, (k, a)| a.get_value().map(|x| acc + *k * x));
  let out = AllocatedNum::alloc(cs.namespace(|| name.to_string()), || {
    v.ok_or(SynthesisError::AssignmentMissing)
  })?;
  cs.enforce(
    || format!("{name} = lc"),
    |lc| {
      terms.iter().fold(lc + (c, CS::one()), |lc, (k, a)| {
        lc + (*k, a.get_variable())
      })
    },
    |lc| lc + CS::one(),
    |lc| lc + out.get_variable(),
  );
  Ok(out)
}

impl<F: PrimeField> PredicateSet<F> for ChainPredicates<F> {
  fn arity(&self) -> usize {
    2
  }

  fn num_predicates(&self) -> usize {
    self.k
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    id: usize,
    cs: &mut CS,
    z: &[AllocatedNum<F>],
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
    let (x, y) = (&z[0], &z[1]);
    let one = F::ONE;
    match id {
      0 if self.pow5 => {
        let x5 = AllocatedNum::alloc(cs.namespace(|| "x5"), || {
          x.get_value()
            .map(|x| x.square().square() * x)
            .ok_or(SynthesisError::AssignmentMissing)
        })?;
        super::enforce_pow5(cs, x, &x5);
        let a = lin(cs, "a", &[(one, &x5), (one, y)], F::ZERO)?;
        let b = lin(cs, "b", &[(one, x)], F::ZERO)?;
        Ok(vec![a, b])
      }
      0 => {
        let x2 = x.square(cs.namespace(|| "x2"))?;
        let x3 = x2.mul(cs.namespace(|| "x3"), x)?;
        let a = lin(cs, "a", &[(one, &x3), (one, y)], F::from(5))?;
        let b = lin(cs, "b", &[(one, x)], F::ZERO)?;
        Ok(vec![a, b])
      }
      1 => {
        let x2 = x.square(cs.namespace(|| "x2"))?;
        let a = lin(cs, "a", &[(one, &x2), (-one, y)], F::from(7))?;
        let b = lin(cs, "b", &[(one, y)], one)?;
        Ok(vec![a, b])
      }
      2 => {
        let xy = x.mul(cs.namespace(|| "xy"), y)?;
        let x2 = x.square(cs.namespace(|| "x2"))?;
        let a = lin(cs, "a", &[(one, &xy)], F::from(9))?;
        let b = lin(cs, "b", &[(one, &x2)], -F::from(3))?;
        Ok(vec![a, b])
      }
      _ => {
        let y2 = y.square(cs.namespace(|| "y2"))?;
        let a = lin(cs, "a", &[(one, &y2), (-one, x)], F::ZERO)?;
        let b = lin(cs, "b", &[(one, x), (one, y)], F::from(11))?;
        Ok(vec![a, b])
      }
    }
  }
}
