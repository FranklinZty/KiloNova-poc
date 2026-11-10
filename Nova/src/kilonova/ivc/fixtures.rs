//! Predicate families for the v2 recursion tests and `kn-run` (arity 2, K ≤ 16).
//!
//! The members change the wiring, use negative coefficients and constants:
//!
//! - 0: `(x, y) ↦ (x³ + y + 5, x)`, or with `pow5`: `(x⁵ + y, x)` where `x⁵` is **one native
//!   degree-5 row** ([`super::enforce_pow5`], template [`super::PrimaryTemplate::R1csPow5`]);
//! - 1: `(x, y) ↦ (x² − y + 7, y + 1)`;
//! - 2: `(x, y) ↦ (x·y + 9, x² − 3)`;
//! - 3: `(x, y) ↦ (y² − x, x + y + 11)`;
//! - 4 ≤ m < 16 (P4): `p = a·b` with `a = (m & 1 ? x : y)`, `b = (m & 2 ? x : y)`, then
//!   `p ← p·x` if `m & 4` and `p ← p·y` if `m & 8`; output `(p + (−1)^m·y + m, x − m)`.
//!
//! P4 adds stable member ids (`chain/m<k>`, `chain/m0-pow5`), test variants with reordered
//! members or one substituted constant, and the [`Scheduled`] programs (φ) used by the tests.
use super::program::Scheduled;
use crate::{
  frontend::{num::AllocatedNum, ConstraintSystem, SynthesisError},
  kilonova::{test_utils::ExamplePredicates, PredicateSet},
};
use core::marker::PhantomData;
use ff::PrimeField;

/// Largest supported family.
pub const MAX_CHAIN_K: usize = 16;

/// The chain family.
#[derive(Clone, Debug)]
pub struct ChainPredicates<F: PrimeField> {
  k: usize,
  pow5: bool,
  /// position → member (identity unless reordered).
  order: Vec<usize>,
  /// A member whose additive constant is changed by +1 under the same id (substitution test).
  tweak: Option<usize>,
  _p: PhantomData<F>,
}

impl<F: PrimeField> ChainPredicates<F> {
  /// The first `k` members (1 ≤ k ≤ 16); `pow5` makes member 0 the native degree-5 one.
  pub fn new(k: usize, pow5: bool) -> Self {
    assert!((1..=MAX_CHAIN_K).contains(&k), "1 <= K <= 16");
    Self {
      k,
      pow5,
      order: (0..k).collect(),
      tweak: None,
      _p: PhantomData,
    }
  }

  /// The same members in another order (`order[pos]` is the member at position `pos`).
  pub fn reordered(k: usize, order: Vec<usize>) -> Self {
    let mut s = Self::new(k, false);
    let mut sorted = order.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..k).collect::<Vec<_>>(), "a permutation");
    s.order = order;
    s
  }

  /// The same family with member `m`'s additive constant changed by +1 (same id).
  pub fn substituted(k: usize, m: usize) -> Self {
    let mut s = Self::new(k, false);
    s.tweak = Some(m);
    s
  }

  /// Stable id of the member at position `pos`.
  pub fn member_id(&self, pos: usize) -> String {
    match self.order[pos] {
      0 if self.pow5 => "chain/m0-pow5".to_string(),
      m => format!("chain/m{m}"),
    }
  }

  /// The scheduled program over this family (φ = next digit of the program register).
  pub fn program(self) -> Scheduled<Self> {
    let ids = (0..self.k).map(|p| self.member_id(p)).collect();
    Scheduled::new(self, "kn-p4-chain", ids)
  }

  fn constant(&self, m: usize, c: u64) -> F {
    F::from(c)
      + if self.tweak == Some(m) {
        F::ONE
      } else {
        F::ZERO
      }
  }

  /// Native evaluation of the member at position `pos`.
  pub fn output(&self, pos: usize, z: &[F]) -> Vec<F> {
    let (x, y) = (z[0], z[1]);
    let m = self.order[pos];
    let c = |v: u64| self.constant(m, v);
    match m {
      0 if self.pow5 => vec![x.square().square() * x + y + c(0), x],
      0 => vec![x.square() * x + y + c(5), x],
      1 => vec![x.square() - y + c(7), y + F::ONE],
      2 => vec![x * y + c(9), x.square() - F::from(3)],
      3 => vec![y.square() - x + c(0), x + y + F::from(11)],
      _ => {
        let a = if m & 1 == 1 { x } else { y };
        let b = if m & 2 == 2 { x } else { y };
        let mut p = a * b;
        if m & 4 != 0 {
          p *= x;
        }
        if m & 8 != 0 {
          p *= y;
        }
        let sy = if m % 2 == 1 { -y } else { y };
        vec![p + sy + c(m as u64), x - F::from(m as u64)]
      }
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
    pos: usize,
    cs: &mut CS,
    z: &[AllocatedNum<F>],
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
    let (x, y) = (&z[0], &z[1]);
    let one = F::ONE;
    let m = self.order[pos];
    let c = |v: u64| self.constant(m, v);
    match m {
      0 if self.pow5 => {
        let x5 = AllocatedNum::alloc(cs.namespace(|| "x5"), || {
          x.get_value()
            .map(|x| x.square().square() * x)
            .ok_or(SynthesisError::AssignmentMissing)
        })?;
        super::enforce_pow5(cs, x, &x5);
        let a = lin(cs, "a", &[(one, &x5), (one, y)], c(0))?;
        let b = lin(cs, "b", &[(one, x)], F::ZERO)?;
        Ok(vec![a, b])
      }
      0 => {
        let x2 = x.square(cs.namespace(|| "x2"))?;
        let x3 = x2.mul(cs.namespace(|| "x3"), x)?;
        let a = lin(cs, "a", &[(one, &x3), (one, y)], c(5))?;
        let b = lin(cs, "b", &[(one, x)], F::ZERO)?;
        Ok(vec![a, b])
      }
      1 => {
        let x2 = x.square(cs.namespace(|| "x2"))?;
        let a = lin(cs, "a", &[(one, &x2), (-one, y)], c(7))?;
        let b = lin(cs, "b", &[(one, y)], one)?;
        Ok(vec![a, b])
      }
      2 => {
        let xy = x.mul(cs.namespace(|| "xy"), y)?;
        let x2 = x.square(cs.namespace(|| "x2"))?;
        let a = lin(cs, "a", &[(one, &xy)], c(9))?;
        let b = lin(cs, "b", &[(one, &x2)], -F::from(3))?;
        Ok(vec![a, b])
      }
      3 => {
        let y2 = y.square(cs.namespace(|| "y2"))?;
        let a = lin(cs, "a", &[(one, &y2), (-one, x)], c(0))?;
        let b = lin(cs, "b", &[(one, x), (one, y)], F::from(11))?;
        Ok(vec![a, b])
      }
      _ => {
        let a = if m & 1 == 1 { x } else { y };
        let b = if m & 2 == 2 { x } else { y };
        let mut p = a.mul(cs.namespace(|| "ab"), b)?;
        if m & 4 != 0 {
          p = p.mul(cs.namespace(|| "abx"), x)?;
        }
        if m & 8 != 0 {
          p = p.mul(cs.namespace(|| "aby"), y)?;
        }
        let sy = if m % 2 == 1 { -one } else { one };
        let a = lin(cs, "a", &[(one, &p), (sy, y)], c(m as u64))?;
        let b = lin(cs, "b", &[(one, x)], -F::from(m as u64))?;
        Ok(vec![a, b])
      }
    }
  }
}

/// The scheduled program over the K = 3 v1 fixture (`test_utils::ExamplePredicates`).
pub fn example_program<F: PrimeField>() -> Scheduled<ExamplePredicates<F>> {
  Scheduled::new(
    ExamplePredicates::<F>::default(),
    "kn-p4-example",
    (0..3).map(|k| format!("example/m{k}")).collect(),
  )
}
