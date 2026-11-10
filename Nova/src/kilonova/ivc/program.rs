//! In-circuit predicate selection φ (PLAN.md P4, closes G4) and the deterministic-schedule
//! program used by the tests and `kn-run`.
//!
//! A [`PredicateProgram`] is a predicate set together with its selection function
//! `φ(i, z_i) → k`. The primary circuit of predicate k evaluates φ on its input state and
//! enforces `φ(i, z_i) = k`, so the schedule is a consequence of the state (the pc lives in the
//! application state, SuperNova-style) and the host cannot choose it. The program also names the
//! family (label, stable member ids, selector descriptor), which enter the family digest.
use crate::{
  frontend::{num::AllocatedNum, AllocatedBit, ConstraintSystem, SynthesisError},
  kilonova::PredicateSet,
};
use ff::PrimeField;

/// A predicate set with an in-circuit selection function φ.
pub trait PredicateProgram<F: PrimeField>: PredicateSet<F> {
  /// Name of the family (enters the family digest).
  fn family_label(&self) -> String;
  /// Stable id of the member at position `k` (enters the family digest).
  fn member_id(&self, k: usize) -> String;
  /// Canonical description of φ (enters the family digest).
  fn selector_descriptor(&self) -> Vec<u8>;
  /// Native φ: the predicate selected at step `i` on state `z`, or `None` if no member is
  /// selected (the program has halted; no circuit can make progress).
  fn select(&self, i: usize, z: &[F]) -> Option<usize>;
  /// In-circuit φ on `(i, z)`; returns the selected id as a field element.
  fn synthesize_select<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    i: &AllocatedNum<F>,
    z: &[AllocatedNum<F>],
  ) -> Result<AllocatedNum<F>, SynthesisError>;
}

/// Bits of the program register that are decomposed (`< 2^253 < p` for the 255-bit fields used
/// here, so the decomposition is unique).
pub const PROGRAM_BITS: usize = 253;

/// Deterministic schedule as a φ function: wraps a predicate set and appends a **program
/// register** `prog` to the state. `prog` holds the schedule as base-2^b digits
/// (b = max(1, ⌈log₂ K⌉)), least significant first; φ(i, z) = the low b bits of `prog`, and every
/// member also sets `prog' = (prog − k) / 2^b` (exact, because φ forced the low digit to be k).
/// A schedule of T steps needs `b·T ≤ L` with `L = b·⌊253 / b⌋`; after it, `prog = 0` selects
/// member 0 forever.
#[derive(Clone, Debug)]
pub struct Scheduled<P> {
  inner: P,
  label: String,
  ids: Vec<String>,
  bits: usize,
}

impl<P> Scheduled<P> {
  /// Wraps `inner`, whose K members get the stable ids `ids`.
  pub fn new(inner: P, label: impl Into<String>, ids: Vec<String>) -> Self {
    let k = ids.len().max(1);
    let bits = (k.next_power_of_two().trailing_zeros() as usize).max(1);
    Self {
      inner,
      label: label.into(),
      ids,
      bits,
    }
  }

  /// The wrapped predicate set.
  pub fn inner(&self) -> &P {
    &self.inner
  }

  /// Bits per schedule digit.
  pub fn bits(&self) -> usize {
    self.bits
  }

  /// Bits of `prog` that φ decomposes.
  pub fn decomposed_bits(&self) -> usize {
    self.bits * (PROGRAM_BITS / self.bits)
  }

  /// Longest schedule a single `prog` can hold.
  pub fn capacity(&self) -> usize {
    PROGRAM_BITS / self.bits
  }

  /// `prog = Σ_i ids[i]·2^{b·i}`, or `None` if an id is out of range or the schedule is too long.
  pub fn encode<F: PrimeField>(&self, ids: &[usize]) -> Option<F> {
    if ids.len() > self.capacity() || ids.iter().any(|&k| k >= self.ids.len()) {
      return None;
    }
    let base = F::from(1u64 << self.bits);
    Some(
      ids
        .iter()
        .rev()
        .fold(F::ZERO, |acc, &k| acc * base + F::from(k as u64)),
    )
  }

  /// The initial state for the application state `app` and the schedule `ids`.
  pub fn z0<F: PrimeField>(&self, app: &[F], ids: &[usize]) -> Option<Vec<F>> {
    let prog = self.encode(ids)?;
    Some([app, &[prog]].concat())
  }
}

/// Little-endian bits of `x` (`len` of them) if `x < 2^len`, else `None`. Field arithmetic only,
/// so it does not depend on the representation's byte order.
fn low_bits<F: PrimeField>(x: F, len: usize) -> Option<Vec<bool>> {
  let half = F::from(2).invert().unwrap();
  let mut x = x;
  let mut out = Vec::with_capacity(len);
  for _ in 0..len {
    let b = bool::from(x.is_odd());
    out.push(b);
    if b {
      x -= F::ONE;
    }
    x *= half;
  }
  bool::from(x.is_zero()).then_some(out)
}

impl<F: PrimeField, P: PredicateSet<F>> PredicateSet<F> for Scheduled<P> {
  fn arity(&self) -> usize {
    self.inner.arity() + 1
  }

  fn num_predicates(&self) -> usize {
    self.inner.num_predicates()
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    id: usize,
    cs: &mut CS,
    z: &[AllocatedNum<F>],
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
    let a = self.inner.arity();
    if z.len() != a + 1 {
      return Err(SynthesisError::IncompatibleLengthVector(
        "scheduled z".into(),
      ));
    }
    let mut out = self
      .inner
      .synthesize(id, &mut cs.namespace(|| "app"), &z[..a])?;
    let prog = &z[a];
    let k = F::from(id as u64);
    let shift = F::from(1u64 << self.bits);
    let next = AllocatedNum::alloc(cs.namespace(|| "prog next"), || {
      prog
        .get_value()
        .map(|p| (p - k) * shift.invert().unwrap())
        .ok_or(SynthesisError::AssignmentMissing)
    })?;
    // 2^b · prog' = prog − k
    cs.enforce(
      || "prog = k + 2^b prog'",
      |lc| lc + (shift, next.get_variable()),
      |lc| lc + CS::one(),
      |lc| lc + prog.get_variable() - (k, CS::one()),
    );
    out.push(next);
    Ok(out)
  }
}

impl<F: PrimeField, P: PredicateSet<F>> PredicateProgram<F> for Scheduled<P> {
  fn family_label(&self) -> String {
    self.label.clone()
  }

  fn member_id(&self, k: usize) -> String {
    self.ids[k].clone()
  }

  fn selector_descriptor(&self) -> Vec<u8> {
    let mut d = b"kn-phi-scheduled-v1".to_vec();
    for v in [self.bits, self.decomposed_bits(), self.inner.arity()] {
      d.extend_from_slice(&(v as u64).to_le_bytes());
    }
    d
  }

  fn select(&self, _i: usize, z: &[F]) -> Option<usize> {
    let bits = low_bits(*z.last()?, self.decomposed_bits())?;
    let k = bits[..self.bits]
      .iter()
      .rev()
      .fold(0usize, |acc, &b| 2 * acc + b as usize);
    (k < self.ids.len()).then_some(k)
  }

  fn synthesize_select<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    _i: &AllocatedNum<F>,
    z: &[AllocatedNum<F>],
  ) -> Result<AllocatedNum<F>, SynthesisError> {
    let prog = z
      .last()
      .ok_or_else(|| SynthesisError::IncompatibleLengthVector("empty z".into()))?;
    let len = self.decomposed_bits();
    let values = prog.get_value().map(|p| low_bits(p, len));
    let bits = (0..len)
      .map(|j| {
        AllocatedBit::alloc(
          cs.namespace(|| format!("prog bit {j}")),
          values.as_ref().map(|v| v.as_ref().is_some_and(|v| v[j])),
        )
      })
      .collect::<Result<Vec<_>, _>>()?;
    // Σ 2^j b_j = prog (unique: the sum is < 2^253 < p)
    cs.enforce(
      || "prog = sum 2^j b_j",
      |lc| {
        let mut c = F::ONE;
        bits.iter().fold(lc, |lc, b| {
          let lc = lc + (c, b.get_variable());
          c = c.double();
          lc
        })
      },
      |lc| lc + CS::one(),
      |lc| lc + prog.get_variable(),
    );
    let sel_val = bits[..self.bits].iter().rev().try_fold(F::ZERO, |acc, b| {
      b.get_value().map(|v| acc.double() + F::from(v as u64))
    });
    let sel = AllocatedNum::alloc(cs.namespace(|| "selected"), || {
      sel_val.ok_or(SynthesisError::AssignmentMissing)
    })?;
    cs.enforce(
      || "selected = low digit",
      |lc| {
        let mut c = F::ONE;
        bits[..self.bits].iter().fold(lc, |lc, b| {
          let lc = lc + (c, b.get_variable());
          c = c.double();
          lc
        })
      },
      |lc| lc + CS::one(),
      |lc| lc + sel.get_variable(),
    );
    Ok(sel)
  }
}
