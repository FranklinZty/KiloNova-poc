//! In-circuit building blocks of the v2 recursion (P5):
//!
//! - [`Expr`]: linear combinations with values (no constraint until allocated or multiplied);
//! - [`NnPoint`]: an E1 point carried as non-native 4 × 64-bit limbs inside an E1::Scalar
//!   circuit, with the infinity flag derived from the limbs;
//! - [`AllocatedRelaxedR1CSInstanceN`]: the running CycleFold accumulator and the **n-input**
//!   Nova fold gadget (generalises `nova/circuit/r1cs.rs::fold_with_r1cs` from 2 public
//!   inputs to any number, and absorbs the running instance);
//! - [`verify_hfs`]: the HFS v2 verifier gadget (sum-checks, end checks, transcript v2),
//!   identical to `hfs::NIFS::verify` for μ = ν = 1.
//!
//! Everything here is succinct: it takes instances, proof messages and hints, never a witness
//! of another circuit or a matrix.
use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_CHALLENGE_BITS},
  frontend::{
    num::AllocatedNum, AllocatedBit, Assignment, Boolean, ConstraintSystem, LinearCombination,
    SynthesisError,
  },
  gadgets::{
    ecc::AllocatedPoint,
    nonnative::{
      bignat::{nat_to_limbs, BigNat, BigNatParams},
      util::{f_to_nat, Num},
    },
    utils::{alloc_bignat_constant, conditionally_select, le_bits_to_num},
  },
  kilonova::{
    hfs::CcsTemplate,
    transcript::v2::{TAG_X_CLAIMS, TAG_Y_CLAIMS},
  },
  r1cs::RelaxedR1CSInstance,
  traits::{commitment::CommitmentTrait, Engine, Group, ROCircuitTrait, ROConstantsCircuit},
};
use ff::{Field, PrimeField, PrimeFieldBits};
use num_bigint::BigInt;

/// Tag absorbed first by the CycleFold fold transcript ("KNCF" ‖ v1).
pub const TAG_CF_FOLD: u64 = 0x4b4e_4346_0001_0001;

/// A linear combination together with its value. `val` is `None` when synthesizing a shape.
#[derive(Clone)]
pub(crate) struct Expr<F: PrimeField> {
  pub(crate) lc: LinearCombination<F>,
  pub(crate) val: Option<F>,
}

impl<F: PrimeField> Expr<F> {
  pub(crate) fn zero() -> Self {
    Self {
      lc: LinearCombination::zero(),
      val: Some(F::ZERO),
    }
  }

  pub(crate) fn constant<CS: ConstraintSystem<F>>(c: F) -> Self {
    Self {
      lc: LinearCombination::zero() + (c, CS::one()),
      val: Some(c),
    }
  }

  pub(crate) fn num(n: &AllocatedNum<F>) -> Self {
    Self {
      lc: LinearCombination::zero() + n.get_variable(),
      val: n.get_value(),
    }
  }

  pub(crate) fn bit(b: &AllocatedBit) -> Self {
    Self {
      lc: LinearCombination::zero() + b.get_variable(),
      val: b.get_value().map(|x| if x { F::ONE } else { F::ZERO }),
    }
  }

  pub(crate) fn add(&self, o: &Self) -> Self {
    Self {
      lc: self.lc.clone() + &o.lc,
      val: self.val.zip(o.val).map(|(a, b)| a + b),
    }
  }

  pub(crate) fn sub(&self, o: &Self) -> Self {
    Self {
      lc: self.lc.clone() - &o.lc,
      val: self.val.zip(o.val).map(|(a, b)| a - b),
    }
  }

  pub(crate) fn scale(&self, c: F) -> Self {
    Self {
      lc: LinearCombination::zero() + (c, &self.lc),
      val: self.val.map(|a| a * c),
    }
  }

  /// Allocates a variable equal to the expression (1 constraint).
  pub(crate) fn alloc<CS: ConstraintSystem<F>>(
    &self,
    mut cs: CS,
  ) -> Result<AllocatedNum<F>, SynthesisError> {
    let n = AllocatedNum::alloc(cs.namespace(|| "v"), || self.val.get().copied())?;
    cs.enforce(
      || "v = lc",
      |_| self.lc.clone(),
      |lc| lc + CS::one(),
      |lc| lc + n.get_variable(),
    );
    Ok(n)
  }

  /// Allocates `self · o` (1 constraint).
  pub(crate) fn mul<CS: ConstraintSystem<F>>(
    &self,
    mut cs: CS,
    o: &Self,
  ) -> Result<AllocatedNum<F>, SynthesisError> {
    let n = AllocatedNum::alloc(cs.namespace(|| "p"), || {
      Ok(*self.val.get()? * *o.val.get()?)
    })?;
    cs.enforce(
      || "p = a * b",
      |_| self.lc.clone(),
      |_| o.lc.clone(),
      |lc| lc + n.get_variable(),
    );
    Ok(n)
  }
}

/// Enforces `e · active = 0`: `e = 0` unless `active = 0` (the base case).
pub(crate) fn enforce_zero_if<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  e: &Expr<F>,
  active: &Expr<F>,
) {
  cs.enforce(
    || "e * active = 0",
    |_| e.lc.clone(),
    |_| active.lc.clone(),
    |lc| lc,
  );
}

/// Allocates `value` and constrains it to that constant (the shape fixes it).
pub(crate) fn alloc_constant<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  value: F,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let n = AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(value))?;
  cs.enforce(
    || "c is constant",
    |lc| lc + n.get_variable() - (value, CS::one()),
    |lc| lc + CS::one(),
    |lc| lc,
  );
  Ok(n)
}

/// Squeezes a 128-bit challenge: its bits (little-endian) and its value.
pub(crate) fn squeeze_challenge<F, RO, CS>(
  mut cs: CS,
  ro: &mut RO,
) -> Result<(AllocatedNum<F>, Vec<AllocatedBit>), SynthesisError>
where
  F: PrimeField + PrimeFieldBits,
  RO: ROCircuitTrait<F>,
  CS: ConstraintSystem<F>,
{
  let bits = ro.squeeze(cs.namespace(|| "bits"), NUM_CHALLENGE_BITS)?;
  let n = le_bits_to_num(cs.namespace(|| "num"), &bits)?;
  Ok((n, bits))
}

/// One-hot decomposition of `k ∈ [0, n)`: bits `b_i = [k = i]` with `Σ b_i = 1` and
/// `Σ i·b_i = k`. This also range-checks `k`.
pub(crate) fn one_hot<F: PrimeField, CS: ConstraintSystem<F>>(
  cs: CS,
  k: &AllocatedNum<F>,
  n: usize,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
  one_hot_with(cs, k, n, None)
}

/// [`one_hot`] with prover-chosen bit values (`forged`, test hook for the P4 non-one-hot
/// rejection test; the bits are witness values, so any prover can choose them).
pub(crate) fn one_hot_with<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  k: &AllocatedNum<F>,
  n: usize,
  forged: Option<&[bool]>,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
  let bits = (0..n)
    .map(|i| {
      AllocatedBit::alloc(
        cs.namespace(|| format!("b{i}")),
        match forged {
          Some(f) => Some(f[i]),
          None => k.get_value().map(|v| v == F::from(i as u64)),
        },
      )
    })
    .collect::<Result<Vec<_>, _>>()?;
  cs.enforce(
    || "sum b = 1",
    |lc| bits.iter().fold(lc, |lc, b| lc + b.get_variable()),
    |lc| lc + CS::one(),
    |lc| lc + CS::one(),
  );
  cs.enforce(
    || "sum i b_i = k",
    |lc| {
      bits
        .iter()
        .enumerate()
        .fold(lc, |lc, (i, b)| lc + (F::from(i as u64), b.get_variable()))
    },
    |lc| lc + CS::one(),
    |lc| lc + k.get_variable(),
  );
  Ok(bits)
}

/// `Π_i (a_i b_i + (1 − a_i)(1 − b_i))` (2 constraints per variable).
pub(crate) fn eq_eval<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &[AllocatedNum<F>],
  b: &[AllocatedNum<F>],
) -> Result<Expr<F>, SynthesisError> {
  let one = Expr::constant::<CS>(F::ONE);
  let mut acc = one.clone();
  for (i, (x, y)) in a.iter().zip(b).enumerate() {
    let (x, y) = (Expr::num(x), Expr::num(y));
    let xy = Expr::num(&x.mul(cs.namespace(|| format!("xy{i}")), &y)?);
    // 1 − x − y + 2xy
    let f = one.sub(&x).sub(&y).add(&xy.scale(F::from(2)));
    acc = Expr::num(&acc.mul(cs.namespace(|| format!("acc{i}")), &f)?);
  }
  Ok(acc)
}

/// `1, x, …, x^{n−1}` as expressions (n − 2 constraints).
pub(crate) fn powers<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  x: &AllocatedNum<F>,
  n: usize,
) -> Result<Vec<Expr<F>>, SynthesisError> {
  let mut out = Vec::with_capacity(n);
  if n > 0 {
    out.push(Expr::constant::<CS>(F::ONE));
  }
  if n > 1 {
    out.push(Expr::num(x));
  }
  for i in 2..n {
    let p = out[i - 1].mul(cs.namespace(|| format!("x^{i}")), &Expr::num(x))?;
    out.push(Expr::num(&p));
  }
  Ok(out)
}

/// Value at `r` of the polynomial with evaluations `e` at 0..len (Lagrange), as in
/// `hfs::sumcheck::interpolate`.
pub(crate) fn interpolate<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  e: &[AllocatedNum<F>],
  r: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let n = e.len();
  let r = Expr::num(r);
  let diffs: Vec<Expr<F>> = (0..n)
    .map(|j| r.sub(&Expr::constant::<CS>(F::from(j as u64))))
    .collect();
  // prefix[i] = Π_{j<i} (r − j), suffix[i] = Π_{j>i} (r − j)
  let mut prefix = vec![Expr::constant::<CS>(F::ONE)];
  for (j, d) in diffs.iter().enumerate().take(n - 1) {
    let p = if j == 0 {
      d.clone()
    } else {
      Expr::num(&prefix[j].mul(cs.namespace(|| format!("pre{j}")), d)?)
    };
    prefix.push(p);
  }
  let mut suffix = vec![Expr::constant::<CS>(F::ONE); n];
  for i in (0..n - 1).rev() {
    suffix[i] = if i == n - 2 {
      diffs[n - 1].clone()
    } else {
      Expr::num(&suffix[i + 1].mul(cs.namespace(|| format!("suf{i}")), &diffs[i + 1])?)
    };
  }
  let mut acc = Expr::zero();
  for i in 0..n {
    let den = (0..n)
      .filter(|&j| j != i)
      .fold(F::ONE, |d, j| d * (F::from(i as u64) - F::from(j as u64)));
    // den ≠ 0 for n far below the characteristic.
    let inv = den.invert().unwrap();
    let basis = Expr::num(&prefix[i].mul(cs.namespace(|| format!("basis{i}")), &suffix[i])?);
    let term = basis.mul(cs.namespace(|| format!("term{i}")), &Expr::num(&e[i]))?;
    acc = acc.add(&Expr::num(&term).scale(inv));
  }
  acc.alloc(cs.namespace(|| "value"))
}

/// An E1 point inside an E1::Scalar circuit: x and y as `BN_N_LIMBS` limbs of `BN_LIMB_WIDTH`
/// bits (least significant first) and the infinity flag `[Σ limbs = 0]`, which matches
/// `to_coordinates` (the identity is `(0, 0, true)`, and `(0, 0)` is not on the curve).
#[derive(Clone)]
pub(crate) struct NnPoint<F: PrimeField> {
  pub(crate) x: Vec<AllocatedNum<F>>,
  pub(crate) y: Vec<AllocatedNum<F>>,
  pub(crate) inf: AllocatedNum<F>,
}

/// Limbs of a non-native field element as values of `F`.
pub(crate) fn limbs_of<B: PrimeField + PrimeFieldBits, F: PrimeField>(x: &B) -> Vec<F> {
  nat_to_limbs::<F>(&f_to_nat(x), BN_LIMB_WIDTH, BN_N_LIMBS).unwrap()
}

impl<F: PrimeField + PrimeFieldBits> NnPoint<F> {
  /// Allocates from coordinates (`None` = the identity when synthesizing a shape). When
  /// `range_check`, every limb is constrained to `BN_LIMB_WIDTH` bits.
  pub(crate) fn alloc<B: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
    mut cs: CS,
    coords: Option<(B, B, bool)>,
    range_check: bool,
  ) -> Result<Self, SynthesisError> {
    let (xv, yv) = match coords {
      Some((x, y, _)) => (Some(limbs_of::<B, F>(&x)), Some(limbs_of::<B, F>(&y))),
      None => (None, None),
    };
    let alloc_limbs = |cs: &mut CS, name: &str, v: Option<Vec<F>>| {
      (0..BN_N_LIMBS)
        .map(|i| {
          let n = AllocatedNum::alloc(cs.namespace(|| format!("{name}{i}")), || {
            v.as_ref()
              .map(|v| v[i])
              .ok_or(SynthesisError::AssignmentMissing)
          })?;
          if range_check {
            Num::new(n.get_value(), LinearCombination::zero() + n.get_variable())
              .fits_in_bits(cs.namespace(|| format!("{name}{i} range")), BN_LIMB_WIDTH)?;
          }
          Ok(n)
        })
        .collect::<Result<Vec<_>, SynthesisError>>()
    };
    let x = alloc_limbs(&mut cs, "x", xv)?;
    let y = alloc_limbs(&mut cs, "y", yv)?;
    let inf = Self::derive_inf(cs.namespace(|| "inf"), &x, &y)?;
    Ok(Self { x, y, inf })
  }

  /// `inf = [Σ limbs = 0]`. Limbs are below 2^64 when range-checked or bound by a hash to
  /// range-checked values, so the sum (< 2^67) is zero over F iff every limb is zero.
  fn derive_inf<CS: ConstraintSystem<F>>(
    mut cs: CS,
    x: &[AllocatedNum<F>],
    y: &[AllocatedNum<F>],
  ) -> Result<AllocatedNum<F>, SynthesisError> {
    let s = x
      .iter()
      .chain(y)
      .fold(Expr::zero(), |acc, l| acc.add(&Expr::num(l)));
    let inf = AllocatedNum::alloc(cs.namespace(|| "inf"), || {
      Ok(if s.val.get()?.is_zero_vartime() {
        F::ONE
      } else {
        F::ZERO
      })
    })?;
    let inv = AllocatedNum::alloc(cs.namespace(|| "inv"), || {
      Ok(s.val.get()?.invert().unwrap_or(F::ZERO))
    })?;
    // s · inv = 1 − inf and s · inf = 0 determine inf ∈ {0, 1}.
    cs.enforce(
      || "s * inv = 1 - inf",
      |_| s.lc.clone(),
      |lc| lc + inv.get_variable(),
      |lc| lc + CS::one() - inf.get_variable(),
    );
    cs.enforce(
      || "s * inf = 0",
      |_| s.lc.clone(),
      |lc| lc + inf.get_variable(),
      |lc| lc,
    );
    Ok(inf)
  }

  /// The identity: all limbs constant 0, flag 1.
  pub(crate) fn identity<CS: ConstraintSystem<F>>(mut cs: CS) -> Result<Self, SynthesisError> {
    let z = |cs: &mut CS, n: &str| {
      (0..BN_N_LIMBS)
        .map(|i| alloc_constant(cs.namespace(|| format!("{n}{i}")), F::ZERO))
        .collect::<Result<Vec<_>, _>>()
    };
    let x = z(&mut cs, "x")?;
    let y = z(&mut cs, "y")?;
    let inf = alloc_constant(cs.namespace(|| "inf"), F::ONE)?;
    Ok(Self { x, y, inf })
  }

  /// Selects among constant points with a one-hot vector: every limb and the flag is
  /// `Σ_i b_i · const_i` (allocated, 1 constraint each).
  pub(crate) fn select_constant<B: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
    mut cs: CS,
    points: &[(B, B, bool)],
    bits: &[AllocatedBit],
  ) -> Result<Self, SynthesisError> {
    let limbs: Vec<(Vec<F>, Vec<F>, F)> = points
      .iter()
      .map(|(x, y, inf)| {
        (
          limbs_of::<B, F>(x),
          limbs_of::<B, F>(y),
          if *inf { F::ONE } else { F::ZERO },
        )
      })
      .collect();
    let sel = |cs: &mut CS, name: String, f: &dyn Fn(&(Vec<F>, Vec<F>, F)) -> F| {
      let e = limbs.iter().zip(bits).fold(Expr::zero(), |acc, (p, b)| {
        acc.add(&Expr::bit(b).scale(f(p)))
      });
      e.alloc(cs.namespace(|| name))
    };
    let mut x = Vec::with_capacity(BN_N_LIMBS);
    let mut y = Vec::with_capacity(BN_N_LIMBS);
    for i in 0..BN_N_LIMBS {
      x.push(sel(&mut cs, format!("x{i}"), &|p| p.0[i])?);
      y.push(sel(&mut cs, format!("y{i}"), &|p| p.1[i])?);
    }
    let inf = sel(&mut cs, "inf".into(), &|p| p.2)?;
    Ok(Self { x, y, inf })
  }

  /// Transcript v2 / `absorb_in_ro2` encoding: x limbs, y limbs, flag.
  pub(crate) fn absorb<RO: ROCircuitTrait<F>>(&self, ro: &mut RO) {
    self.x.iter().chain(&self.y).for_each(|l| ro.absorb(l));
    ro.absorb(&self.inf);
  }

  /// `cond ? a : b`, limb by limb.
  pub(crate) fn select<CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &Self,
    b: &Self,
    cond: &Boolean,
  ) -> Result<Self, SynthesisError> {
    let sel = |cs: &mut CS, n: String, p: &AllocatedNum<F>, q: &AllocatedNum<F>| {
      conditionally_select(cs.namespace(|| n), p, q, cond)
    };
    let mut x = Vec::new();
    let mut y = Vec::new();
    for i in 0..BN_N_LIMBS {
      x.push(sel(&mut cs, format!("x{i}"), &a.x[i], &b.x[i])?);
      y.push(sel(&mut cs, format!("y{i}"), &a.y[i], &b.y[i])?);
    }
    let inf = sel(&mut cs, "inf".into(), &a.inf, &b.inf)?;
    Ok(Self { x, y, inf })
  }

  /// The coordinates as bignats (no new constraints).
  pub(crate) fn coords_bignat(&self) -> (BigNat<F>, BigNat<F>) {
    (bignat_of_limbs(&self.x), bignat_of_limbs(&self.y))
  }
}

/// A bignat whose limbs are existing variables (no constraint; the caller is responsible for
/// the limbs' range).
pub(crate) fn bignat_of_limbs<F: PrimeField>(limbs: &[AllocatedNum<F>]) -> BigNat<F> {
  let limb_values: Option<Vec<F>> = limbs.iter().map(|l| l.get_value()).collect();
  let value = limb_values.as_ref().map(|vs| {
    vs.iter().rev().fold(BigInt::from(0), |acc, v| {
      (acc << BN_LIMB_WIDTH) + f_to_nat(v)
    })
  });
  BigNat {
    limbs: limbs
      .iter()
      .map(|l| LinearCombination::zero() + l.get_variable())
      .collect(),
    limb_values,
    value,
    params: BigNatParams::new(BN_LIMB_WIDTH, BN_N_LIMBS),
  }
}

/// A bignat from little-endian bits (at most `BN_LIMB_WIDTH · BN_N_LIMBS`): every limb is a
/// linear combination of boolean variables, so it is in range without new constraints.
pub(crate) fn bignat_of_bits<F: PrimeField>(bits: &[AllocatedBit]) -> BigNat<F> {
  assert!(bits.len() <= BN_LIMB_WIDTH * BN_N_LIMBS);
  let mut limbs = Vec::with_capacity(BN_N_LIMBS);
  let mut limb_values = Some(Vec::with_capacity(BN_N_LIMBS));
  for l in 0..BN_N_LIMBS {
    let chunk = bits
      .iter()
      .skip(l * BN_LIMB_WIDTH)
      .take(BN_LIMB_WIDTH)
      .collect::<Vec<_>>();
    let mut lc = LinearCombination::zero();
    let mut val = Some(F::ZERO);
    let mut c = F::ONE;
    for b in chunk {
      lc = lc + (c, b.get_variable());
      val = val
        .zip(b.get_value())
        .map(|(v, bit)| if bit { v + c } else { v });
      c = c.double();
    }
    limbs.push(lc);
    limb_values = limb_values.zip(val).map(|(mut vs, v)| {
      vs.push(v);
      vs
    });
  }
  let value = limb_values.as_ref().map(|vs| {
    vs.iter().rev().fold(BigInt::from(0), |acc, v| {
      (acc << BN_LIMB_WIDTH) + f_to_nat(v)
    })
  });
  BigNat {
    limbs,
    limb_values,
    value,
    params: BigNatParams::new(BN_LIMB_WIDTH, BN_N_LIMBS),
  }
}

/// Allocates the limbs of a bignat as variables (1 constraint each), for absorption.
fn bignat_limb_nums<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
  mut cs: CS,
  b: &BigNat<F>,
) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
  b.as_limbs()
    .iter()
    .enumerate()
    .map(|(i, l)| l.as_allocated_num(cs.namespace(|| format!("limb{i}"))))
    .collect()
}

/// The running CycleFold accumulator: a relaxed R1CS instance of the CycleFold circuit
/// (curve E2, field E2::Scalar), allocated in an `E2::Base` circuit. `W`, `E` are native
/// points; `u` fits in `E2::Base` (it is 1 + a sum of 128-bit challenges); `X` are bignats.
#[derive(Clone)]
pub struct AllocatedRelaxedR1CSInstanceN<E: Engine> {
  pub(crate) w: AllocatedPoint<E>,
  pub(crate) e: AllocatedPoint<E>,
  pub(crate) u: AllocatedNum<E::Base>,
  /// Limb variables of `X` (kept so absorption costs no constraint).
  pub(crate) x: Vec<Vec<AllocatedNum<E::Base>>>,
}

impl<E: Engine> AllocatedRelaxedR1CSInstanceN<E> {
  /// Allocates `n` inputs; `None` allocates the default instance values.
  pub fn alloc<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    inst: Option<&RelaxedR1CSInstance<E>>,
    n: usize,
  ) -> Result<Self, SynthesisError> {
    let w = AllocatedPoint::alloc(
      cs.namespace(|| "W"),
      inst.map(|u| u.comm_W.to_coordinates()),
    )?;
    let e = AllocatedPoint::alloc(
      cs.namespace(|| "E"),
      inst.map(|u| u.comm_E.to_coordinates()),
    )?;
    let u = AllocatedNum::alloc(cs.namespace(|| "u"), || {
      Ok(inst.map_or(E::Base::ZERO, |u| {
        crate::gadgets::utils::scalar_as_base::<E>(u.u)
      }))
    })?;
    let x = (0..n)
      .map(|i| {
        let v = inst.map(|u| limbs_of::<E::Scalar, E::Base>(&u.X[i]));
        (0..BN_N_LIMBS)
          .map(|l| {
            AllocatedNum::alloc(cs.namespace(|| format!("X{i}_{l}")), || {
              Ok(v.as_ref().map_or(E::Base::ZERO, |v| v[l]))
            })
          })
          .collect::<Result<Vec<_>, _>>()
      })
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self { w, e, u, x })
  }

  /// The default instance (W = E = identity, u = 0, X = 0), all constants.
  pub fn default<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    n: usize,
  ) -> Result<Self, SynthesisError> {
    let w = AllocatedPoint::default(cs.namespace(|| "W"))?;
    let e = AllocatedPoint::default(cs.namespace(|| "E"))?;
    let u = alloc_constant(cs.namespace(|| "u"), E::Base::ZERO)?;
    let x = (0..n)
      .map(|i| {
        (0..BN_N_LIMBS)
          .map(|l| alloc_constant(cs.namespace(|| format!("X{i}_{l}")), E::Base::ZERO))
          .collect::<Result<Vec<_>, _>>()
      })
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self { w, e, u, x })
  }

  /// Absorbs `W, E, u, X` (limbs) in the order of `RelaxedR1CSInstance::absorb_in_ro`.
  pub(crate) fn absorb<RO: ROCircuitTrait<E::Base>>(&self, ro: &mut RO) {
    for p in [&self.w, &self.e] {
      ro.absorb(&p.x);
      ro.absorb(&p.y);
      ro.absorb(&p.is_infinity);
    }
    ro.absorb(&self.u);
    self.x.iter().flatten().for_each(|l| ro.absorb(l));
  }

  /// Folds a fresh (u = 1, E = 0) instance `(comm_w, x)` with cross term `t`:
  /// `r = H(TAG_CF_FOLD, params, self, comm_w, x, t)`, `W ← W + r·comm_w`, `E ← E + r·t`,
  /// `u ← u + r`, `X_i ← X_i + r·x_i mod |E::Scalar|`. The limbs of `x` must be in range
  /// (64 bits each); the caller guarantees it.
  pub fn fold_with_r1cs<CS: ConstraintSystem<E::Base>>(
    &self,
    mut cs: CS,
    params: &AllocatedNum<E::Base>,
    comm_w: &AllocatedPoint<E>,
    x: &[BigNat<E::Base>],
    t: &AllocatedPoint<E>,
    ro_consts: ROConstantsCircuit<E>,
  ) -> Result<Self, SynthesisError> {
    assert_eq!(x.len(), self.x.len());
    let mut ro = E::ROCircuit::new(ro_consts);
    let tag = alloc_constant(cs.namespace(|| "tag"), E::Base::from(TAG_CF_FOLD))?;
    ro.absorb(&tag);
    ro.absorb(params);
    self.absorb(&mut ro);
    ro.absorb(&comm_w.x);
    ro.absorb(&comm_w.y);
    ro.absorb(&comm_w.is_infinity);
    for (i, xi) in x.iter().enumerate() {
      for l in bignat_limb_nums(cs.namespace(|| format!("x{i} limbs")), xi)? {
        ro.absorb(&l);
      }
    }
    ro.absorb(&t.x);
    ro.absorb(&t.y);
    ro.absorb(&t.is_infinity);
    let (r, r_bits) = squeeze_challenge(cs.namespace(|| "r"), &mut ro)?;

    let rw = comm_w.scalar_mul(cs.namespace(|| "r * comm_w"), &r_bits)?;
    let w = self.w.add(cs.namespace(|| "W + r comm_w"), &rw)?;
    let rt = t.scalar_mul(cs.namespace(|| "r * T"), &r_bits)?;
    let e = self.e.add(cs.namespace(|| "E + r T"), &rt)?;
    let u = Expr::num(&self.u)
      .add(&Expr::num(&r))
      .alloc(cs.namespace(|| "u + r"))?;

    let r_bn = bignat_of_bits::<E::Base>(&r_bits);
    let m_bn = alloc_bignat_constant(
      cs.namespace(|| "modulus"),
      &E::GE::group_params().2,
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;
    let mut x_new = Vec::with_capacity(x.len());
    for (i, (xi, run)) in x.iter().zip(&self.x).enumerate() {
      let (_, prod) = xi.mult_mod(cs.namespace(|| format!("r x{i}")), &r_bn, &m_bn)?;
      let sum = bignat_of_limbs(run).add(&prod)?;
      let red = sum.red_mod(cs.namespace(|| format!("reduce x{i}")), &m_bn)?;
      x_new.push(bignat_limb_nums(
        cs.namespace(|| format!("x{i} out")),
        &red,
      )?);
    }
    Ok(Self { w, e, u, x: x_new })
  }

  /// `cond ? a : b`.
  pub fn select<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    a: &Self,
    b: &Self,
    cond: &Boolean,
  ) -> Result<Self, SynthesisError> {
    let w = AllocatedPoint::conditionally_select(cs.namespace(|| "W"), &a.w, &b.w, cond)?;
    let e = AllocatedPoint::conditionally_select(cs.namespace(|| "E"), &a.e, &b.e, cond)?;
    let u = conditionally_select(cs.namespace(|| "u"), &a.u, &b.u, cond)?;
    let x = a
      .x
      .iter()
      .zip(&b.x)
      .enumerate()
      .map(|(i, (p, q))| {
        p.iter()
          .zip(q)
          .enumerate()
          .map(|(l, (s, t))| conditionally_select(cs.namespace(|| format!("X{i}_{l}")), s, t, cond))
          .collect::<Result<Vec<_>, _>>()
      })
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self { w, e, u, x })
  }
}

/// Running ACCS instance in the circuit (μ = 1). The index is the Direct `comm_M[0..t]` as
/// non-native points, or the Span λ.
#[derive(Clone)]
pub(crate) struct AllocRunning<F: PrimeField> {
  pub(crate) comm_w: NnPoint<F>,
  pub(crate) index: AllocIndex<F>,
  pub(crate) u: AllocatedNum<F>,
  pub(crate) io: Vec<AllocatedNum<F>>,
  pub(crate) r_x: Vec<AllocatedNum<F>>,
  pub(crate) r_y: Vec<AllocatedNum<F>>,
  pub(crate) v: Vec<AllocatedNum<F>>,
}

/// The running index in the circuit.
#[derive(Clone)]
pub(crate) enum AllocIndex<F: PrimeField> {
  Direct(Vec<NnPoint<F>>),
  Span(Vec<AllocatedNum<F>>),
}

impl<F: PrimeField + PrimeFieldBits> AllocRunning<F> {
  /// Absorbs in the order of `hfs::nifs::absorb_inputs` (one running instance).
  pub(crate) fn absorb<RO: ROCircuitTrait<F>>(&self, ro: &mut RO) {
    self.comm_w.absorb(ro);
    match &self.index {
      AllocIndex::Direct(m) => m.iter().for_each(|p| p.absorb(ro)),
      AllocIndex::Span(l) => l.iter().for_each(|x| ro.absorb(x)),
    }
    ro.absorb(&self.u);
    for x in self
      .io
      .iter()
      .chain(&self.r_x)
      .chain(&self.r_y)
      .chain(&self.v)
    {
      ro.absorb(x);
    }
  }

  /// `cond ? a : b`.
  pub(crate) fn select<CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &Self,
    b: &Self,
    cond: &Boolean,
  ) -> Result<Self, SynthesisError> {
    let comm_w = NnPoint::select(cs.namespace(|| "comm_w"), &a.comm_w, &b.comm_w, cond)?;
    let index = match (&a.index, &b.index) {
      (AllocIndex::Direct(p), AllocIndex::Direct(q)) => AllocIndex::Direct(
        p.iter()
          .zip(q)
          .enumerate()
          .map(|(j, (p, q))| NnPoint::select(cs.namespace(|| format!("M{j}")), p, q, cond))
          .collect::<Result<_, _>>()?,
      ),
      (AllocIndex::Span(p), AllocIndex::Span(q)) => {
        AllocIndex::Span(select_vec(cs.namespace(|| "lambda"), p, q, cond)?)
      }
      _ => return Err(SynthesisError::Unsatisfiable),
    };
    Ok(Self {
      comm_w,
      index,
      u: conditionally_select(cs.namespace(|| "u"), &a.u, &b.u, cond)?,
      io: select_vec(cs.namespace(|| "io"), &a.io, &b.io, cond)?,
      r_x: select_vec(cs.namespace(|| "r_x"), &a.r_x, &b.r_x, cond)?,
      r_y: select_vec(cs.namespace(|| "r_y"), &a.r_y, &b.r_y, cond)?,
      v: select_vec(cs.namespace(|| "v"), &a.v, &b.v, cond)?,
    })
  }
}

pub(crate) fn select_vec<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &[AllocatedNum<F>],
  b: &[AllocatedNum<F>],
  cond: &Boolean,
) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
  a.iter()
    .zip(b)
    .enumerate()
    .map(|(i, (p, q))| conditionally_select(cs.namespace(|| format!("{i}")), p, q, cond))
    .collect()
}

/// Allocates `n` values (`None` → zeros in shape mode is irrelevant; values are only read when
/// synthesizing a witness).
pub(crate) fn alloc_vec<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  vals: Option<&[F]>,
  n: usize,
) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
  (0..n)
    .map(|i| {
      AllocatedNum::alloc(cs.namespace(|| format!("{i}")), || {
        Ok(vals.map_or(F::ZERO, |v| v[i]))
      })
    })
    .collect()
}

/// Incoming CCCS instance in the circuit: predicate id (with its one-hot), comm_W, io.
pub(crate) struct AllocIncoming<F: PrimeField> {
  pub(crate) k: AllocatedNum<F>,
  pub(crate) k_bits: Vec<AllocatedBit>,
  pub(crate) comm_w: NnPoint<F>,
  pub(crate) io: Vec<AllocatedNum<F>>,
}

/// HFS v2 proof in the circuit (μ = ν = 1).
pub(crate) struct AllocProof<F: PrimeField> {
  pub(crate) sc_x: Vec<Vec<AllocatedNum<F>>>,
  pub(crate) sigma: Vec<AllocatedNum<F>>,
  pub(crate) tau: Vec<AllocatedNum<F>>,
  pub(crate) sc_y: Vec<Vec<AllocatedNum<F>>>,
  pub(crate) eps: Vec<AllocatedNum<F>>,
  pub(crate) theta: Vec<AllocatedNum<F>>,
}

/// Static data the HFS gadget needs (all public parameters).
pub(crate) struct HfsGadgetParams<'a, F: PrimeField, B: PrimeField> {
  pub(crate) template: &'a CcsTemplate<F>,
  pub(crate) tag_input: u64,
  pub(crate) s: usize,
  /// ι_k[j] coordinates (Direct); empty for Span.
  pub(crate) iota: &'a [Vec<(B, B, bool)>],
}

/// Outputs of the HFS gadget (the challenges are read by the native-vs-gadget tests).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) struct HfsGadgetOut<F: PrimeField> {
  pub(crate) gamma: AllocatedNum<F>,
  pub(crate) alpha: Vec<AllocatedNum<F>>,
  pub(crate) r_x: Vec<AllocatedNum<F>>,
  pub(crate) delta: AllocatedNum<F>,
  pub(crate) r_y: Vec<AllocatedNum<F>>,
  pub(crate) rho: AllocatedNum<F>,
  pub(crate) rho_bits: Vec<AllocatedBit>,
  /// Folded scalar parts: u, io, v, and λ (Span).
  pub(crate) u: AllocatedNum<F>,
  pub(crate) io: Vec<AllocatedNum<F>>,
  pub(crate) v: Vec<AllocatedNum<F>>,
  pub(crate) lambda: Option<Vec<AllocatedNum<F>>>,
}

fn sum_exprs<F: PrimeField>(xs: impl IntoIterator<Item = Expr<F>>) -> Expr<F> {
  xs.into_iter().fold(Expr::zero(), |a, x| a.add(&x))
}

/// The HFS v2 verifier for one running and one incoming instance, in an `E::Scalar` circuit,
/// with transcript `E::RO2Circuit`. Mirrors `hfs::NIFS::verify_with_tags` step for step. Every
/// equality is enforced only when `active = 1` (`active = 1 − is_base`).
pub(crate) fn verify_hfs<E: Engine, CS: ConstraintSystem<E::Scalar>>(
  mut cs: CS,
  p: &HfsGadgetParams<'_, E::Scalar, E::Base>,
  ro_consts: crate::traits::RO2ConstantsCircuit<E>,
  digest: &AllocatedNum<E::Scalar>,
  run: &AllocRunning<E::Scalar>,
  inc: &AllocIncoming<E::Scalar>,
  pf: &AllocProof<E::Scalar>,
  active: &Expr<E::Scalar>,
) -> Result<HfsGadgetOut<E::Scalar>, SynthesisError> {
  type F<E> = <E as Engine>::Scalar;
  let tpl = p.template;
  let t = tpl.t();
  let mut ro = E::RO2Circuit::new(ro_consts);

  // Statement.
  let tag = alloc_constant(cs.namespace(|| "tag input"), F::<E>::from(p.tag_input))?;
  ro.absorb(&tag);
  ro.absorb(digest);
  let one = alloc_constant(cs.namespace(|| "mu"), F::<E>::ONE)?;
  ro.absorb(&one); // μ = 1
  ro.absorb(&one); // ν = 1
  run.absorb(&mut ro);
  ro.absorb(&inc.k);
  inc.comm_w.absorb(&mut ro);
  inc.io.iter().for_each(|x| ro.absorb(x));
  if let AllocIndex::Direct(_) = run.index {
    for j in 0..t {
      let pts: Vec<(E::Base, E::Base, bool)> = p.iota.iter().map(|io| io[j]).collect();
      NnPoint::select_constant(cs.namespace(|| format!("iota{j}")), &pts, &inc.k_bits)?
        .absorb(&mut ro);
    }
  }
  let (gamma, _) = squeeze_challenge(cs.namespace(|| "gamma"), &mut ro)?;
  let alpha = (0..p.s)
    .map(|i| squeeze_challenge(cs.namespace(|| format!("alpha{i}")), &mut ro).map(|x| x.0))
    .collect::<Result<Vec<_>, _>>()?;
  let gp = powers(cs.namespace(|| "gamma powers"), &gamma, t + 1)?;

  // X phase.
  let claim_x = sum_exprs(weighted(cs.namespace(|| "g v"), &gp[..t], &run.v[..t])?);
  let (fx, r_x) = sumcheck(cs.namespace(|| "sc_x"), &mut ro, claim_x, &pf.sc_x, active)?;
  let eq_alpha = eq_eval(cs.namespace(|| "eq alpha"), &alpha, &r_x)?;
  let eq_rx = eq_eval(cs.namespace(|| "eq r_x"), &run.r_x, &r_x)?;
  let gsig = weighted(cs.namespace(|| "g sigma"), &gp[..t], &pf.sigma)?;
  let s_run = Expr::num(&eq_rx.mul(cs.namespace(|| "eq * sigma"), &sum_exprs(gsig))?);
  let comb = combine(cs.namespace(|| "combine tau"), tpl, &pf.tau)?;
  let ea = Expr::num(&eq_alpha.mul(cs.namespace(|| "eq_alpha g^t"), &gp[t])?);
  let s_inc = Expr::num(&ea.mul(cs.namespace(|| "zero-check term"), &comb)?);
  enforce_zero_if(
    cs.namespace(|| "X end check"),
    &s_run.add(&s_inc).sub(&fx),
    active,
  );
  let tx = alloc_constant(cs.namespace(|| "tag x"), F::<E>::from(TAG_X_CLAIMS))?;
  ro.absorb(&tx);
  pf.sigma.iter().chain(&pf.tau).for_each(|x| ro.absorb(x));
  let (delta, _) = squeeze_challenge(cs.namespace(|| "delta"), &mut ro)?;
  let dp = powers(cs.namespace(|| "delta powers"), &delta, 2 * t + 1)?;

  // Y phase.
  let mut cy = weighted(cs.namespace(|| "d sigma"), &dp[..t], &pf.sigma)?;
  cy.extend(weighted(cs.namespace(|| "d tau"), &dp[t + 1..], &pf.tau)?);
  cy.push(Expr::num(
    &dp[t].mul(cs.namespace(|| "d v_t"), &Expr::num(&run.v[t]))?,
  ));
  let claim_y = sum_exprs(cy);
  let (fy, r_y) = sumcheck(cs.namespace(|| "sc_y"), &mut ro, claim_y, &pf.sc_y, active)?;
  let eq_ry = eq_eval(cs.namespace(|| "eq r_y"), &run.r_y, &r_y)?;
  let de = weighted(cs.namespace(|| "d eps"), &dp[..=t], &pf.eps)?;
  let e_run = Expr::num(&eq_ry.mul(cs.namespace(|| "eq * eps"), &sum_exprs(de))?);
  let mut e_inc = Vec::new();
  for j in 0..t {
    let dt = Expr::num(&dp[t + 1 + j].mul(
      cs.namespace(|| format!("d theta{j}")),
      &Expr::num(&pf.theta[j]),
    )?);
    e_inc.push(Expr::num(&dt.mul(
      cs.namespace(|| format!("d theta{j} z")),
      &Expr::num(&pf.theta[t]),
    )?));
  }
  enforce_zero_if(
    cs.namespace(|| "Y end check"),
    &e_run.add(&sum_exprs(e_inc)).sub(&fy),
    active,
  );
  let ty = alloc_constant(cs.namespace(|| "tag y"), F::<E>::from(TAG_Y_CLAIMS))?;
  ro.absorb(&ty);
  pf.eps.iter().chain(&pf.theta).for_each(|x| ro.absorb(x));
  let (rho, rho_bits) = squeeze_challenge(cs.namespace(|| "rho"), &mut ro)?;

  // Fold of the scalar parts (weights 1, ρ).
  let rho_e = Expr::num(&rho);
  let u = Expr::num(&run.u)
    .add(&rho_e)
    .alloc(cs.namespace(|| "u fold"))?;
  let fold = |cs: &mut CS, name: &str, a: &[AllocatedNum<F<E>>], b: &[AllocatedNum<F<E>>]| {
    a.iter()
      .zip(b)
      .enumerate()
      .map(|(i, (a, b))| {
        let rb = rho_e.mul(cs.namespace(|| format!("{name}{i} r")), &Expr::num(b))?;
        Expr::num(a)
          .add(&Expr::num(&rb))
          .alloc(cs.namespace(|| format!("{name}{i}")))
      })
      .collect::<Result<Vec<_>, SynthesisError>>()
  };
  let io = fold(&mut cs, "io", &run.io, &inc.io)?;
  let v = fold(&mut cs, "v", &pf.eps, &pf.theta)?;
  let lambda = match &run.index {
    AllocIndex::Span(l) => Some(
      l.iter()
        .zip(&inc.k_bits)
        .enumerate()
        .map(|(i, (l, b))| {
          let rb = rho_e.mul(cs.namespace(|| format!("lambda{i} r")), &Expr::bit(b))?;
          Expr::num(l)
            .add(&Expr::num(&rb))
            .alloc(cs.namespace(|| format!("lambda{i}")))
        })
        .collect::<Result<Vec<_>, SynthesisError>>()?,
    ),
    AllocIndex::Direct(_) => None,
  };
  Ok(HfsGadgetOut {
    gamma,
    alpha,
    r_x,
    delta,
    r_y,
    rho,
    rho_bits,
    u,
    io,
    v,
    lambda,
  })
}

/// `w_j · x_j` for each j (one constraint each).
fn weighted<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  w: &[Expr<F>],
  x: &[AllocatedNum<F>],
) -> Result<Vec<Expr<F>>, SynthesisError> {
  w.iter()
    .zip(x)
    .enumerate()
    .map(|(j, (w, x))| {
      w.mul(cs.namespace(|| format!("{j}")), &Expr::num(x))
        .map(|p| Expr::num(&p))
    })
    .collect()
}

/// `Σ_k c_k Π_{j ∈ S_k} vals[j]`.
fn combine<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  tpl: &CcsTemplate<F>,
  vals: &[AllocatedNum<F>],
) -> Result<Expr<F>, SynthesisError> {
  let mut acc = Expr::zero();
  for (k, (ms, c)) in tpl.multisets().iter().zip(tpl.coeffs()).enumerate() {
    let mut prod = Expr::num(&vals[ms[0]]);
    for (i, &j) in ms.iter().enumerate().skip(1) {
      prod = Expr::num(&prod.mul(
        cs.namespace(|| format!("term{k} factor{i}")),
        &Expr::num(&vals[j]),
      )?);
    }
    acc = acc.add(&prod.scale(*c));
  }
  Ok(acc)
}

/// Sum-check verifier: round i checks `p(0) + p(1) = claim` (gated), absorbs the evaluations,
/// squeezes `r_i` and sets `claim = p(r_i)`. Returns the final claim and the point.
fn sumcheck<F, RO, CS>(
  mut cs: CS,
  ro: &mut RO,
  claim: Expr<F>,
  msgs: &[Vec<AllocatedNum<F>>],
  active: &Expr<F>,
) -> Result<(Expr<F>, Vec<AllocatedNum<F>>), SynthesisError>
where
  F: PrimeField + PrimeFieldBits,
  RO: ROCircuitTrait<F>,
  CS: ConstraintSystem<F>,
{
  let mut claim = claim;
  let mut point = Vec::with_capacity(msgs.len());
  for (round, m) in msgs.iter().enumerate() {
    let mut cs = cs.namespace(|| format!("round {round}"));
    enforce_zero_if(
      cs.namespace(|| "p(0) + p(1) = claim"),
      &Expr::num(&m[0]).add(&Expr::num(&m[1])).sub(&claim),
      active,
    );
    m.iter().for_each(|e| ro.absorb(e));
    let (r, _) = squeeze_challenge(cs.namespace(|| "r"), ro)?;
    claim = Expr::num(&interpolate(cs.namespace(|| "p(r)"), m, &r)?);
    point.push(r);
  }
  Ok((claim, point))
}

/// The CycleFold public inputs as bignats, in the order of `cyclefold::CycleFoldCircuit`:
/// `ρ, [k], W_run, W_inc, W_out, (M_run[j], M_out[j])_j`.
pub(crate) fn cyclefold_inputs<F: PrimeField + PrimeFieldBits>(
  rho_bits: &[AllocatedBit],
  k_bits: Option<&[AllocatedBit]>,
  w: [&NnPoint<F>; 3],
  m: &[(NnPoint<F>, NnPoint<F>)],
) -> Vec<BigNat<F>> {
  let mut out = vec![bignat_of_bits(rho_bits)];
  if let Some(kb) = k_bits {
    // k = Σ i·b_i < 2^64: a single limb that is a linear combination of booleans.
    let mut lc = LinearCombination::zero();
    let mut val = Some(F::ZERO);
    for (i, b) in kb.iter().enumerate() {
      lc = lc + (F::from(i as u64), b.get_variable());
      val = val
        .zip(b.get_value())
        .map(|(v, bit)| if bit { v + F::from(i as u64) } else { v });
    }
    let mut limbs = vec![lc];
    limbs.extend((1..BN_N_LIMBS).map(|_| LinearCombination::zero()));
    let limb_values = val.map(|v| {
      let mut vs = vec![v];
      vs.extend((1..BN_N_LIMBS).map(|_| F::ZERO));
      vs
    });
    out.push(BigNat {
      value: val.map(|v| f_to_nat(&v)),
      limb_values,
      limbs,
      params: BigNatParams::new(BN_LIMB_WIDTH, BN_N_LIMBS),
    });
  }
  for p in w {
    let (x, y) = p.coords_bignat();
    out.push(x);
    out.push(y);
  }
  for (run, outp) in m {
    for p in [run, outp] {
      let (x, y) = p.coords_bignat();
      out.push(x);
      out.push(y);
    }
  }
  out
}
