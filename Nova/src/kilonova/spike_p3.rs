//! P3.0 decision spike (D1): in-circuit cost of the building blocks of option (a),
//! "Nova fork + CycleFold". Test-only; the numbers feed `docs/P3.0-decision.md`.
//!
//! Option (a) runs the HFS for E1-instances inside the E1-scalar circuit (native sum-check, which
//! fixes B15). Its group operations on E1 points (coordinates in E1::Base, non-native there) are
//! delegated to a small CycleFold circuit over E2::Scalar = E1::Base, where they are native. The
//! primary circuit then folds the CycleFold instance with plain Nova NIFS, whose group operations
//! are on E2 points (coordinates in E2::Base = E1::Scalar, native) and whose public-input fold is
//! non-native (bignat).
//!
//! Engines: E1 = Pallas, E2 = Vesta. Primary circuit field = Pallas::Scalar = Vesta::Base.
use super::CountingCS;
use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_CHALLENGE_BITS},
  frontend::{gadgets::boolean::AllocatedBit, num::AllocatedNum, ConstraintSystem, SynthesisError},
  gadgets::{
    ecc::AllocatedPoint,
    nonnative::{bignat::BigNat, util::Num},
    utils::alloc_bignat_constant,
  },
  nova::circuit::r1cs::{AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance},
  provider::{PallasEngine, VestaEngine},
  traits::{Engine, Group, ROCircuitTrait, ROConstantsCircuit},
};
use ff::Field;

type Fp = <VestaEngine as Engine>::Base; // primary circuit field (= Pallas::Scalar)
type Fq = <PallasEngine as Engine>::Base; // CycleFold circuit field (= Vesta::Scalar)

fn count<F: ff::PrimeField>(
  f: impl FnOnce(&mut CountingCS<F>) -> Result<(), SynthesisError>,
) -> (usize, usize) {
  let mut cs = CountingCS::<F>::default();
  f(&mut cs).unwrap();
  (cs.num_constraints, cs.num_aux)
}

fn alloc_bits<F: ff::PrimeField, CS: ConstraintSystem<F>>(
  cs: &mut CS,
  n: usize,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
  (0..n)
    .map(|i| AllocatedBit::alloc(cs.namespace(|| format!("b{i}")), Some(i % 3 == 0)))
    .collect()
}

/// Cost of `f` alone: run `setup` and `setup + f`, return the difference.
fn delta<F: ff::PrimeField>(
  setup: impl Fn(&mut CountingCS<F>) -> Result<(), SynthesisError>,
  with_f: impl FnOnce(&mut CountingCS<F>) -> Result<(), SynthesisError>,
) -> usize {
  count(setup).0.abs_diff(count(with_f).0)
}

/// 128-bit scalar multiplication plus one addition of a point of curve `E`, inside a circuit over
/// `E::Base` (native coordinates).
fn ecc_costs<E: Engine>() -> (usize, usize) {
  let setup = |cs: &mut CountingCS<E::Base>| -> Result<(), SynthesisError> {
    AllocatedPoint::<E>::alloc(cs.namespace(|| "p"), None)?;
    AllocatedPoint::<E>::alloc(cs.namespace(|| "q"), None)?;
    alloc_bits(&mut cs.namespace(|| "bits"), NUM_CHALLENGE_BITS)?;
    Ok(())
  };
  let sm = delta(setup, |cs| {
    let p = AllocatedPoint::<E>::alloc(cs.namespace(|| "p"), None)?;
    AllocatedPoint::<E>::alloc(cs.namespace(|| "q"), None)?;
    let bits = alloc_bits(&mut cs.namespace(|| "bits"), NUM_CHALLENGE_BITS)?;
    p.scalar_mul(cs.namespace(|| "sm"), &bits)?;
    Ok(())
  });
  let add = delta(setup, |cs| {
    let p = AllocatedPoint::<E>::alloc(cs.namespace(|| "p"), None)?;
    let q = AllocatedPoint::<E>::alloc(cs.namespace(|| "q"), None)?;
    alloc_bits(&mut cs.namespace(|| "bits"), NUM_CHALLENGE_BITS)?;
    p.add(cs.namespace(|| "add"), &q)?;
    Ok(())
  });
  (sm, add)
}

/// Non-native arithmetic in the primary circuit (field Fp) on values of Fq = E1::Base, with the
/// limb parameters Nova uses (4 × 64).
fn bignat_costs() -> (usize, usize, usize) {
  let modulus = <VestaEngine as Engine>::GE::group_params().2;
  let setup = |cs: &mut CountingCS<Fp>| -> Result<(), SynthesisError> {
    let r = AllocatedNum::alloc(cs.namespace(|| "r"), || Ok(Fp::ONE))?;
    BigNat::from_num(
      cs.namespace(|| "r_bn"),
      &Num::from(r),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;
    alloc_bignat_constant(cs.namespace(|| "m"), &modulus, BN_LIMB_WIDTH, BN_N_LIMBS)?;
    BigNat::alloc_from_nat(
      cs.namespace(|| "acc"),
      || Ok(0u64.into()),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;
    Ok(())
  };
  // One public-input fold `acc + r·x mod m`, exactly as in `fold_with_r1cs`.
  let fold_one = delta(setup, |cs| {
    let r = AllocatedNum::alloc(cs.namespace(|| "r"), || Ok(Fp::ONE))?;
    let r_bn = BigNat::from_num(
      cs.namespace(|| "r_bn"),
      &Num::from(r),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;
    let m = alloc_bignat_constant(cs.namespace(|| "m"), &modulus, BN_LIMB_WIDTH, BN_N_LIMBS)?;
    let acc = BigNat::alloc_from_nat(
      cs.namespace(|| "acc"),
      || Ok(0u64.into()),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;
    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(Fp::ONE))?;
    let x_bn = BigNat::from_num(
      cs.namespace(|| "x_bn"),
      &Num::from(x),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;
    let (_, rx) = x_bn.mult_mod(cs.namespace(|| "r*x"), &r_bn, &m)?;
    acc.add(&rx)?.red_mod(cs.namespace(|| "red"), &m)?;
    Ok(())
  });
  // One non-native multiplication mod m (the unit cost of non-native sum-check arithmetic).
  let mult_mod = delta(setup, |cs| {
    let r = AllocatedNum::alloc(cs.namespace(|| "r"), || Ok(Fp::ONE))?;
    let r_bn = BigNat::from_num(
      cs.namespace(|| "r_bn"),
      &Num::from(r),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;
    let m = alloc_bignat_constant(cs.namespace(|| "m"), &modulus, BN_LIMB_WIDTH, BN_N_LIMBS)?;
    let acc = BigNat::alloc_from_nat(
      cs.namespace(|| "acc"),
      || Ok(0u64.into()),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;
    acc.mult_mod(cs.namespace(|| "acc*r"), &r_bn, &m)?;
    Ok(())
  });
  // Allocating one non-native field element as range-checked limbs (e.g. one coordinate of an
  // E1 point carried in the primary circuit).
  let alloc_fe = count(|cs: &mut CountingCS<Fp>| {
    BigNat::alloc_from_nat(
      cs.namespace(|| "c"),
      || Ok(0u64.into()),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;
    Ok(())
  })
  .0;
  (fold_one, mult_mod, alloc_fe)
}

/// Nova's in-circuit fold of a 2-input R1CS instance of curve E2 (Vesta) in the primary circuit.
fn nova_fold2_cost() -> usize {
  let setup = |cs: &mut CountingCS<Fp>| -> Result<(), SynthesisError> {
    AllocatedRelaxedR1CSInstance::<VestaEngine>::alloc(cs.namespace(|| "U"), None)?;
    AllocatedR1CSInstance::<VestaEngine>::alloc(cs.namespace(|| "u"), None)?;
    AllocatedPoint::<VestaEngine>::alloc(cs.namespace(|| "T"), None)?;
    AllocatedNum::alloc(cs.namespace(|| "params"), || Ok(Fp::ONE))?;
    Ok(())
  };
  delta(setup, |cs| {
    let big_u = AllocatedRelaxedR1CSInstance::<VestaEngine>::alloc(cs.namespace(|| "U"), None)?;
    let u = AllocatedR1CSInstance::<VestaEngine>::alloc(cs.namespace(|| "u"), None)?;
    let t = AllocatedPoint::<VestaEngine>::alloc(cs.namespace(|| "T"), None)?;
    let params = AllocatedNum::alloc(cs.namespace(|| "params"), || Ok(Fp::ONE))?;
    big_u.fold_with_r1cs(
      cs.namespace(|| "fold"),
      &params,
      &u,
      &t,
      ROConstantsCircuit::<VestaEngine>::default(),
    )?;
    Ok(())
  })
}

/// Poseidon squeeze cost as a function of the number of absorbed elements.
fn poseidon_cost(n: usize) -> usize {
  count(|cs: &mut CountingCS<Fp>| {
    let mut ro =
      <VestaEngine as Engine>::ROCircuit::new(ROConstantsCircuit::<VestaEngine>::default());
    for i in 0..n {
      let x = AllocatedNum::alloc(cs.namespace(|| format!("x{i}")), || Ok(Fp::ONE))?;
      ro.absorb(&x);
    }
    ro.squeeze(cs.namespace(|| "sq"), NUM_CHALLENGE_BITS)?;
    Ok(())
  })
  .0
}

/// Prints the measured unit costs and the composed per-step estimates used in the memo.
/// Run: `cargo test -p nova-snark --release --lib kilonova::spike_p3 -- --nocapture`
#[test]
fn p3_spike_unit_costs() {
  let (sm_p, add_p) = ecc_costs::<VestaEngine>(); // E2 points in the primary circuit (native)
  let (sm_cf, add_cf) = ecc_costs::<PallasEngine>(); // E1 points in the CycleFold circuit
  let (fold_one, mult_mod, _) = bignat_costs();
  let nova_fold2 = nova_fold2_cost();
  let (pos10, pos60) = (poseidon_cost(10), poseidon_cost(60));
  let _ = Fq::ONE;

  println!("[spike] ecc in primary (Vesta pts): scalar_mul128 = {sm_p}, add = {add_p}");
  println!(
    "[spike] ecc in CycleFold circuit (Pallas pts): scalar_mul128 = {sm_cf}, add = {add_cf}"
  );
  println!("[spike] bignat: fold one public input (range check + mult_mod + reduce) = {fold_one}, mult_mod = {mult_mod}");
  println!("[spike] Nova fold_with_r1cs (2 public inputs) = {nova_fold2}");
  println!("[spike] poseidon squeeze after 10 / 60 absorbs = {pos10} / {pos60}");

  // Composition (see docs/P3.0-decision.md §3 for the derivation).
  // CycleFold circuit for one HFS fold: 4 × (ρ·P + Q) on E1 points, ρ 128 bits.
  let cf_ops = 4 * (sm_cf + add_cf);
  // Public inputs of the batched CycleFold instance: ρ + 4 ops × 3 points × 2 coordinates.
  let cf_io = 1 + 4 * 3 * 2;
  // Primary-side fold of that instance: Nova's 2-input fold with the input part re-priced.
  let cf_fold = nova_fold2 - 2 * fold_one + cf_io * fold_one;
  // E1 points the primary must carry non-natively (2 coordinates each): U1.comm_W, U1.comm_M[3],
  // U2.comm_W, output comm_W, comm_M[3] (ι is a per-predicate constant). Their limbs are range
  // checked inside the CycleFold input fold above; the extra cost is hashing 4 limbs per
  // coordinate into the transcript and the link hash.
  let carried_points = 9;
  let carry = poseidon_cost(8 + carried_points * 2 * BN_N_LIMBS) - poseidon_cost(8);
  let removed = 4 * (sm_p + add_p);
  println!("[spike] option (a): CycleFold circuit ≈ {cf_ops} (+ IO/hash overhead)");
  println!(
    "[spike] option (a): primary delta = −{removed} (native ECC removed) + {cf_fold} (CycleFold fold, {cf_io} inputs) + {carry} (hashing carried E1 point limbs)"
  );
  // Option (a'): keep the two-curve layout and verify the sum-check non-natively.
  // Per fold ≈ 5 mult_mod per X round, 4 per Y round, 3 per eq factor in c_x / c_y, plus ~30
  // for claims and folds; s_max = s'_max = 17 at the measured P0 sizes.
  let (s, sp) = (17usize, 17usize);
  let nn_mults = 5 * s + 4 * sp + 3 * (s + sp) + 30;
  println!(
    "[spike] option (a'): non-native sum-check ≈ {nn_mults} mult_mod × {mult_mod} = {}",
    nn_mults * mult_mod
  );

  assert!(sm_p > 0 && sm_cf > 0 && fold_one > 0 && nova_fold2 > 2 * fold_one);
}

/// B15 resolution prototype: the HFS fold of `docs/protocol-spec.md` (two-phase sum-check,
/// committed index λ, fold `v* = ε + ρθ`), generalised to any CCS template and run over the
/// **native field** of the folded relation (E1::Scalar), with real Pedersen commitments on E1.
/// Every fold output is checked by the independent P2 oracle (`kn_ccs::accs::check_accs`) and the
/// index commitments are re-opened. The transcript is a Keccak toy (P3 uses Poseidon); sum-check
/// rounds bind the low bit first, so points are in kn-ccs order (not the reversed order of N9).
mod hfs_native {
  use crate::{
    provider::PallasEngine,
    traits::{commitment::CommitmentEngineTrait, commitment::CommitmentTrait, Engine},
    Commitment, CommitmentKey,
  };
  use ff::{Field, PrimeField};
  use kn_ccs::{
    accs::check_accs, mle::num_vars, AccsInstance, Assignment, Ccs, Family, NativeCcsBuilder,
    Template, Var,
  };
  use rand_chacha::ChaCha20Rng;
  use rand_core::SeedableRng;
  use sha3::{Digest, Keccak256};

  type E = PallasEngine;
  type F = <E as Engine>::Scalar;
  type C = Commitment<E>;

  const INDEX_LABELS: [&[u8]; 8] = [
    b"kn-idx-0",
    b"kn-idx-1",
    b"kn-idx-2",
    b"kn-idx-3",
    b"kn-idx-4",
    b"kn-idx-5",
    b"kn-idx-6",
    b"kn-idx-7",
  ];

  struct Tr([u8; 32]);
  impl Tr {
    fn new() -> Self {
      Tr(Keccak256::digest(b"KNHFS-native-prototype").into())
    }
    fn bytes(&mut self, b: &[u8]) {
      let mut h = Keccak256::new();
      h.update(self.0);
      h.update(b);
      self.0 = h.finalize().into();
    }
    fn fe(&mut self, f: &F) {
      self.bytes(f.to_repr().as_ref());
    }
    fn fes(&mut self, fs: &[F]) {
      fs.iter().for_each(|f| self.fe(f));
    }
    fn com(&mut self, c: &C) {
      let (x, y, inf) = c.to_coordinates();
      self.bytes(x.to_repr().as_ref());
      self.bytes(y.to_repr().as_ref());
      self.bytes(&[inf as u8]);
    }
    /// 128-bit challenge, like NUM_CHALLENGE_BITS.
    fn squeeze(&mut self) -> F {
      self.bytes(b"squeeze");
      F::from_u128(u128::from_le_bytes(self.0[..16].try_into().unwrap()))
    }
  }

  fn eq_table(p: &[F]) -> Vec<F> {
    let mut t = vec![F::ONE];
    for r in p {
      let n = t.len();
      let mut next = vec![F::ZERO; 2 * n];
      for (j, v) in t.iter().enumerate() {
        next[j] = *v * (F::ONE - r);
        next[j + n] = *v * r;
      }
      t = next;
    }
    t
  }

  fn eq_at(a: &[F], b: &[F]) -> F {
    a.iter().zip(b).fold(F::ONE, |acc, (x, y)| {
      acc * (*x * y + (F::ONE - x) * (F::ONE - y))
    })
  }

  fn powers(x: F, n: usize) -> Vec<F> {
    (0..n)
      .scan(F::ONE, |acc, _| {
        let v = *acc;
        *acc *= x;
        Some(v)
      })
      .collect()
  }

  fn padded(v: &[F], len: usize) -> Vec<F> {
    let mut v = v.to_vec();
    v.resize(len, F::ZERO);
    v
  }

  /// A term of a sum-check polynomial: coefficient × product of tables.
  type Term = (F, Vec<usize>);

  /// Proves Σ_x Σ_terms c·Π tables(x); returns round evaluations at 0..=deg, the point, and the
  /// fully bound table values.
  fn sc_prove(
    mut tables: Vec<Vec<F>>,
    terms: &[Term],
    deg: usize,
    tr: &mut Tr,
  ) -> (Vec<Vec<F>>, Vec<F>, Vec<F>) {
    let (mut polys, mut point) = (vec![], vec![]);
    while tables[0].len() > 1 {
      let half = tables[0].len() / 2;
      let evals: Vec<F> = (0..=deg as u64)
        .map(|t| {
          let t = F::from(t);
          (0..half).fold(F::ZERO, |acc, j| {
            acc
              + terms.iter().fold(F::ZERO, |s, (c, idx)| {
                s + idx.iter().fold(*c, |p, &k| {
                  let (a, b) = (tables[k][2 * j], tables[k][2 * j + 1]);
                  p * (a + (b - a) * t)
                })
              })
          })
        })
        .collect();
      tr.fes(&evals);
      let r = tr.squeeze();
      for tab in tables.iter_mut() {
        *tab = (0..half)
          .map(|j| tab[2 * j] + (tab[2 * j + 1] - tab[2 * j]) * r)
          .collect();
      }
      polys.push(evals);
      point.push(r);
    }
    (polys, point, tables.into_iter().map(|t| t[0]).collect())
  }

  fn interp(evals: &[F], r: F) -> F {
    let n = evals.len();
    (0..n).fold(F::ZERO, |acc, i| {
      let (num, den) = (0..n)
        .filter(|&j| j != i)
        .fold((F::ONE, F::ONE), |(nu, de), j| {
          (
            nu * (r - F::from(j as u64)),
            de * (F::from(i as u64) - F::from(j as u64)),
          )
        });
      acc + evals[i] * num * den.invert().unwrap()
    })
  }

  fn sc_verify(
    mut claim: F,
    polys: &[Vec<F>],
    rounds: usize,
    deg: usize,
    tr: &mut Tr,
  ) -> Result<(F, Vec<F>), String> {
    if polys.len() != rounds || polys.iter().any(|p| p.len() != deg + 1) {
      return Err("sum-check proof shape".into());
    }
    let mut point = vec![];
    for (i, p) in polys.iter().enumerate() {
      if p[0] + p[1] != claim {
        return Err(format!("sum-check round {i}: p(0)+p(1) != claim"));
      }
      tr.fes(p);
      let r = tr.squeeze();
      claim = interp(p, r);
      point.push(r);
    }
    Ok((claim, point))
  }

  #[derive(Clone, Debug, PartialEq)]
  pub struct Running {
    comm_w: C,
    comm_m: Vec<C>,
    u: F,
    io: Vec<F>,
    r_x: Vec<F>,
    r_y: Vec<F>,
    v: Vec<F>,
  }

  #[derive(Clone)]
  pub struct RunningW {
    w: Vec<F>,
    lambda: Vec<F>,
  }

  #[derive(Clone)]
  pub struct Proof {
    px: Vec<Vec<F>>,
    sigma: Vec<F>,
    tau: Vec<F>,
    py: Vec<Vec<F>>,
    eps: Vec<F>,
    theta: Vec<F>,
  }

  pub struct Keys {
    ck: CommitmentKey<E>,
    ck_index: Vec<CommitmentKey<E>>,
    /// ι_k[j] = Com(ck_index[j], e_k).
    iota: Vec<Vec<C>>,
  }

  impl Keys {
    fn new(family: &Family<F>) -> Self {
      let (k, t, num_w) = (family.k(), family.member(0).t(), family.member(0).num_w);
      let ck_index: Vec<_> = (0..t)
        .map(|j| <E as Engine>::CE::setup(INDEX_LABELS[j], k))
        .collect();
      let iota = (0..k)
        .map(|i| {
          let mut e = vec![F::ZERO; k];
          e[i] = F::ONE;
          ck_index
            .iter()
            .map(|ck| <E as Engine>::CE::commit(ck, &e, &F::ZERO))
            .collect()
        })
        .collect();
      Keys {
        ck: <E as Engine>::CE::setup(b"kn-ck", num_w.max(1)),
        ck_index,
        iota,
      }
    }
    fn commit_w(&self, w: &[F]) -> C {
      <E as Engine>::CE::commit(&self.ck, w, &F::ZERO)
    }
  }

  fn absorb_inputs(tr: &mut Tr, u1: &Running, k: usize, comm_w2: &C, io2: &[F], keys: &Keys) {
    tr.bytes(b"inputs");
    tr.com(&u1.comm_w);
    u1.comm_m.iter().for_each(|c| tr.com(c));
    tr.fe(&u1.u);
    tr.fes(&u1.io);
    tr.fes(&u1.r_x);
    tr.fes(&u1.r_y);
    tr.fes(&u1.v);
    tr.com(comm_w2);
    tr.fes(io2);
    tr.fe(&F::from(k as u64));
    keys.iota[k].iter().for_each(|c| tr.com(c));
  }

  /// Row table of Σ_i λ_i M_{i,j}(·, col) weighted by `col_eq[col]`, and the column table
  /// weighted by `row_eq[row]`.
  fn row_table(fam: &Family<F>, lambda: &[F], j: usize, col_eq: &[F], len: usize) -> Vec<F> {
    let mut t = vec![F::ZERO; len];
    for (i, l) in lambda.iter().enumerate() {
      for &(r, c, v) in fam.member(i).matrices[j].entries() {
        t[r] += *l * v * col_eq[c];
      }
    }
    t
  }
  fn col_table(fam: &Family<F>, lambda: &[F], j: usize, row_eq: &[F], len: usize) -> Vec<F> {
    let mut t = vec![F::ZERO; len];
    for (i, l) in lambda.iter().enumerate() {
      for &(r, c, v) in fam.member(i).matrices[j].entries() {
        t[c] += *l * v * row_eq[r];
      }
    }
    t
  }

  fn e_k(k: usize, n: usize) -> Vec<F> {
    let mut e = vec![F::ZERO; n];
    e[k] = F::ONE;
    e
  }

  /// Native HFS prover: folds running (U1, W1) with a fresh CCCS of predicate k.
  pub fn prove(
    fam: &Family<F>,
    keys: &Keys,
    u1: &Running,
    w1: &RunningW,
    k: usize,
    a2: &Assignment<F>,
  ) -> (Proof, Running, RunningW) {
    let c0 = fam.member(0);
    let (t, s, sp) = (c0.t(), num_vars(c0.m), num_vars(c0.n()));
    let tpl = &c0.template;
    let comm_w2 = keys.commit_w(&a2.w);
    let mut tr = Tr::new();
    absorb_inputs(&mut tr, u1, k, &comm_w2, &a2.io, keys);
    let gamma = tr.squeeze();
    let alpha: Vec<F> = (0..s).map(|_| tr.squeeze()).collect();
    let gp = powers(gamma, t + 1);

    // X phase over rows.
    let z1 = c0.z(&w1.w, u1.u, &u1.io).unwrap();
    let z2 = a2.z();
    let eq_ry1 = eq_table(&u1.r_y);
    let mut tables = vec![eq_table(&u1.r_x), eq_table(&alpha)];
    for j in 0..t {
      tables.push(row_table(fam, &w1.lambda, j, &eq_ry1, 1 << s));
    }
    for j in 0..t {
      tables.push(padded(
        &fam.member(k).matrices[j].mul_vec(&z2).unwrap(),
        1 << s,
      ));
    }
    let mut terms: Vec<Term> = (0..t).map(|j| (gp[j], vec![0, 2 + j])).collect();
    for (ms, c) in tpl.multisets.iter().zip(&tpl.coeffs) {
      let mut idx = vec![1];
      idx.extend(ms.iter().map(|j| 2 + t + j));
      terms.push((gp[t] * c, idx));
    }
    let (px, r_xp, finals) = sc_prove(tables, &terms, tpl.degree() + 1, &mut tr);
    let sigma = finals[2..2 + t].to_vec();
    let tau = finals[2 + t..2 + 2 * t].to_vec();
    tr.bytes(b"x-claims");
    tr.fes(&sigma);
    tr.fes(&tau);
    let delta = tr.squeeze();
    let dp = powers(delta, 2 * t + 1);

    // Y phase over columns.
    let eq_rx = eq_table(&r_xp);
    let mut tables = vec![eq_ry1.clone(), padded(&z1, 1 << sp), padded(&z2, 1 << sp)];
    for j in 0..t {
      tables.push(col_table(fam, &w1.lambda, j, &eq_rx, 1 << sp));
    }
    for j in 0..t {
      tables.push(col_table(fam, &e_k(k, fam.k()), j, &eq_rx, 1 << sp));
    }
    let mut terms: Vec<Term> = (0..t).map(|j| (dp[j], vec![0, 3 + j])).collect();
    terms.push((dp[t], vec![0, 1]));
    terms.extend((0..t).map(|j| (dp[t + 1 + j], vec![3 + t + j, 2])));
    let (py, r_yp, finals) = sc_prove(tables, &terms, 2, &mut tr);
    let mut eps = finals[3..3 + t].to_vec();
    eps.push(finals[1]);
    let mut theta = finals[3 + t..3 + 2 * t].to_vec();
    theta.push(finals[2]);
    tr.bytes(b"y-claims");
    tr.fes(&eps);
    tr.fes(&theta);
    let rho = tr.squeeze();

    let proof = Proof {
      px,
      sigma,
      tau,
      py,
      eps,
      theta,
    };
    let out = fold_instance(u1, k, &comm_w2, &a2.io, keys, &proof, r_xp, r_yp, rho);
    let w = w1.w.iter().zip(&a2.w).map(|(a, b)| *a + rho * b).collect();
    let lambda = w1
      .lambda
      .iter()
      .zip(e_k(k, fam.k()))
      .map(|(a, b)| *a + rho * b)
      .collect();
    (proof, out, RunningW { w, lambda })
  }

  #[allow(clippy::too_many_arguments)]
  fn fold_instance(
    u1: &Running,
    k: usize,
    comm_w2: &C,
    io2: &[F],
    keys: &Keys,
    p: &Proof,
    r_x: Vec<F>,
    r_y: Vec<F>,
    rho: F,
  ) -> Running {
    Running {
      comm_w: u1.comm_w + *comm_w2 * rho,
      comm_m: u1
        .comm_m
        .iter()
        .zip(&keys.iota[k])
        .map(|(a, b)| *a + *b * rho)
        .collect(),
      u: u1.u + rho,
      io: u1.io.iter().zip(io2).map(|(a, b)| *a + rho * b).collect(),
      r_x,
      r_y,
      v: p
        .eps
        .iter()
        .zip(&p.theta)
        .map(|(e, th)| *e + rho * th)
        .collect(),
    }
  }

  /// Native HFS verifier: succinct (no witness), returns the folded instance.
  pub fn verify(
    fam: &Family<F>,
    keys: &Keys,
    u1: &Running,
    k: usize,
    comm_w2: &C,
    io2: &[F],
    p: &Proof,
  ) -> Result<Running, String> {
    let c0 = fam.member(0);
    let (t, s, sp) = (c0.t(), num_vars(c0.m), num_vars(c0.n()));
    let tpl = &c0.template;
    if p.sigma.len() != t || p.tau.len() != t || p.eps.len() != t + 1 || p.theta.len() != t + 1 {
      return Err("claim lengths".into());
    }
    let mut tr = Tr::new();
    absorb_inputs(&mut tr, u1, k, comm_w2, io2, keys);
    let gamma = tr.squeeze();
    let alpha: Vec<F> = (0..s).map(|_| tr.squeeze()).collect();
    let gp = powers(gamma, t + 1);
    let claim_x = (0..t).fold(F::ZERO, |acc, j| acc + gp[j] * u1.v[j]);
    let (cx_claim, r_xp) = sc_verify(claim_x, &p.px, s, tpl.degree() + 1, &mut tr)?;
    let zero_check = tpl
      .multisets
      .iter()
      .zip(&tpl.coeffs)
      .fold(F::ZERO, |acc, (ms, c)| {
        acc + ms.iter().fold(*c, |pr, &j| pr * p.tau[j])
      });
    let cx = eq_at(&u1.r_x, &r_xp) * (0..t).fold(F::ZERO, |a, j| a + gp[j] * p.sigma[j])
      + gp[t] * eq_at(&alpha, &r_xp) * zero_check;
    if cx != cx_claim {
      return Err("X end check c_x".into());
    }
    tr.bytes(b"x-claims");
    tr.fes(&p.sigma);
    tr.fes(&p.tau);
    let delta = tr.squeeze();
    let dp = powers(delta, 2 * t + 1);
    let claim_y = (0..t).fold(F::ZERO, |a, j| a + dp[j] * p.sigma[j])
      + dp[t] * u1.v[t]
      + (0..t).fold(F::ZERO, |a, j| a + dp[t + 1 + j] * p.tau[j]);
    let (cy_claim, r_yp) = sc_verify(claim_y, &p.py, sp, 2, &mut tr)?;
    let cy = eq_at(&u1.r_y, &r_yp)
      * ((0..t).fold(F::ZERO, |a, j| a + dp[j] * p.eps[j]) + dp[t] * p.eps[t])
      + (0..t).fold(F::ZERO, |a, j| a + dp[t + 1 + j] * p.theta[j] * p.theta[t]);
    if cy != cy_claim {
      return Err("Y end check c_y".into());
    }
    tr.bytes(b"y-claims");
    tr.fes(&p.eps);
    tr.fes(&p.theta);
    let rho = tr.squeeze();
    Ok(fold_instance(u1, k, comm_w2, io2, keys, p, r_xp, r_yp, rho))
  }

  /// Independent decider: the P2 oracle on (U, W) plus the opening of the index commitments.
  fn decide(fam: &Family<F>, keys: &Keys, u: &Running, w: &RunningW) -> Result<(), String> {
    let accs = AccsInstance {
      comm_w: u.comm_w,
      u: u.u,
      io: u.io.clone(),
      lambda: w.lambda.clone(),
      r_x: u.r_x.clone(),
      r_y: u.r_y.clone(),
      v: u.v.clone(),
    };
    check_accs(fam, &accs, &w.w, |x| keys.commit_w(x)).map_err(|e| e.to_string())?;
    for (j, ck) in keys.ck_index.iter().enumerate() {
      if u.comm_m[j] != <E as Engine>::CE::commit(ck, &w.lambda, &F::ZERO) {
        return Err(format!("comm_M[{j}] does not open to λ"));
      }
    }
    Ok(())
  }

  /// Two predicates of each template with different wiring, negative coefficients, and
  /// full-field (wrapping) values.
  fn predicate(template: &str, k: usize, x: Option<F>) -> (Ccs<F>, Option<Assignment<F>>) {
    let one = |v: Var| vec![(v, F::ONE)];
    match template {
      "r1cs" => {
        let mut b = NativeCcsBuilder::new(Template::<F>::r1cs()).unwrap();
        let xv = b.alloc_io(x);
        if k == 0 {
          // a = x·x ; a·x = y + 3x − 11
          let a = b.alloc_w(x.map(|x| x.square()));
          let y = b.alloc_io(x.map(|x| x.square() * x - x * F::from(3) + F::from(11)));
          b.push_row(vec![one(xv), one(xv), one(a)]).unwrap();
          b.push_row(vec![
            one(a),
            one(xv),
            vec![(y, F::ONE), (xv, F::from(3)), (Var::One, -F::from(11))],
          ])
          .unwrap();
        } else {
          // a = x·(−x) ; (a + 2)·x = y − 7
          let a = b.alloc_w(x.map(|x| -x.square()));
          let y = b.alloc_io(x.map(|x| (F::from(2) - x.square()) * x + F::from(7)));
          b.push_row(vec![one(xv), vec![(xv, -F::ONE)], one(a)])
            .unwrap();
          b.push_row(vec![
            vec![(a, F::ONE), (Var::One, F::from(2))],
            one(xv),
            vec![(y, F::ONE), (Var::One, -F::from(7))],
          ])
          .unwrap();
        }
        b.build().unwrap()
      }
      _ => {
        // power(5): (M0 z)^5 = M1 z.
        let mut b = NativeCcsBuilder::new(Template::<F>::power(5)).unwrap();
        let xv = b.alloc_io(x);
        let p5 = |v: F| v.pow_vartime([5]);
        if k == 0 {
          // x^5 = w + 3 ; (w + x)^5 = y − x
          let w = b.alloc_w(x.map(|x| p5(x) - F::from(3)));
          let y = b.alloc_io(x.map(|x| p5(p5(x) - F::from(3) + x) + x));
          b.push_row(vec![one(xv), vec![(w, F::ONE), (Var::One, F::from(3))]])
            .unwrap();
          b.push_row(vec![
            vec![(w, F::ONE), (xv, F::ONE)],
            vec![(y, F::ONE), (xv, -F::ONE)],
          ])
          .unwrap();
        } else {
          // (2x − 1)^5 = w ; (w − x)^5 = y + 2x
          let w = b.alloc_w(x.map(|x| p5(x.double() - F::ONE)));
          let y = b.alloc_io(x.map(|x| p5(p5(x.double() - F::ONE) - x) - x.double()));
          b.push_row(vec![vec![(xv, F::from(2)), (Var::One, -F::ONE)], one(w)])
            .unwrap();
          b.push_row(vec![
            vec![(w, F::ONE), (xv, -F::ONE)],
            vec![(y, F::ONE), (xv, F::from(2))],
          ])
          .unwrap();
        }
        b.build().unwrap()
      }
    }
  }

  fn run_chain(template: &str, steps: usize) {
    let fam = Family::new((0..2).map(|k| predicate(template, k, None).0).collect()).unwrap();
    let keys = Keys::new(&fam);
    let mut rng = ChaCha20Rng::seed_from_u64(15);
    let c0 = fam.member(0);
    let (s, sp) = (num_vars(c0.m), num_vars(c0.n()));

    // Base case: the first CCCS as an ACCS at random points (u = 1, λ = e_0).
    let a0 = predicate(template, 0, Some(F::random(&mut rng))).1.unwrap();
    let r_x: Vec<F> = (0..s).map(|_| F::random(&mut rng)).collect();
    let r_y: Vec<F> = (0..sp).map(|_| F::random(&mut rng)).collect();
    let lambda = e_k(0, 2);
    let v = fam.claims(&lambda, &a0.z(), &r_x, &r_y).unwrap();
    let mut u = Running {
      comm_w: keys.commit_w(&a0.w),
      comm_m: keys.iota[0].clone(),
      u: F::ONE,
      io: a0.io.clone(),
      r_x,
      r_y,
      v,
    };
    let mut w = RunningW { w: a0.w, lambda };
    decide(&fam, &keys, &u, &w).unwrap();

    for step in 1..steps {
      let k = step % 2;
      let a2 = predicate(template, k, Some(F::random(&mut rng))).1.unwrap();
      assert!(fam.member(k).is_satisfied(&a2.z()).is_ok());
      let (proof, u_p, w_p) = prove(&fam, &keys, &u, &w, k, &a2);
      let u_v = verify(&fam, &keys, &u, k, &keys.commit_w(&a2.w), &a2.io, &proof)
        .unwrap_or_else(|e| panic!("{template} step {step}: verifier rejected: {e}"));
      assert_eq!(u_v, u_p, "prover and verifier fold to the same instance");
      decide(&fam, &keys, &u_v, &w_p)
        .unwrap_or_else(|e| panic!("{template} step {step}: oracle rejected: {e}"));
      u = u_v;
      w = w_p;
    }
    println!(
      "[spike] native HFS over E1::Scalar, template {template}: {steps} steps alternating K=2, every fold accepted by verifier and kn-ccs oracle"
    );
  }

  /// The B15 counter-example class (negative coefficients, wrapping products) folds for 100
  /// alternating steps once the HFS runs over the relation's native field.
  #[test]
  fn native_field_hfs_folds_100_steps_r1cs() {
    run_chain("r1cs", 100);
  }

  /// The same protocol, generalised to a degree-5 CCS template (deg_x = d + 1 = 6).
  #[test]
  fn native_field_hfs_folds_100_steps_degree5_ccs() {
    run_chain("power5", 100);
  }

  /// Negative cases: an unsatisfied incoming witness, a tampered claim and a tampered round
  /// message are rejected by the succinct verifier; a tampered fold output is caught by the
  /// oracle (decider layer).
  #[test]
  fn native_field_hfs_rejects() {
    let fam = Family::new((0..2).map(|k| predicate("r1cs", k, None).0).collect()).unwrap();
    let keys = Keys::new(&fam);
    let mut rng = ChaCha20Rng::seed_from_u64(16);
    let c0 = fam.member(0);
    let a0 = predicate("r1cs", 0, Some(F::random(&mut rng))).1.unwrap();
    let r_x: Vec<F> = (0..num_vars(c0.m)).map(|_| F::random(&mut rng)).collect();
    let r_y: Vec<F> = (0..num_vars(c0.n())).map(|_| F::random(&mut rng)).collect();
    let lambda = e_k(0, 2);
    let v = fam.claims(&lambda, &a0.z(), &r_x, &r_y).unwrap();
    let u = Running {
      comm_w: keys.commit_w(&a0.w),
      comm_m: keys.iota[0].clone(),
      u: F::ONE,
      io: a0.io.clone(),
      r_x,
      r_y,
      v,
    };
    let w = RunningW { w: a0.w, lambda };

    // Unsatisfied incoming instance: y is off by one.
    let mut bad = predicate("r1cs", 1, Some(F::from(5))).1.unwrap();
    bad.io[1] += F::ONE;
    let (p, _, _) = prove(&fam, &keys, &u, &w, 1, &bad);
    let err = verify(&fam, &keys, &u, 1, &keys.commit_w(&bad.w), &bad.io, &p).unwrap_err();
    println!("[spike] unsatisfied incoming witness rejected at: {err}");

    let good = predicate("r1cs", 1, Some(F::from(5))).1.unwrap();
    let cw = keys.commit_w(&good.w);
    let (p, _, w_p) = prove(&fam, &keys, &u, &w, 1, &good);
    assert!(verify(&fam, &keys, &u, 1, &cw, &good.io, &p).is_ok());
    let mut q = p.clone();
    q.sigma[0] += F::ONE;
    assert!(verify(&fam, &keys, &u, 1, &cw, &good.io, &q).is_err());
    let mut q = p.clone();
    q.px[0][0] += F::ONE;
    assert!(verify(&fam, &keys, &u, 1, &cw, &good.io, &q).is_err());
    // Wrong predicate id: transcript and ι change, so the fold no longer verifies.
    assert!(verify(&fam, &keys, &u, 0, &cw, &good.io, &p).is_err());
    // ε/θ are deferred claims: tampering θ_t passes the bare verifier only if c_y still holds,
    // which it does not; tampering the folded output instead is caught by the decider.
    let mut u_out = verify(&fam, &keys, &u, 1, &cw, &good.io, &p).unwrap();
    u_out.v[0] += F::ONE;
    assert!(decide(&fam, &keys, &u_out, &w_p).is_err());
  }
}
