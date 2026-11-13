//! In-circuit building blocks of the tree PCD (P6):
//!
//! - [`verify_hfs_multi`]: the HFS v2 verifier gadget for **μ running and ν incoming** inputs,
//!   step for step identical to `hfs::NIFS::verify` (transcript v2, γ/δ power assignment,
//!   weights ρ^0, ρ^1, …). For μ = ν = 1 it has exactly the constraint count of the P5 gadget
//!   `ivc::gadgets::verify_hfs`, which stays untouched (`test_multi_gadget_matches_p5_gadget_size`).
//! - [`CfAcc`]: a CycleFold accumulator whose `u` is carried as a bignat (like `X`), with the
//!   **relaxed–relaxed** Nova fold (`E ← E_0 + r·(T + r·E_1)`, `u, X ← · + r·· mod |E2::Scalar|`)
//!   and the fresh-instance fold. Merging a children's accumulators needs the relaxed fold, and
//!   `u` then grows by a 128-bit factor per level, so it cannot stay a native number.
//!
//! Everything is succinct: instances, proof messages and hints only.
use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS},
  frontend::{num::AllocatedNum, AllocatedBit, ConstraintSystem, SynthesisError},
  gadgets::{
    ecc::AllocatedPoint,
    nonnative::bignat::BigNat,
    utils::{alloc_bignat_constant, alloc_zero},
  },
  kilonova::{
    ivc::gadgets::{
      alloc_constant, bignat_limb_nums, bignat_of_bits, bignat_of_limbs, combine, enforce_zero_if,
      eq_eval, limbs_of, powers, squeeze_challenge, sum_exprs, sumcheck, weighted, AllocIncoming,
      AllocIndex, AllocRunning, Expr, HfsGadgetParams, NnPoint,
    },
    transcript::v2::{TAG_X_CLAIMS, TAG_Y_CLAIMS},
  },
  r1cs::RelaxedR1CSInstance,
  traits::{commitment::CommitmentTrait, Engine, Group, ROCircuitTrait, ROConstantsCircuit},
};
use ff::{Field, PrimeField, PrimeFieldBits};

/// Tag of the relaxed–relaxed CycleFold fold of the tree ("KNCF" ‖ v2 ‖ 1).
pub const TAG_CF_RELAXED: u64 = 0x4b4e_4346_0002_0001;
/// Tag of the fresh-instance CycleFold fold of the tree ("KNCF" ‖ v2 ‖ 2).
pub const TAG_CF_FRESH: u64 = 0x4b4e_4346_0002_0002;

/// HFS v2 proof in the circuit for (μ, ν) inputs.
pub(crate) struct AllocProofN<F: PrimeField> {
  pub(crate) sc_x: Vec<Vec<AllocatedNum<F>>>,
  pub(crate) sigma: Vec<Vec<AllocatedNum<F>>>,
  pub(crate) tau: Vec<Vec<AllocatedNum<F>>>,
  pub(crate) sc_y: Vec<Vec<AllocatedNum<F>>>,
  pub(crate) eps: Vec<Vec<AllocatedNum<F>>>,
  pub(crate) theta: Vec<Vec<AllocatedNum<F>>>,
}

/// Outputs of the multi-input HFS gadget.
#[allow(dead_code)] // the challenges are read by the native-vs-gadget tests
pub(crate) struct HfsMultiOut<F: PrimeField> {
  pub(crate) gamma: AllocatedNum<F>,
  pub(crate) alpha: Vec<AllocatedNum<F>>,
  pub(crate) r_x: Vec<AllocatedNum<F>>,
  pub(crate) delta: AllocatedNum<F>,
  pub(crate) r_y: Vec<AllocatedNum<F>>,
  pub(crate) rho: AllocatedNum<F>,
  pub(crate) rho_bits: Vec<AllocatedBit>,
  pub(crate) u: AllocatedNum<F>,
  pub(crate) io: Vec<AllocatedNum<F>>,
  pub(crate) v: Vec<AllocatedNum<F>>,
  pub(crate) lambda: Option<Vec<AllocatedNum<F>>>,
}

/// `Σ_i w_i · x_i` allocated (1 constraint), where `w_0 = 1` is folded in linearly, terms whose
/// `x_i` is a constant are linear, and every other term costs one product.
fn fold_sum<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  w: &[Expr<F>],
  xs: &[Expr<F>],
  constant: &[bool],
) -> Result<AllocatedNum<F>, SynthesisError> {
  let mut acc = Expr::zero();
  for (i, (wi, x)) in w.iter().zip(xs).enumerate() {
    if i == 0 {
      acc = acc.add(x);
    } else if constant[i] {
      // x is the constant 1 (an incoming u)
      acc = acc.add(wi);
    } else {
      acc = acc.add(&Expr::num(&wi.mul(cs.namespace(|| format!("w{i} x")), x)?));
    }
  }
  acc.alloc(cs.namespace(|| "sum"))
}

/// The HFS v2 verifier for μ running and ν incoming instances (μ ≥ 1), in an `E::Scalar`
/// circuit with transcript `E::RO2Circuit`. Mirrors `hfs::NIFS::verify_with_tags`. Every
/// equality is enforced only when `active = 1`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_hfs_multi<E: Engine, CS: ConstraintSystem<E::Scalar>>(
  mut cs: CS,
  p: &HfsGadgetParams<'_, E::Scalar, E::Base>,
  ro_consts: crate::traits::RO2ConstantsCircuit<E>,
  digest: &AllocatedNum<E::Scalar>,
  run: &[AllocRunning<E::Scalar>],
  inc: &[AllocIncoming<E::Scalar>],
  pf: &AllocProofN<E::Scalar>,
  active: &Expr<E::Scalar>,
) -> Result<HfsMultiOut<E::Scalar>, SynthesisError> {
  type F<E> = <E as Engine>::Scalar;
  let (mu, nu) = (run.len(), inc.len());
  if mu == 0 || pf.sigma.len() != mu || pf.tau.len() != nu {
    return Err(SynthesisError::Unsatisfiable);
  }
  let direct = matches!(run[0].index, AllocIndex::Direct(_));
  let tpl = p.template;
  let t = tpl.t();
  let mut ro = E::RO2Circuit::new(ro_consts);

  // Statement: tag, digest, μ, ν, running instances, incoming instances.
  let tag = alloc_constant(cs.namespace(|| "tag input"), F::<E>::from(p.tag_input))?;
  ro.absorb(&tag);
  ro.absorb(digest);
  let mu_c = alloc_constant(cs.namespace(|| "mu"), F::<E>::from(mu as u64))?;
  let nu_c = if nu == mu {
    mu_c.clone()
  } else {
    alloc_constant(cs.namespace(|| "nu"), F::<E>::from(nu as u64))?
  };
  ro.absorb(&mu_c);
  ro.absorb(&nu_c);
  for r in run {
    r.absorb(&mut ro);
  }
  for (l, i) in inc.iter().enumerate() {
    ro.absorb(&i.k);
    i.comm_w.absorb(&mut ro);
    i.io.iter().for_each(|x| ro.absorb(x));
    if direct {
      for j in 0..t {
        let pts: Vec<(E::Base, E::Base, bool)> = p.iota.iter().map(|io| io[j]).collect();
        NnPoint::select_constant(cs.namespace(|| format!("iota{l}_{j}")), &pts, &i.k_bits)?
          .absorb(&mut ro);
      }
    }
  }
  let (gamma, _) = squeeze_challenge(cs.namespace(|| "gamma"), &mut ro)?;
  let alpha = (0..p.s)
    .map(|i| squeeze_challenge(cs.namespace(|| format!("alpha{i}")), &mut ro).map(|x| x.0))
    .collect::<Result<Vec<_>, _>>()?;
  let gp = powers(cs.namespace(|| "gamma powers"), &gamma, mu * t + nu)?;

  // X phase.
  let mut cx = Vec::new();
  for (i, r) in run.iter().enumerate() {
    cx.extend(weighted(
      cs.namespace(|| format!("g v{i}")),
      &gp[i * t..(i + 1) * t],
      &r.v[..t],
    )?);
  }
  let claim_x = sum_exprs(cx);
  let (fx, r_x) = sumcheck(cs.namespace(|| "sc_x"), &mut ro, claim_x, &pf.sc_x, active)?;
  let eq_alpha = eq_eval(cs.namespace(|| "eq alpha"), &alpha, &r_x)?;
  let mut end_x = Expr::zero();
  for (i, r) in run.iter().enumerate() {
    let eq_rx = eq_eval(cs.namespace(|| format!("eq r_x{i}")), &r.r_x, &r_x)?;
    let gsig = weighted(
      cs.namespace(|| format!("g sigma{i}")),
      &gp[i * t..(i + 1) * t],
      &pf.sigma[i],
    )?;
    end_x = end_x.add(&Expr::num(
      &eq_rx.mul(cs.namespace(|| format!("eq * sigma{i}")), &sum_exprs(gsig))?,
    ));
  }
  for l in 0..nu {
    let comb = combine(cs.namespace(|| format!("combine tau{l}")), tpl, &pf.tau[l])?;
    let ea = Expr::num(&eq_alpha.mul(cs.namespace(|| format!("eq_alpha g^{l}")), &gp[mu * t + l])?);
    end_x = end_x.add(&Expr::num(
      &ea.mul(cs.namespace(|| format!("zero-check term{l}")), &comb)?,
    ));
  }
  enforce_zero_if(cs.namespace(|| "X end check"), &end_x.sub(&fx), active);
  let tx = alloc_constant(cs.namespace(|| "tag x"), F::<E>::from(TAG_X_CLAIMS))?;
  ro.absorb(&tx);
  pf.sigma
    .iter()
    .chain(&pf.tau)
    .flatten()
    .for_each(|x| ro.absorb(x));
  let (delta, _) = squeeze_challenge(cs.namespace(|| "delta"), &mut ro)?;
  let dp = powers(
    cs.namespace(|| "delta powers"),
    &delta,
    mu * (t + 1) + nu * t,
  )?;

  // Y phase.
  let mut cy = Vec::new();
  for (i, r) in run.iter().enumerate() {
    let b = i * (t + 1);
    cy.extend(weighted(
      cs.namespace(|| format!("d sigma{i}")),
      &dp[b..b + t],
      &pf.sigma[i],
    )?);
    cy.push(Expr::num(
      &dp[b + t].mul(cs.namespace(|| format!("d v_t{i}")), &Expr::num(&r.v[t]))?,
    ));
  }
  for l in 0..nu {
    let b = mu * (t + 1) + l * t;
    cy.extend(weighted(
      cs.namespace(|| format!("d tau{l}")),
      &dp[b..b + t],
      &pf.tau[l],
    )?);
  }
  let claim_y = sum_exprs(cy);
  let (fy, r_y) = sumcheck(cs.namespace(|| "sc_y"), &mut ro, claim_y, &pf.sc_y, active)?;
  let mut end_y = Expr::zero();
  for (i, r) in run.iter().enumerate() {
    let b = i * (t + 1);
    let eq_ry = eq_eval(cs.namespace(|| format!("eq r_y{i}")), &r.r_y, &r_y)?;
    let de = weighted(
      cs.namespace(|| format!("d eps{i}")),
      &dp[b..=b + t],
      &pf.eps[i],
    )?;
    end_y = end_y.add(&Expr::num(
      &eq_ry.mul(cs.namespace(|| format!("eq * eps{i}")), &sum_exprs(de))?,
    ));
  }
  for l in 0..nu {
    let th = &pf.theta[l];
    for j in 0..t {
      let dt = Expr::num(&dp[mu * (t + 1) + l * t + j].mul(
        cs.namespace(|| format!("d theta{l}_{j}")),
        &Expr::num(&th[j]),
      )?);
      end_y = end_y.add(&Expr::num(&dt.mul(
        cs.namespace(|| format!("d theta{l}_{j} z")),
        &Expr::num(&th[t]),
      )?));
    }
  }
  enforce_zero_if(cs.namespace(|| "Y end check"), &end_y.sub(&fy), active);
  let ty = alloc_constant(cs.namespace(|| "tag y"), F::<E>::from(TAG_Y_CLAIMS))?;
  ro.absorb(&ty);
  pf.eps
    .iter()
    .chain(&pf.theta)
    .flatten()
    .for_each(|x| ro.absorb(x));
  let (rho, rho_bits) = squeeze_challenge(cs.namespace(|| "rho"), &mut ro)?;

  // Fold of the scalar parts with weights ρ^0, ρ^1, … (running first, then incoming).
  let w = powers(cs.namespace(|| "rho powers"), &rho, mu + nu)?;
  let is_const: Vec<bool> = (0..mu + nu).map(|i| i >= mu).collect();
  let not_const = vec![false; mu + nu];
  let one = Expr::constant::<CS>(F::<E>::ONE);
  let us: Vec<Expr<F<E>>> = run
    .iter()
    .map(|r| Expr::num(&r.u))
    .chain((0..nu).map(|_| one.clone()))
    .collect();
  let u = fold_sum(cs.namespace(|| "u fold"), &w, &us, &is_const)?;
  let fold_vec = |cs: &mut CS,
                  name: &str,
                  a: &[&[AllocatedNum<F<E>>]]|
   -> Result<Vec<AllocatedNum<F<E>>>, SynthesisError> {
    (0..a[0].len())
      .map(|e| {
        let xs: Vec<Expr<F<E>>> = a.iter().map(|v| Expr::num(&v[e])).collect();
        fold_sum(cs.namespace(|| format!("{name}{e}")), &w, &xs, &not_const)
      })
      .collect()
  };
  let ios: Vec<&[AllocatedNum<F<E>>]> = run
    .iter()
    .map(|r| &r.io[..])
    .chain(inc.iter().map(|i| &i.io[..]))
    .collect();
  let io = fold_vec(&mut cs, "io", &ios)?;
  let claims: Vec<&[AllocatedNum<F<E>>]> = pf.eps.iter().chain(&pf.theta).map(|v| &v[..]).collect();
  let v = fold_vec(&mut cs, "v", &claims)?;
  let lambda = if direct {
    None
  } else {
    let lams: Vec<&[AllocatedNum<F<E>>]> = run
      .iter()
      .map(|r| match &r.index {
        AllocIndex::Span(l) => Ok(&l[..]),
        AllocIndex::Direct(_) => Err(SynthesisError::Unsatisfiable),
      })
      .collect::<Result<_, _>>()?;
    let k = lams[0].len();
    let out = (0..k)
      .map(|e| {
        let mut xs: Vec<Expr<F<E>>> = lams.iter().map(|l| Expr::num(&l[e])).collect();
        xs.extend(inc.iter().map(|i| Expr::bit(&i.k_bits[e])));
        fold_sum(cs.namespace(|| format!("lambda{e}")), &w, &xs, &not_const)
      })
      .collect::<Result<Vec<_>, _>>()?;
    Some(out)
  };
  Ok(HfsMultiOut {
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

/// A CycleFold accumulator (relaxed R1CS instance on E, field `E::Scalar`) in an `E::Base`
/// circuit: `W`, `E` native points; `u` and every `X_i` as `BN_N_LIMBS` limbs of
/// `BN_LIMB_WIDTH` bits.
#[derive(Clone)]
pub(crate) struct CfAcc<E: Engine> {
  pub(crate) w: AllocatedPoint<E>,
  pub(crate) e: AllocatedPoint<E>,
  pub(crate) u: Vec<AllocatedNum<E::Base>>,
  pub(crate) x: Vec<Vec<AllocatedNum<E::Base>>>,
}

fn alloc_limbs<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  v: Option<&E::Scalar>,
) -> Result<Vec<AllocatedNum<E::Base>>, SynthesisError> {
  let limbs = v.map(limbs_of::<E::Scalar, E::Base>);
  (0..BN_N_LIMBS)
    .map(|l| {
      AllocatedNum::alloc(cs.namespace(|| format!("{l}")), || {
        Ok(limbs.as_ref().map_or(E::Base::ZERO, |v| v[l]))
      })
    })
    .collect()
}

impl<E: Engine> CfAcc<E> {
  /// Allocates `n` inputs (advice; bound by a link hash to range-checked outputs of the
  /// circuit that produced them). `None` allocates zeros (shape synthesis).
  pub(crate) fn alloc<CS: ConstraintSystem<E::Base>>(
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
    let u = alloc_limbs::<E, _>(cs.namespace(|| "u"), inst.map(|u| &u.u))?;
    let x = (0..n)
      .map(|i| alloc_limbs::<E, _>(cs.namespace(|| format!("X{i}")), inst.map(|u| &u.X[i])))
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self { w, e, u, x })
  }

  /// The default accumulator (identity W and E, u = 0, X = 0), all constants.
  pub(crate) fn default<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    n: usize,
  ) -> Result<Self, SynthesisError> {
    let w = AllocatedPoint::default(cs.namespace(|| "W"))?;
    let e = AllocatedPoint::default(cs.namespace(|| "E"))?;
    let zero = alloc_zero(cs.namespace(|| "zero"));
    let u = vec![zero.clone(); BN_N_LIMBS];
    let x = vec![vec![zero; BN_N_LIMBS]; n];
    Ok(Self { w, e, u, x })
  }

  /// Absorbs `W(x, y, inf), E(x, y, inf), u limbs, X limbs` (native twin:
  /// `pcd::cyclefold::absorb_acc`).
  pub(crate) fn absorb<RO: ROCircuitTrait<E::Base>>(&self, ro: &mut RO) {
    for p in [&self.w, &self.e] {
      ro.absorb(&p.x);
      ro.absorb(&p.y);
      ro.absorb(&p.is_infinity);
    }
    self
      .u
      .iter()
      .chain(self.x.iter().flatten())
      .for_each(|l| ro.absorb(l));
  }

  fn modulus<CS: ConstraintSystem<E::Base>>(mut cs: CS) -> Result<BigNat<E::Base>, SynthesisError> {
    alloc_bignat_constant(
      cs.namespace(|| "modulus"),
      &E::GE::group_params().2,
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )
  }

  /// `(a + b) mod m` and `(a + r·b) mod m` as limb variables.
  fn red<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    a: &[AllocatedNum<E::Base>],
    b: &BigNat<E::Base>,
    m: &BigNat<E::Base>,
  ) -> Result<Vec<AllocatedNum<E::Base>>, SynthesisError> {
    let sum = bignat_of_limbs(a).add(b)?;
    let red = sum.red_mod(cs.namespace(|| "reduce"), m)?;
    bignat_limb_nums(cs.namespace(|| "out"), &red)
  }

  /// Relaxed–relaxed fold with cross term `t`: `r = H(TAG_CF_RELAXED, params, self, other, t)`,
  /// `W ← W + r·W'`, `E ← E + r·(T + r·E')`, `u ← u + r·u'`, `X ← X + r·X' (mod |E::Scalar|)`.
  pub(crate) fn fold_relaxed<CS: ConstraintSystem<E::Base>>(
    &self,
    mut cs: CS,
    params: &AllocatedNum<E::Base>,
    other: &Self,
    t: &AllocatedPoint<E>,
    ro_consts: ROConstantsCircuit<E>,
  ) -> Result<Self, SynthesisError> {
    assert_eq!(self.x.len(), other.x.len());
    let mut ro = E::ROCircuit::new(ro_consts);
    let tag = alloc_constant(cs.namespace(|| "tag"), E::Base::from(TAG_CF_RELAXED))?;
    ro.absorb(&tag);
    ro.absorb(params);
    self.absorb(&mut ro);
    other.absorb(&mut ro);
    ro.absorb(&t.x);
    ro.absorb(&t.y);
    ro.absorb(&t.is_infinity);
    let (_, r_bits) = squeeze_challenge(cs.namespace(|| "r"), &mut ro)?;

    let rw = other.w.scalar_mul(cs.namespace(|| "r * W'"), &r_bits)?;
    let w = self.w.add(cs.namespace(|| "W + r W'"), &rw)?;
    let re = other.e.scalar_mul(cs.namespace(|| "r * E'"), &r_bits)?;
    let te = t.add(cs.namespace(|| "T + r E'"), &re)?;
    let rte = te.scalar_mul(cs.namespace(|| "r * (T + r E')"), &r_bits)?;
    let e = self.e.add(cs.namespace(|| "E + r (T + r E')"), &rte)?;

    let r_bn = bignat_of_bits::<E::Base>(&r_bits);
    let m_bn = Self::modulus(cs.namespace(|| "modulus"))?;
    let (_, ru) = bignat_of_limbs(&other.u).mult_mod(cs.namespace(|| "r u'"), &r_bn, &m_bn)?;
    let u = Self::red(cs.namespace(|| "u"), &self.u, &ru, &m_bn)?;
    let mut x = Vec::with_capacity(self.x.len());
    for (i, (a, b)) in self.x.iter().zip(&other.x).enumerate() {
      let (_, rb) =
        bignat_of_limbs(b).mult_mod(cs.namespace(|| format!("r x{i}")), &r_bn, &m_bn)?;
      x.push(Self::red(cs.namespace(|| format!("x{i}")), a, &rb, &m_bn)?);
    }
    Ok(Self { w, e, u, x })
  }

  /// Fresh-instance fold (u = 1, E = 0) of `(comm_w, x)` with cross term `t`:
  /// `r = H(TAG_CF_FRESH, params, self, comm_w, x limbs, t)`, `W ← W + r·comm_w`, `E ← E + r·T`,
  /// `u ← u + r`, `X ← X + r·x (mod |E::Scalar|)`. The limbs of `x` must be in range.
  pub(crate) fn fold_fresh<CS: ConstraintSystem<E::Base>>(
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
    let tag = alloc_constant(cs.namespace(|| "tag"), E::Base::from(TAG_CF_FRESH))?;
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
    let (_, r_bits) = squeeze_challenge(cs.namespace(|| "r"), &mut ro)?;

    let rw = comm_w.scalar_mul(cs.namespace(|| "r * comm_w"), &r_bits)?;
    let w = self.w.add(cs.namespace(|| "W + r comm_w"), &rw)?;
    let rt = t.scalar_mul(cs.namespace(|| "r * T"), &r_bits)?;
    let e = self.e.add(cs.namespace(|| "E + r T"), &rt)?;

    let r_bn = bignat_of_bits::<E::Base>(&r_bits);
    let m_bn = Self::modulus(cs.namespace(|| "modulus"))?;
    let u = Self::red(cs.namespace(|| "u"), &self.u, &r_bn, &m_bn)?;
    let mut x_new = Vec::with_capacity(x.len());
    for (i, (xi, run)) in x.iter().zip(&self.x).enumerate() {
      let (_, prod) = xi.mult_mod(cs.namespace(|| format!("r x{i}")), &r_bn, &m_bn)?;
      x_new.push(Self::red(
        cs.namespace(|| format!("x{i}")),
        run,
        &prod,
        &m_bn,
      )?);
    }
    Ok(Self { w, e, u, x: x_new })
  }
}

/// Little-endian bits of a value below `2^n`, enforced to recompose to `x` (this range-checks
/// `x < 2^n`). `n` ≤ 64.
pub(crate) fn to_bits<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
  mut cs: CS,
  x: &Expr<F>,
  n: usize,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
  let bits = (0..n)
    .map(|i| {
      AllocatedBit::alloc(
        cs.namespace(|| format!("b{i}")),
        x.val.map(|v| v.to_le_bits()[i]),
      )
    })
    .collect::<Result<Vec<_>, _>>()?;
  let mut c = F::ONE;
  let mut acc = Expr::zero();
  for b in &bits {
    acc = acc.add(&Expr::bit(b).scale(c));
    c = c.double();
  }
  enforce_zero_if(
    cs.namespace(|| "x = sum bits"),
    &acc.sub(x),
    &Expr::constant::<CS>(F::ONE),
  );
  Ok(bits)
}
