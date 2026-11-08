//! v2 HFS non-interactive folding: μ running ACCS + ν incoming CCCS → one running ACCS.
//!
//! Index conventions (μ running inputs i, ν incoming inputs l, t matrices, s / s' variables):
//!
//! - γ powers: running (i, j) ↦ γ^{i·t+j}; incoming l ↦ γ^{μt+l}.
//! - δ powers: running (i, j) ↦ δ^{i(t+1)+j}, running z_i ↦ δ^{i(t+1)+t};
//!   incoming (l, j) ↦ δ^{μ(t+1)+l·t+j}.
//! - Fold weights ρ^0, ρ^1, … over running inputs first, then incoming inputs.
//!
//! For μ = ν = 1 these are the v1 assignments (spec N6–N8).
use super::{
  check_len,
  instance::{IncomingInstance, RunningInstance, RunningWitness, Variant},
  sumcheck::{self, eq_eval, eq_table, powers, Term},
  HfsError, HfsParams, Phase,
};
use crate::{
  constants::NUM_CHALLENGE_BITS,
  kilonova::transcript::v2::{absorb_commitment, absorb_tag, TAG_X_CLAIMS, TAG_Y_CLAIMS},
  traits::{Engine, ROTrait},
  Commitment,
};
use core::marker::PhantomData;
use ff::Field;
use serde::{Deserialize, Serialize};

/// HFS v2 proof: two sum-checks and the helper claims.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct HfsProof<E: Engine> {
  /// X-phase round messages: s rounds × (deg_x + 1) evaluations.
  pub sc_x: Vec<Vec<E::Scalar>>,
  /// σ: μ × t running row claims `R_{i,j}(r_x')`.
  pub sigma: Vec<Vec<E::Scalar>>,
  /// τ: ν × t incoming claims `(M_{k_l,j} z_l)~(r_x')`.
  pub tau: Vec<Vec<E::Scalar>>,
  /// Y-phase round messages: s' rounds × 3 evaluations.
  pub sc_y: Vec<Vec<E::Scalar>>,
  /// ε: μ × (t + 1): `M̃_{λ_i,j}(r_x', r_y')` and `z̃_i(r_y')`.
  pub eps: Vec<Vec<E::Scalar>>,
  /// θ: ν × (t + 1): `M̃_{k_l,j}(r_x', r_y')` and `z̃_l(r_y')`.
  pub theta: Vec<Vec<E::Scalar>>,
}

/// All Fiat–Shamir challenges of one fold (returned by both prover and verifier).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct Challenges<E: Engine> {
  /// Batching challenge of the X phase.
  pub gamma: E::Scalar,
  /// Zero-check point (s entries).
  pub alpha: Vec<E::Scalar>,
  /// X-phase point r_x' (s entries).
  pub r_x: Vec<E::Scalar>,
  /// Batching challenge of the Y phase.
  pub delta: E::Scalar,
  /// Y-phase point r_y' (s' entries).
  pub r_y: Vec<E::Scalar>,
  /// Fold challenge (paper η).
  pub rho: E::Scalar,
}

/// Prover result.
#[derive(Clone, Debug)]
pub struct ProverOutput<E: Engine, V: Variant<E>> {
  /// The NIFS proof.
  pub proof: HfsProof<E>,
  /// The folded instance (equal to the verifier's output).
  pub instance: RunningInstance<E, V>,
  /// The folded witness.
  pub witness: RunningWitness<E>,
  /// The prover's challenges.
  pub challenges: Challenges<E>,
}

/// Transcript tags. Production code always uses [`Tags::of`]; tests vary them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Tags {
  pub(crate) input: u64,
  pub(crate) x_claims: u64,
  pub(crate) y_claims: u64,
}

impl Tags {
  pub(crate) fn of<E: Engine, V: Variant<E>>() -> Self {
    Self {
      input: V::TAG_INPUT,
      x_claims: TAG_X_CLAIMS,
      y_claims: TAG_Y_CLAIMS,
    }
  }
}

/// The v2 HFS for variant `V` ([`super::Direct`] or [`super::Span`]).
pub struct NIFS<E: Engine, V: Variant<E>>(PhantomData<(E, V)>);

fn absorb_all<E: Engine>(ro: &mut E::RO2, v: &[E::Scalar]) {
  v.iter().for_each(|x| ro.absorb(*x));
}

/// Validates the inputs (Input layer).
fn check_inputs<E: Engine, V: Variant<E>>(
  pp: &HfsParams<E>,
  running: &[RunningInstance<E, V>],
  incoming: &[IncomingInstance<E>],
) -> Result<(), HfsError> {
  if running.is_empty() && incoming.is_empty() {
    return Err(HfsError::Shape {
      what: "number of inputs mu + nu".into(),
      expected: 1,
      got: 0,
    });
  }
  let t = pp.t();
  for (i, u) in running.iter().enumerate() {
    let what = format!("running[{i}]");
    check_len(format!("{what}.io"), pp.num_io(), u.io.len())?;
    check_len(format!("{what}.r_x"), pp.s(), u.r_x.len())?;
    check_len(format!("{what}.r_y"), pp.s_prime(), u.r_y.len())?;
    check_len(format!("{what}.v"), t + 1, u.v.len())?;
    V::check_index(pp, &u.index, &what)?;
  }
  for (l, inc) in incoming.iter().enumerate() {
    if inc.k >= pp.k() {
      return Err(HfsError::PredicateId {
        id: inc.k,
        k: pp.k(),
      });
    }
    check_len(format!("incoming[{l}].io"), pp.num_io(), inc.io.len())?;
  }
  Ok(())
}

/// Validates the proof shape against (μ, ν) and the parameters (Input layer).
fn check_proof_shape<E: Engine>(
  pp: &HfsParams<E>,
  mu: usize,
  nu: usize,
  p: &HfsProof<E>,
) -> Result<(), HfsError> {
  let t = pp.t();
  let deg_x = pp.template().deg_x();
  check_len("proof.sc_x rounds", pp.s(), p.sc_x.len())?;
  for (r, m) in p.sc_x.iter().enumerate() {
    check_len(format!("proof.sc_x[{r}] evaluations"), deg_x + 1, m.len())?;
  }
  check_len("proof.sc_y rounds", pp.s_prime(), p.sc_y.len())?;
  for (r, m) in p.sc_y.iter().enumerate() {
    check_len(format!("proof.sc_y[{r}] evaluations"), 3, m.len())?;
  }
  let rows = |what: &str, v: &[Vec<E::Scalar>], n: usize, w: usize| -> Result<(), HfsError> {
    check_len(format!("proof.{what} inputs"), n, v.len())?;
    for (i, row) in v.iter().enumerate() {
      check_len(format!("proof.{what}[{i}]"), w, row.len())?;
    }
    Ok(())
  };
  rows("sigma", &p.sigma, mu, t)?;
  rows("tau", &p.tau, nu, t)?;
  rows("eps", &p.eps, mu, t + 1)?;
  rows("theta", &p.theta, nu, t + 1)
}

/// Absorbs the statement: tag, digest, (μ, ν), running instances, incoming instances.
fn absorb_inputs<E: Engine, V: Variant<E>>(
  ro: &mut E::RO2,
  pp: &HfsParams<E>,
  tags: &Tags,
  running: &[RunningInstance<E, V>],
  incoming: &[IncomingInstance<E>],
) {
  absorb_tag::<E>(ro, tags.input);
  ro.absorb(pp.digest());
  ro.absorb(E::Scalar::from(running.len() as u64));
  ro.absorb(E::Scalar::from(incoming.len() as u64));
  for u in running {
    absorb_commitment::<E>(ro, &u.comm_w);
    V::absorb_running_index(ro, &u.index);
    ro.absorb(u.u);
    absorb_all::<E>(ro, &u.io);
    absorb_all::<E>(ro, &u.r_x);
    absorb_all::<E>(ro, &u.r_y);
    absorb_all::<E>(ro, &u.v);
  }
  for inc in incoming {
    ro.absorb(E::Scalar::from(inc.k as u64));
    absorb_commitment::<E>(ro, &inc.comm_w);
    absorb_all::<E>(ro, &inc.io);
    V::absorb_incoming_index(ro, pp, inc.k);
  }
}

fn absorb_claims<E: Engine>(ro: &mut E::RO2, tag: u64, a: &[Vec<E::Scalar>], b: &[Vec<E::Scalar>]) {
  absorb_tag::<E>(ro, tag);
  a.iter().chain(b).for_each(|row| absorb_all::<E>(ro, row));
}

fn padded<F: Field>(v: &[F], len: usize) -> Vec<F> {
  let mut v = v.to_vec();
  v.resize(len, F::ZERO);
  v
}

/// Row table of `M_{λ,j}` against the column weights: `T[r] = Σ_k λ_k Σ_{(r,c,v) ∈ M_{k,j}} v·w[c]`.
fn row_table<E: Engine>(
  pp: &HfsParams<E>,
  lambda: &[E::Scalar],
  j: usize,
  col_w: &[E::Scalar],
) -> Vec<E::Scalar> {
  let mut t = vec![E::Scalar::ZERO; 1 << pp.s()];
  for (sh, l) in pp.shapes().iter().zip(lambda) {
    if bool::from(l.is_zero()) {
      continue;
    }
    for &(r, c, v) in &sh.matrices()[j] {
      t[r] += *l * v * col_w[c];
    }
  }
  t
}

/// Column table: `T[c] = Σ_k λ_k Σ_{(r,c,v) ∈ M_{k,j}} v·w[r]`.
fn col_table<E: Engine>(
  pp: &HfsParams<E>,
  lambda: &[E::Scalar],
  j: usize,
  row_w: &[E::Scalar],
) -> Vec<E::Scalar> {
  let mut t = vec![E::Scalar::ZERO; 1 << pp.s_prime()];
  for (sh, l) in pp.shapes().iter().zip(lambda) {
    if bool::from(l.is_zero()) {
      continue;
    }
    for &(r, c, v) in &sh.matrices()[j] {
      t[c] += *l * v * row_w[r];
    }
  }
  t
}

/// Σ_i w_i · x_i over equal-length vectors.
fn lincomb<F: Field>(weights: &[F], vecs: &[&[F]]) -> Vec<F> {
  let mut out = vec![F::ZERO; vecs.first().map_or(0, |v| v.len())];
  for (w, v) in weights.iter().zip(vecs) {
    for (o, x) in out.iter_mut().zip(v.iter()) {
      *o += *w * x;
    }
  }
  out
}

impl<E: Engine, V: Variant<E>> NIFS<E, V> {
  /// Folds `running` (with witnesses) and `incoming` (with witnesses). The prover does not
  /// check that its inputs are satisfied; an unsatisfied input gives a proof the verifier
  /// rejects. Input lengths are checked.
  pub fn prove(
    pp: &HfsParams<E>,
    running: &[RunningInstance<E, V>],
    running_w: &[RunningWitness<E>],
    incoming: &[IncomingInstance<E>],
    incoming_w: &[Vec<E::Scalar>],
  ) -> Result<ProverOutput<E, V>, HfsError> {
    Self::prove_with_tags(
      pp,
      running,
      running_w,
      incoming,
      incoming_w,
      &Tags::of::<E, V>(),
    )
  }

  pub(crate) fn prove_with_tags(
    pp: &HfsParams<E>,
    running: &[RunningInstance<E, V>],
    running_w: &[RunningWitness<E>],
    incoming: &[IncomingInstance<E>],
    incoming_w: &[Vec<E::Scalar>],
    tags: &Tags,
  ) -> Result<ProverOutput<E, V>, HfsError> {
    check_inputs(pp, running, incoming)?;
    check_len("running witnesses", running.len(), running_w.len())?;
    check_len("incoming witnesses", incoming.len(), incoming_w.len())?;
    for (i, w) in running_w.iter().enumerate() {
      check_len(format!("running_w[{i}].w"), pp.num_w(), w.w.len())?;
      check_len(format!("running_w[{i}].lambda"), pp.k(), w.lambda.len())?;
    }
    for (l, w) in incoming_w.iter().enumerate() {
      check_len(format!("incoming_w[{l}]"), pp.num_w(), w.len())?;
    }
    let (mu, nu, t) = (running.len(), incoming.len(), pp.t());
    let (s, sp) = (pp.s(), pp.s_prime());
    let tpl = pp.template();

    let mut ro = E::RO2::new(pp.ro_consts().clone());
    absorb_inputs(&mut ro, pp, tags, running, incoming);
    let gamma = ro.squeeze(NUM_CHALLENGE_BITS);
    let alpha: Vec<E::Scalar> = (0..s).map(|_| ro.squeeze(NUM_CHALLENGE_BITS)).collect();
    let gp = powers(gamma, mu * t + nu);

    let z_run: Vec<Vec<E::Scalar>> = running
      .iter()
      .zip(running_w)
      .map(|(u, w)| [w.w.as_slice(), &[u.u], &u.io].concat())
      .collect();
    let z_inc: Vec<Vec<E::Scalar>> = incoming
      .iter()
      .zip(incoming_w)
      .map(|(inc, w)| [w.as_slice(), &[E::Scalar::ONE], &inc.io].concat())
      .collect();
    let lambda_inc: Vec<Vec<E::Scalar>> = incoming.iter().map(|inc| pp.e_k(inc.k)).collect();

    // X phase. Tables: eq(r_x^i) (μ), eq(α), R_{i,j} (μt), M_{k_l,j} z_l (νt).
    let eq_ry_run: Vec<Vec<E::Scalar>> = running.iter().map(|u| eq_table(&u.r_y)).collect();
    let mut tables: Vec<Vec<E::Scalar>> = running.iter().map(|u| eq_table(&u.r_x)).collect();
    tables.push(eq_table(&alpha));
    for (w, eq_ry) in running_w.iter().zip(&eq_ry_run) {
      for j in 0..t {
        tables.push(row_table(pp, &w.lambda, j, eq_ry));
      }
    }
    for (inc, z) in incoming.iter().zip(&z_inc) {
      for j in 0..t {
        tables.push(padded(&pp.shape(inc.k).mul_vec(j, z), 1 << s));
      }
    }
    let row_base = mu + 1;
    let inc_base = row_base + mu * t;
    let mut terms: Vec<Term<E::Scalar>> = Vec::new();
    for i in 0..mu {
      for j in 0..t {
        terms.push((gp[i * t + j], vec![i, row_base + i * t + j]));
      }
    }
    for l in 0..nu {
      for (ms, c) in tpl.multisets().iter().zip(tpl.coeffs()) {
        let mut idx = vec![mu];
        idx.extend(ms.iter().map(|j| inc_base + l * t + j));
        terms.push((gp[mu * t + l] * c, idx));
      }
    }
    let (sc_x, r_xp, finals) = sumcheck::prove(tables, &terms, tpl.deg_x(), &mut ro);
    let sigma: Vec<Vec<E::Scalar>> = (0..mu)
      .map(|i| finals[row_base + i * t..row_base + (i + 1) * t].to_vec())
      .collect();
    let tau: Vec<Vec<E::Scalar>> = (0..nu)
      .map(|l| finals[inc_base + l * t..inc_base + (l + 1) * t].to_vec())
      .collect();
    absorb_claims::<E>(&mut ro, tags.x_claims, &sigma, &tau);
    let delta = ro.squeeze(NUM_CHALLENGE_BITS);
    let dp = powers(delta, mu * (t + 1) + nu * t);

    // Y phase. Running i: [eq(r_y^i), z_i, C_{λ_i,0..t}]; incoming l: [z_l, C_{e_k,0..t}].
    let eq_rx = eq_table(&r_xp);
    let mut tables: Vec<Vec<E::Scalar>> = Vec::new();
    let mut terms: Vec<Term<E::Scalar>> = Vec::new();
    for (i, (w, eq_ry)) in running_w.iter().zip(eq_ry_run).enumerate() {
      let base = tables.len();
      tables.push(eq_ry);
      tables.push(padded(&z_run[i], 1 << sp));
      for j in 0..t {
        tables.push(col_table(pp, &w.lambda, j, &eq_rx));
        terms.push((dp[i * (t + 1) + j], vec![base, base + 2 + j]));
      }
      terms.push((dp[i * (t + 1) + t], vec![base, base + 1]));
    }
    for (l, lam) in lambda_inc.iter().enumerate() {
      let base = tables.len();
      tables.push(padded(&z_inc[l], 1 << sp));
      for j in 0..t {
        tables.push(col_table(pp, lam, j, &eq_rx));
        terms.push((dp[mu * (t + 1) + l * t + j], vec![base + 1 + j, base]));
      }
    }
    let (sc_y, r_yp, finals) = sumcheck::prove(tables, &terms, 2, &mut ro);
    let eps: Vec<Vec<E::Scalar>> = (0..mu)
      .map(|i| {
        let base = i * (t + 2);
        let mut e = finals[base + 2..base + 2 + t].to_vec();
        e.push(finals[base + 1]);
        e
      })
      .collect();
    let theta: Vec<Vec<E::Scalar>> = (0..nu)
      .map(|l| {
        let base = mu * (t + 2) + l * (t + 1);
        let mut e = finals[base + 1..base + 1 + t].to_vec();
        e.push(finals[base]);
        e
      })
      .collect();
    absorb_claims::<E>(&mut ro, tags.y_claims, &eps, &theta);
    let rho = ro.squeeze(NUM_CHALLENGE_BITS);

    let proof = HfsProof {
      sc_x,
      sigma,
      tau,
      sc_y,
      eps,
      theta,
    };
    let challenges = Challenges {
      gamma,
      alpha,
      r_x: r_xp,
      delta,
      r_y: r_yp,
      rho,
    };
    let instance = fold_instances(pp, running, incoming, &proof, &challenges);
    let witness = fold_witnesses(pp, running_w, incoming, incoming_w, rho);
    Ok(ProverOutput {
      proof,
      instance,
      witness,
      challenges,
    })
  }

  /// Succinct verifier: checks both sum-checks and returns the folded instance. It uses only
  /// the instances, the proof and the public parameters (no witness, no matrix). The ε/θ
  /// claims are deferred to [`super::decide`].
  pub fn verify(
    pp: &HfsParams<E>,
    running: &[RunningInstance<E, V>],
    incoming: &[IncomingInstance<E>],
    proof: &HfsProof<E>,
  ) -> Result<(RunningInstance<E, V>, Challenges<E>), HfsError> {
    Self::verify_with_tags(pp, running, incoming, proof, &Tags::of::<E, V>())
  }

  pub(crate) fn verify_with_tags(
    pp: &HfsParams<E>,
    running: &[RunningInstance<E, V>],
    incoming: &[IncomingInstance<E>],
    p: &HfsProof<E>,
    tags: &Tags,
  ) -> Result<(RunningInstance<E, V>, Challenges<E>), HfsError> {
    check_inputs(pp, running, incoming)?;
    let (mu, nu, t) = (running.len(), incoming.len(), pp.t());
    check_proof_shape(pp, mu, nu, p)?;
    let tpl = pp.template();

    let mut ro = E::RO2::new(pp.ro_consts().clone());
    absorb_inputs(&mut ro, pp, tags, running, incoming);
    let gamma = ro.squeeze(NUM_CHALLENGE_BITS);
    let alpha: Vec<E::Scalar> = (0..pp.s())
      .map(|_| ro.squeeze(NUM_CHALLENGE_BITS))
      .collect();
    let gp = powers(gamma, mu * t + nu);

    let claim_x = running
      .iter()
      .enumerate()
      .fold(E::Scalar::ZERO, |acc, (i, u)| {
        (0..t).fold(acc, |a, j| a + gp[i * t + j] * u.v[j])
      });
    let (fx, r_xp) = sumcheck::verify(claim_x, &p.sc_x, Phase::X, &mut ro)?;
    let eq_alpha = eq_eval(&alpha, &r_xp);
    let mut c_x = E::Scalar::ZERO;
    for (i, u) in running.iter().enumerate() {
      let s = (0..t).fold(E::Scalar::ZERO, |a, j| a + gp[i * t + j] * p.sigma[i][j]);
      c_x += eq_eval(&u.r_x, &r_xp) * s;
    }
    for (l, tau) in p.tau.iter().enumerate() {
      c_x += eq_alpha * gp[mu * t + l] * tpl.combine(tau);
    }
    if c_x != fx {
      return Err(HfsError::EndCheck { phase: Phase::X });
    }
    absorb_claims::<E>(&mut ro, tags.x_claims, &p.sigma, &p.tau);
    let delta = ro.squeeze(NUM_CHALLENGE_BITS);
    let dp = powers(delta, mu * (t + 1) + nu * t);

    let mut claim_y = E::Scalar::ZERO;
    for (i, u) in running.iter().enumerate() {
      for j in 0..t {
        claim_y += dp[i * (t + 1) + j] * p.sigma[i][j];
      }
      claim_y += dp[i * (t + 1) + t] * u.v[t];
    }
    for l in 0..nu {
      for j in 0..t {
        claim_y += dp[mu * (t + 1) + l * t + j] * p.tau[l][j];
      }
    }
    let (fy, r_yp) = sumcheck::verify(claim_y, &p.sc_y, Phase::Y, &mut ro)?;
    let mut c_y = E::Scalar::ZERO;
    for (i, u) in running.iter().enumerate() {
      let s = (0..=t).fold(E::Scalar::ZERO, |a, j| {
        a + dp[i * (t + 1) + j] * p.eps[i][j]
      });
      c_y += eq_eval(&u.r_y, &r_yp) * s;
    }
    for (l, th) in p.theta.iter().enumerate() {
      for j in 0..t {
        c_y += dp[mu * (t + 1) + l * t + j] * th[j] * th[t];
      }
    }
    if c_y != fy {
      return Err(HfsError::EndCheck { phase: Phase::Y });
    }
    absorb_claims::<E>(&mut ro, tags.y_claims, &p.eps, &p.theta);
    let rho = ro.squeeze(NUM_CHALLENGE_BITS);
    let challenges = Challenges {
      gamma,
      alpha,
      r_x: r_xp,
      delta,
      r_y: r_yp,
      rho,
    };
    Ok((
      fold_instances(pp, running, incoming, p, &challenges),
      challenges,
    ))
  }
}

/// Folds the instances with weights ρ^0, ρ^1, … (running first, then incoming).
fn fold_instances<E: Engine, V: Variant<E>>(
  pp: &HfsParams<E>,
  running: &[RunningInstance<E, V>],
  incoming: &[IncomingInstance<E>],
  p: &HfsProof<E>,
  ch: &Challenges<E>,
) -> RunningInstance<E, V> {
  let w = powers(ch.rho, running.len() + incoming.len());
  let comms: Vec<Commitment<E>> = running
    .iter()
    .map(|u| u.comm_w)
    .chain(incoming.iter().map(|i| i.comm_w))
    .collect();
  let comm_w = comms
    .iter()
    .zip(&w)
    .skip(1)
    .fold(comms[0], |acc, (c, wi)| acc + *c * *wi);
  let mut idx: Vec<V::Index> = running.iter().map(|u| u.index.clone()).collect();
  idx.extend(incoming.iter().map(|i| V::incoming_index(pp, i.k)));
  let mut index = idx[0].clone();
  for (x, wi) in idx.iter().zip(&w).skip(1) {
    V::scale_add(&mut index, x, *wi);
  }
  let us: Vec<E::Scalar> = running
    .iter()
    .map(|u| u.u)
    .chain(incoming.iter().map(|_| E::Scalar::ONE))
    .collect();
  let u = us
    .iter()
    .zip(&w)
    .fold(E::Scalar::ZERO, |a, (x, wi)| a + *x * wi);
  let ios: Vec<&[E::Scalar]> = running
    .iter()
    .map(|u| u.io.as_slice())
    .chain(incoming.iter().map(|i| i.io.as_slice()))
    .collect();
  let claims: Vec<&[E::Scalar]> = p.eps.iter().chain(&p.theta).map(Vec::as_slice).collect();
  RunningInstance {
    comm_w,
    index,
    u,
    io: lincomb(&w, &ios),
    r_x: ch.r_x.clone(),
    r_y: ch.r_y.clone(),
    v: lincomb(&w, &claims),
  }
}

/// Folds the witnesses with the same weights: `W* = Σ ρ^i W_i`, `λ* = Σ ρ^i λ_i` (λ = e_k for
/// an incoming instance).
pub(crate) fn fold_witnesses<E: Engine>(
  pp: &HfsParams<E>,
  running_w: &[RunningWitness<E>],
  incoming: &[IncomingInstance<E>],
  incoming_w: &[Vec<E::Scalar>],
  rho: E::Scalar,
) -> RunningWitness<E> {
  let w = powers(rho, running_w.len() + incoming.len());
  let lambda_inc: Vec<Vec<E::Scalar>> = incoming.iter().map(|i| pp.e_k(i.k)).collect();
  let ws: Vec<&[E::Scalar]> = running_w
    .iter()
    .map(|x| x.w.as_slice())
    .chain(incoming_w.iter().map(Vec::as_slice))
    .collect();
  let ls: Vec<&[E::Scalar]> = running_w
    .iter()
    .map(|x| x.lambda.as_slice())
    .chain(lambda_inc.iter().map(Vec::as_slice))
    .collect();
  RunningWitness {
    w: lincomb(&w, &ws),
    lambda: lincomb(&w, &ls),
  }
}
