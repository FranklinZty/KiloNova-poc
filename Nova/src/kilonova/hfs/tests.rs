//! P3 acceptance tests for the v2 HFS (`docs/P3-plan.md`).
//!
//! Every positive fold is checked three ways: the bare verifier (its output must equal the
//! prover's), the native decider, and the independent P2 oracle `kn_ccs::accs::check_accs`
//! (which gets its own matrices from `kn_ccs` and a Pedersen `commit` closure) plus the index
//! opening.
use super::{
  nifs::{fold_witnesses, Tags},
  *,
};
use crate::{
  kilonova::transcript::{self, v2},
  provider::PallasEngine,
  r1cs::{R1CSShape, SparseMatrix},
  traits::{AbsorbInRO2Trait, Engine, RO2Constants, ROTrait},
  Commitment,
};
use ff::{Field, PrimeField};
use kn_ccs::{
  accs::check_accs,
  r#gen::{random_satisfiable, wiring_pair, PairTemplate},
  AccsInstance, Assignment, Ccs, Family, Template,
};
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};

type E = PallasEngine;
type F = <E as Engine>::Scalar;

fn bincode_bytes<T: serde::Serialize>(v: &T) -> Vec<u8> {
  bincode::serde::encode_to_vec(v, bincode::config::legacy()).unwrap()
}

// ---------------------------------------------------------------------------------------------
// Fixtures and the independent oracle
// ---------------------------------------------------------------------------------------------

fn hfs_shape(c: &Ccs<F>) -> CcsShape<F> {
  CcsShape::new(
    c.m,
    c.num_w,
    c.num_io,
    c.matrices.iter().map(|m| m.entries().to_vec()).collect(),
  )
  .unwrap()
}

fn hfs_template(t: &Template<F>) -> CcsTemplate<F> {
  CcsTemplate::new(t.t, t.multisets.clone(), t.coeffs.clone()).unwrap()
}

fn params_of(fam: &Family<F>) -> HfsParams<E> {
  let shapes = (0..fam.k()).map(|i| hfs_shape(fam.member(i))).collect();
  HfsParams::new(hfs_template(&fam.member(0).template), shapes).unwrap()
}

fn pair_family(tpl: PairTemplate, reps: usize) -> Family<F> {
  Family::new(
    (0..2)
      .map(|k| wiring_pair::<F>(tpl, k, reps, None).unwrap().0)
      .collect(),
  )
  .unwrap()
}

/// A fresh, satisfied incoming instance of predicate `k` of a wiring pair.
fn pair_input(
  pp: &HfsParams<E>,
  tpl: PairTemplate,
  k: usize,
  reps: usize,
  x: F,
) -> (IncomingInstance<E>, Vec<F>) {
  let (c, a) = wiring_pair(tpl, k, reps, Some(x)).unwrap();
  let a = a.unwrap();
  assert!(c.is_satisfied(&a.z()).is_ok());
  (
    IncomingInstance::new(pp, k, &a.w, a.io.clone()).unwrap(),
    a.w,
  )
}

/// The independent oracle: kn-ccs `check_accs` (Pedersen commitment) and the index opening.
fn oracle<V: Variant<E>>(
  pp: &HfsParams<E>,
  fam: &Family<F>,
  u: &RunningInstance<E, V>,
  w: &RunningWitness<E>,
) -> Result<(), String> {
  let accs = AccsInstance {
    comm_w: u.comm_w,
    u: u.u,
    io: u.io.clone(),
    lambda: w.lambda.clone(),
    r_x: u.r_x.clone(),
    r_y: u.r_y.clone(),
    v: u.v.clone(),
  };
  check_accs(fam, &accs, &w.w, |x| {
    pp.commit_w(x).expect("check_accs checks the length first")
  })
  .map_err(|e| format!("kn-ccs: {e}"))?;
  V::check_opening(pp, &u.index, &w.lambda).map_err(|e| format!("opening: {e}"))
}

type Run<V> = (RunningInstance<E, V>, RunningWitness<E>);
type Inc = (IncomingInstance<E>, Vec<F>);

/// Prove, verify (same instance and challenges), decide and run the oracle.
fn fold_checked<V: Variant<E>>(
  pp: &HfsParams<E>,
  fam: &Family<F>,
  running: &[Run<V>],
  incoming: &[Inc],
) -> (Run<V>, ProverOutput<E, V>) {
  let (ru, rw): (Vec<_>, Vec<_>) = running.iter().cloned().unzip();
  let (iu, iw): (Vec<_>, Vec<_>) = incoming.iter().cloned().unzip();
  let out = NIFS::<E, V>::prove(pp, &ru, &rw, &iu, &iw).unwrap();
  let (u, ch) = NIFS::<E, V>::verify(pp, &ru, &iu, &out.proof)
    .unwrap_or_else(|e| panic!("verifier rejected an honest fold: {e}"));
  assert_eq!(
    u, out.instance,
    "prover and verifier fold to the same instance"
  );
  assert_eq!(
    bincode_bytes(&ch),
    bincode_bytes(&out.challenges),
    "challenges agree byte for byte"
  );
  decide(pp, &u, &out.witness).unwrap_or_else(|e| panic!("decider rejected: {e}"));
  oracle(pp, fam, &u, &out.witness).unwrap_or_else(|e| panic!("oracle rejected: {e}"));
  ((u, out.witness.clone()), out)
}

// ---------------------------------------------------------------------------------------------
// 100-step alternating chains (closes B8/B10)
// ---------------------------------------------------------------------------------------------

fn run_chain<V: Variant<E>>(tpl: PairTemplate, steps: usize, reps: usize, seed: u64) {
  let fam = pair_family(tpl, reps);
  let pp = params_of(&fam);
  let mut rng = ChaCha20Rng::seed_from_u64(seed);
  let mut acc: Option<Run<V>> = None;
  for step in 0..steps {
    let k = step % 2;
    let inc = pair_input(&pp, tpl, k, reps, F::random(&mut rng));
    let running: Vec<Run<V>> = acc.iter().cloned().collect();
    let (next, _) = fold_checked(&pp, &fam, &running, &[inc]);
    acc = Some(next);
  }
  let (_, w) = acc.unwrap();
  // λ is a dense combination of both predicates, not one-hot.
  assert!(w.lambda.iter().all(|l| !bool::from(l.is_zero())));
  assert!(w.lambda.iter().all(|l| *l != F::ONE));
  println!(
    "[p3] v2 HFS {} {}: {steps} alternating steps (K = 2, reps = {reps}); verifier, decider and kn-ccs oracle accepted every step",
    V::NAME,
    tpl.name()
  );
}

#[test]
fn test_chain_100_r1cs_direct() {
  run_chain::<Direct>(PairTemplate::R1cs, 100, 1, 15);
}

#[test]
fn test_chain_100_r1cs_span() {
  run_chain::<Span>(PairTemplate::R1cs, 100, 1, 15);
}

#[test]
fn test_chain_100_power5_direct() {
  run_chain::<Direct>(PairTemplate::Power5, 100, 1, 16);
}

#[test]
fn test_chain_100_power5_span() {
  run_chain::<Span>(PairTemplate::Power5, 100, 1, 16);
}

/// Larger shapes (more sum-check rounds) for a shorter chain.
#[test]
fn test_chain_reps_both_templates() {
  for reps in [3, 8] {
    run_chain::<Direct>(PairTemplate::R1cs, 12, reps, 17);
    run_chain::<Span>(PairTemplate::Power5, 12, reps, 18);
  }
}

// ---------------------------------------------------------------------------------------------
// B15
// ---------------------------------------------------------------------------------------------

/// The B15 counter-example of `nifs::tests::test_known_issue_b15_scalar_r1cs_not_foldable_over_base`
/// (negative coefficient `(w0 − w1)·1 = 0`, wrapping product `w0·w0 = x0`, satisfied over
/// `E::Scalar`), taken from the same `R1CSShape`, folds in v2 over the native field. The v1 test
/// keeps documenting that v1 (and therefore the recursion path until P5) still rejects it.
fn b15_fold<V: Variant<E>>() {
  let one = F::ONE;
  let shape = R1CSShape::<E>::new(
    2,
    2,
    2,
    SparseMatrix::new(&[(0, 0, one), (0, 1, -one), (1, 0, one)], 2, 5),
    SparseMatrix::new(&[(0, 2, one), (1, 0, one)], 2, 5),
    SparseMatrix::new(&[(1, 3, one)], 2, 5),
  )
  .unwrap();
  // The oracle gets its own copy of the relation, built with kn-ccs.
  let kn = |t: &[(usize, usize, F)]| kn_ccs::SparseMatrix::from_triplets(2, 5, t.to_vec()).unwrap();
  let fam = Family::new(vec![Ccs::new(
    2,
    2,
    2,
    Template::r1cs(),
    vec![
      kn(&[(0, 0, one), (0, 1, -one), (1, 0, one)]),
      kn(&[(0, 2, one), (1, 0, one)]),
      kn(&[(1, 3, one)]),
    ],
  )
  .unwrap()])
  .unwrap();
  let pp = HfsParams::<E>::new(CcsTemplate::r1cs(), vec![CcsShape::from(&shape)]).unwrap();

  let mut rng = ChaCha20Rng::seed_from_u64(1515);
  let mut acc: Option<Run<V>> = None;
  for step in 0..10 {
    // x ≥ 2^252 (the v1 test uses (2^63)^4 + 7), so x·x wraps modulo the scalar field.
    let x = if step == 0 {
      F::from(1u64 << 63).pow_vartime([4]) + F::from(7u64)
    } else {
      F::random(&mut rng)
    };
    let a = Assignment {
      w: vec![x, x],
      io: vec![x * x, F::ZERO],
    };
    assert!(fam.member(0).is_satisfied(&a.z()).is_ok());
    let inc = (
      IncomingInstance::new(&pp, 0, &a.w, a.io.clone()).unwrap(),
      a.w.clone(),
    );
    let running: Vec<Run<V>> = acc.iter().cloned().collect();
    acc = Some(fold_checked(&pp, &fam, &running, &[inc]).0);
  }
}

#[test]
fn test_b15_instance_class_folds_in_v2() {
  b15_fold::<Direct>();
  b15_fold::<Span>();
}

// ---------------------------------------------------------------------------------------------
// μ / ν combinations
// ---------------------------------------------------------------------------------------------

fn mu_nu<V: Variant<E>>(tpl: PairTemplate, mu: usize, nu: usize, rng: &mut ChaCha20Rng) {
  let fam = pair_family(tpl, 2);
  let pp = params_of(&fam);
  // Running inputs: each from its own (0, 1) fold, then one (1, 1) fold to make λ dense.
  let running: Vec<Run<V>> = (0..mu)
    .map(|i| {
      let first = pair_input(&pp, tpl, i % 2, 2, F::random(&mut *rng));
      let (r, _) = fold_checked::<V>(&pp, &fam, &[], &[first]);
      let second = pair_input(&pp, tpl, (i + 1) % 2, 2, F::random(&mut *rng));
      fold_checked(&pp, &fam, &[r], &[second]).0
    })
    .collect();
  let incoming: Vec<Inc> = (0..nu)
    .map(|l| pair_input(&pp, tpl, (l + mu) % 2, 2, F::random(&mut *rng)))
    .collect();
  let (_, out) = fold_checked(&pp, &fam, &running, &incoming);
  assert_eq!(out.proof.sigma.len(), mu);
  assert_eq!(out.proof.tau.len(), nu);
}

#[test]
fn test_mu_nu_combinations() {
  let mut rng = ChaCha20Rng::seed_from_u64(42);
  for (mu, nu) in [
    (0, 1),
    (0, 2),
    (1, 0),
    (1, 1),
    (1, 2),
    (2, 0),
    (2, 1),
    (2, 2),
    (3, 2),
  ] {
    for tpl in [PairTemplate::R1cs, PairTemplate::Power5] {
      mu_nu::<Direct>(tpl, mu, nu, &mut rng);
      mu_nu::<Span>(tpl, mu, nu, &mut rng);
    }
  }
}

// ---------------------------------------------------------------------------------------------
// Explicit rejection of mismatched counts, lengths and degrees (Input layer)
// ---------------------------------------------------------------------------------------------

/// One honest (1, 1) fold of a wiring pair: (pp, fam, running, incoming, prover output).
struct Setup<V: Variant<E>> {
  pp: HfsParams<E>,
  fam: Family<F>,
  run: Run<V>,
  inc: Inc,
  out: ProverOutput<E, V>,
}

fn setup<V: Variant<E>>(tpl: PairTemplate, reps: usize, seed: u64) -> Setup<V> {
  let fam = pair_family(tpl, reps);
  let pp = params_of(&fam);
  let mut rng = ChaCha20Rng::seed_from_u64(seed);
  let first = pair_input(&pp, tpl, 0, reps, F::random(&mut rng));
  let (r0, _) = fold_checked::<V>(&pp, &fam, &[], &[first]);
  let second = pair_input(&pp, tpl, 1, reps, F::random(&mut rng));
  let (run, _) = fold_checked(&pp, &fam, &[r0], &[second]);
  let inc = pair_input(&pp, tpl, 0, reps, F::random(&mut rng));
  let (_, out) = fold_checked(
    &pp,
    &fam,
    std::slice::from_ref(&run),
    std::slice::from_ref(&inc),
  );
  Setup {
    pp,
    fam,
    run,
    inc,
    out,
  }
}

fn expect_input(res: Result<impl Sized, HfsError>, what: &str) -> HfsError {
  match res {
    Ok(_) => panic!("{what}: accepted"),
    Err(e) => {
      assert_eq!(e.layer(), Layer::Input, "{what}: {e}");
      e
    }
  }
}

fn mismatches<V: Variant<E>>() {
  let st = setup::<V>(PairTemplate::R1cs, 2, 7);
  let (pp, p) = (&st.pp, &st.out.proof);
  let (u1, w1) = &st.run;
  let (u2, w2) = &st.inc;
  let ver = |run: &[RunningInstance<E, V>], inc: &[IncomingInstance<E>], p: &HfsProof<E>| {
    NIFS::<E, V>::verify(pp, run, inc, p)
  };
  let one_run = std::slice::from_ref(u1);
  let one_inc = std::slice::from_ref(u2);
  assert!(ver(one_run, one_inc, p).is_ok());

  // Input counts.
  expect_input(
    ver(&[u1.clone(), u1.clone()], one_inc, p),
    "mu = 2 for a mu = 1 proof",
  );
  expect_input(ver(&[], one_inc, p), "mu = 0 for a mu = 1 proof");
  expect_input(
    ver(one_run, &[u2.clone(), u2.clone()], p),
    "nu = 2 for a nu = 1 proof",
  );
  expect_input(ver(one_run, &[], p), "nu = 0 for a nu = 1 proof");
  expect_input(ver(&[], &[], p), "mu = nu = 0");
  expect_input(
    NIFS::<E, V>::prove(pp, &[], &[], &[], &[]),
    "prove with mu = nu = 0",
  );
  expect_input(
    NIFS::<E, V>::prove(pp, one_run, &[], one_inc, std::slice::from_ref(w2)),
    "missing running witness",
  );
  expect_input(
    NIFS::<E, V>::prove(pp, one_run, std::slice::from_ref(w1), one_inc, &[]),
    "missing incoming witness",
  );

  // Instance lengths.
  let mut bad = u1.clone();
  bad.io.push(F::ONE);
  expect_input(ver(&[bad], one_inc, p), "running io too long");
  let mut bad = u1.clone();
  bad.r_x.pop();
  expect_input(ver(&[bad], one_inc, p), "running r_x too short");
  let mut bad = u1.clone();
  bad.r_y.push(F::ONE);
  expect_input(ver(&[bad], one_inc, p), "running r_y too long");
  let mut bad = u1.clone();
  bad.v.pop();
  expect_input(ver(&[bad], one_inc, p), "running v too short");
  // (Index lengths are variant-specific; see `test_rejects_mismatched_shapes`.)
  let mut inc_bad = u2.clone();
  inc_bad.io.pop();
  expect_input(ver(one_run, &[inc_bad], p), "incoming io too short");
  let mut inc_bad = u2.clone();
  inc_bad.k = pp.k();
  assert!(matches!(
    expect_input(ver(one_run, &[inc_bad], p), "predicate id = K"),
    HfsError::PredicateId { .. }
  ));

  // Witness lengths.
  let mut w_bad = w1.clone();
  w_bad.w.pop();
  expect_input(
    NIFS::<E, V>::prove(pp, one_run, &[w_bad], one_inc, std::slice::from_ref(w2)),
    "running witness too short",
  );
  let mut w_bad = w1.clone();
  w_bad.lambda.push(F::ONE);
  expect_input(
    NIFS::<E, V>::prove(pp, one_run, &[w_bad], one_inc, std::slice::from_ref(w2)),
    "running lambda too long",
  );
  let mut iw_bad = w2.clone();
  iw_bad.push(F::ONE);
  expect_input(
    NIFS::<E, V>::prove(pp, one_run, std::slice::from_ref(w1), one_inc, &[iw_bad]),
    "incoming witness too long",
  );
  expect_input(pp.commit_w(&[F::ONE; 64]), "commit to a too-long witness");
  expect_input(
    decide(
      pp,
      u1,
      &RunningWitness {
        w: vec![],
        lambda: w1.lambda.clone(),
      },
    ),
    "decider witness length",
  );

  // Proof shape: rounds, degrees, claim counts.
  let mut q = p.clone();
  q.sc_x[0].push(F::ONE);
  expect_input(ver(one_run, one_inc, &q), "X round with degree d + 2");
  let mut q = p.clone();
  q.sc_x[0].pop();
  expect_input(ver(one_run, one_inc, &q), "X round with degree d");
  let mut q = p.clone();
  q.sc_y.pop();
  expect_input(ver(one_run, one_inc, &q), "missing Y round");
  let mut q = p.clone();
  q.sc_y[1].push(F::ONE);
  expect_input(ver(one_run, one_inc, &q), "Y round with degree 3");
  let mut q = p.clone();
  q.sigma[0].pop();
  expect_input(ver(one_run, one_inc, &q), "sigma too short");
  let mut q = p.clone();
  q.tau.push(q.tau[0].clone());
  expect_input(ver(one_run, one_inc, &q), "tau for two inputs");
  let mut q = p.clone();
  q.eps[0].push(F::ONE);
  expect_input(ver(one_run, one_inc, &q), "eps too long");
  let mut q = p.clone();
  q.theta.clear();
  expect_input(ver(one_run, one_inc, &q), "theta missing");
}

#[test]
fn test_rejects_mismatched_shapes() {
  mismatches::<Direct>();
  mismatches::<Span>();

  // Index lengths (variant-specific).
  let st = setup::<Direct>(PairTemplate::R1cs, 1, 8);
  let mut bad = st.run.0.clone();
  bad.index.pop();
  expect_input(
    NIFS::<E, Direct>::verify(
      &st.pp,
      &[bad],
      std::slice::from_ref(&st.inc.0),
      &st.out.proof,
    ),
    "comm_M with t - 1 entries",
  );
  let st = setup::<Span>(PairTemplate::R1cs, 1, 8);
  let mut bad = st.run.0.clone();
  bad.index.push(F::ONE);
  expect_input(
    NIFS::<E, Span>::verify(
      &st.pp,
      &[bad],
      std::slice::from_ref(&st.inc.0),
      &st.out.proof,
    ),
    "lambda with K + 1 entries",
  );

  // Degree mismatch: a proof made under power(3) does not verify under power(5) parameters
  // with the same matrices; it is rejected for its round-polynomial degree.
  let fam5 = pair_family(PairTemplate::Power5, 1);
  let pp5 = params_of(&fam5);
  let shapes: Vec<CcsShape<F>> = pp5.shapes().to_vec();
  let pp3 = HfsParams::<E>::new(CcsTemplate::power(3).unwrap(), shapes).unwrap();
  let mut rng = ChaCha20Rng::seed_from_u64(9);
  let (inc, w) = pair_input(&pp3, PairTemplate::Power5, 0, 1, F::random(&mut rng));
  let out3 = NIFS::<E, Direct>::prove(&pp3, &[], &[], std::slice::from_ref(&inc), &[w]).unwrap();
  let e = expect_input(
    NIFS::<E, Direct>::verify(&pp5, &[], &[inc], &out3.proof),
    "degree-3 proof under a degree-5 template",
  );
  assert!(e.to_string().contains("sc_x"), "{e}");

  // Parameter validation.
  let c0 = hfs_shape(fam5.member(0));
  let r1 = hfs_shape(pair_family(PairTemplate::R1cs, 1).member(0));
  let r2 = hfs_shape(pair_family(PairTemplate::R1cs, 2).member(0));
  let err = |r: Result<HfsParams<E>, HfsError>| r.err().expect("rejected");
  assert!(matches!(
    err(HfsParams::new(CcsTemplate::r1cs(), vec![])),
    HfsError::InvalidFamily(_)
  ));
  assert!(matches!(
    err(HfsParams::new(CcsTemplate::r1cs(), vec![r1.clone(), r2])),
    HfsError::InvalidFamily(_)
  ));
  assert!(matches!(
    err(HfsParams::new(CcsTemplate::r1cs(), vec![r1, c0])),
    HfsError::InvalidFamily(_)
  ));
  assert!(matches!(
    CcsTemplate::<F>::new(2, vec![vec![0, 2]], vec![F::ONE]),
    Err(HfsError::InvalidTemplate(_))
  ));
  assert!(matches!(
    CcsTemplate::<F>::new(2, vec![vec![]], vec![F::ONE]),
    Err(HfsError::InvalidTemplate(_))
  ));
  assert!(matches!(
    CcsTemplate::<F>::new(2, vec![vec![0]], vec![]),
    Err(HfsError::Shape { .. })
  ));
  assert!(matches!(
    CcsTemplate::<F>::power(0),
    Err(HfsError::InvalidTemplate(_))
  ));
  assert!(matches!(
    CcsShape::<F>::new(2, 1, 1, vec![vec![(2, 0, F::ONE)]]),
    Err(HfsError::InvalidFamily(_))
  ));
  assert!(matches!(
    CcsShape::<F>::new(2, 1, 1, vec![vec![(0, 3, F::ONE)]]),
    Err(HfsError::InvalidFamily(_))
  ));
}

// ---------------------------------------------------------------------------------------------
// Challenges, serialisation, transcript encoding
// ---------------------------------------------------------------------------------------------

#[test]
fn test_challenges_agree_bytewise() {
  fn run<V: Variant<E>>() {
    for tpl in [PairTemplate::R1cs, PairTemplate::Power5] {
      let st = setup::<V>(tpl, 3, 11);
      let (u, ch) = NIFS::<E, V>::verify(
        &st.pp,
        std::slice::from_ref(&st.run.0),
        std::slice::from_ref(&st.inc.0),
        &st.out.proof,
      )
      .unwrap();
      assert_eq!(bincode_bytes(&ch), bincode_bytes(&st.out.challenges));
      assert_eq!(bincode_bytes(&u), bincode_bytes(&st.out.instance));
      // Every challenge is at most 128 bits.
      let all: Vec<F> = [ch.gamma, ch.delta, ch.rho]
        .into_iter()
        .chain(ch.alpha.iter().copied())
        .chain(ch.r_x.iter().copied())
        .chain(ch.r_y.iter().copied())
        .collect();
      for c in all {
        assert!(c.to_repr().as_ref()[16..].iter().all(|b| *b == 0));
      }
      // Serialisation round trip of proof and instance.
      let pb = bincode_bytes(&st.out.proof);
      let (p2, n): (HfsProof<E>, usize) =
        bincode::serde::decode_from_slice(&pb, bincode::config::legacy()).unwrap();
      assert_eq!((p2, n), (st.out.proof.clone(), pb.len()));
      let ub = bincode_bytes(&st.out.instance);
      let (u2, _): (RunningInstance<E, V>, usize) =
        bincode::serde::decode_from_slice(&ub, bincode::config::legacy()).unwrap();
      assert_eq!(u2, st.out.instance);
    }
  }
  run::<Direct>();
  run::<Span>();
}

/// The v2 commitment absorption (4 × 64-bit limbs per coordinate, then the infinity flag) is
/// the encoding of `Commitment::absorb_in_ro2`, and differs from absorbing in another order.
#[test]
fn test_commitment_absorption_matches_ro2() {
  let fam = pair_family(PairTemplate::R1cs, 1);
  let pp = params_of(&fam);
  let consts = RO2Constants::<E>::default();
  for c in pp
    .iota(0)
    .iter()
    .chain(pp.iota(1))
    .copied()
    .chain([Commitment::<E>::default()])
  {
    let mut a = <E as Engine>::RO2::new(consts.clone());
    let mut b = <E as Engine>::RO2::new(consts.clone());
    v2::absorb_commitment::<E>(&mut a, &c);
    c.absorb_in_ro2(&mut b);
    assert_eq!(a.squeeze(128), b.squeeze(128));
  }
  assert_eq!(v2::COMMITMENT_ABSORB_LEN, 9);
  assert_eq!(v2::HFS_TRANSCRIPT_VERSION, 2);
  assert_eq!(transcript::HFS_TRANSCRIPT_VERSION, 1, "v1 path unchanged");
  let tags = [
    v2::TAG_INPUT_DIRECT,
    v2::TAG_INPUT_SPAN,
    v2::TAG_X_CLAIMS,
    v2::TAG_Y_CLAIMS,
  ];
  for (i, t) in tags.iter().enumerate() {
    assert_eq!(t >> 16, 0x4b4e_4846_5302, "KNHFS v2 prefix");
    assert_eq!(t & 0xffff, i as u64 + 1);
  }
}

// ---------------------------------------------------------------------------------------------
// Negative tests with the detection layer
// ---------------------------------------------------------------------------------------------

/// Verifier, then the decider on the witness folded with the verifier's ρ. The kn-ccs oracle
/// must agree with the decider whenever the verifier accepts.
#[allow(clippy::too_many_arguments)]
fn full_check<V: Variant<E>>(
  pp: &HfsParams<E>,
  fam: &Family<F>,
  run: &[Run<V>],
  inc: &[Inc],
  proof: &HfsProof<E>,
  tags: &Tags,
) -> Result<(), HfsError> {
  let (ru, rw): (Vec<_>, Vec<_>) = run.iter().cloned().unzip();
  let (iu, iw): (Vec<_>, Vec<_>) = inc.iter().cloned().unzip();
  let (u, ch) = NIFS::<E, V>::verify_with_tags(pp, &ru, &iu, proof, tags)?;
  let w = fold_witnesses(pp, &rw, &iu, &iw, ch.rho);
  let d = decide(pp, &u, &w);
  let o = oracle(pp, fam, &u, &w);
  assert_eq!(
    d.is_ok(),
    o.is_ok(),
    "decider and oracle disagree: {d:?} vs {o:?}"
  );
  d
}

struct Report {
  rows: Vec<(String, Layer, String)>,
}

impl Report {
  fn reject(&mut self, case: impl Into<String>, expected: Layer, res: Result<(), HfsError>) {
    let case = case.into();
    match res {
      Ok(()) => panic!("{case}: accepted (expected rejection at {expected:?})"),
      Err(e) => {
        assert_eq!(e.layer(), expected, "{case}: {e}");
        self.rows.push((case, e.layer(), e.to_string()));
      }
    }
  }
}

fn negative_matrix<V: Variant<E>>(tpl: PairTemplate, report: &mut Report) {
  let st = setup::<V>(tpl, 2, 21);
  let (pp, fam) = (&st.pp, &st.fam);
  let p = &st.out.proof;
  let tags = Tags::of::<E, V>();
  let run = std::slice::from_ref(&st.run);
  let inc = std::slice::from_ref(&st.inc);
  let pre = format!("{} {}", V::NAME, tpl.name());
  let check =
    |run: &[Run<V>], inc: &[Inc], q: &HfsProof<E>| full_check(pp, fam, run, inc, q, &tags);
  assert!(check(run, inc, p).is_ok());
  let t = pp.t();
  let delta = st.out.challenges.delta;

  // Sum-check coefficients: every evaluation of every round.
  for (r, msg) in p.sc_x.iter().enumerate() {
    for e in 0..msg.len() {
      let mut q = p.clone();
      q.sc_x[r][e] += F::ONE;
      report.reject(
        format!("{pre}: sc_x[{r}][{e}] + 1"),
        Layer::Verifier,
        check(run, inc, &q),
      );
    }
  }
  for (r, msg) in p.sc_y.iter().enumerate() {
    for e in 0..msg.len() {
      let mut q = p.clone();
      q.sc_y[r][e] += F::ONE;
      report.reject(
        format!("{pre}: sc_y[{r}][{e}] + 1"),
        Layer::Verifier,
        check(run, inc, &q),
      );
    }
  }
  // Helper claims (plain tampering).
  for j in 0..t {
    let mut q = p.clone();
    q.sigma[0][j] += F::ONE;
    report.reject(
      format!("{pre}: sigma[0][{j}] + 1"),
      Layer::Verifier,
      check(run, inc, &q),
    );
    let mut q = p.clone();
    q.tau[0][j] += F::ONE;
    report.reject(
      format!("{pre}: tau[0][{j}] + 1"),
      Layer::Verifier,
      check(run, inc, &q),
    );
  }
  for j in 0..=t {
    let mut q = p.clone();
    q.eps[0][j] += F::ONE;
    report.reject(
      format!("{pre}: eps[0][{j}] + 1"),
      Layer::Verifier,
      check(run, inc, &q),
    );
    let mut q = p.clone();
    q.theta[0][j] += F::ONE;
    report.reject(
      format!("{pre}: theta[0][{j}] + 1"),
      Layer::Verifier,
      check(run, inc, &q),
    );
  }

  // Deferred claims: compensated tampering keeps c_y, passes the bare verifier and must be
  // caught by the decider.
  let d = F::from(5);
  let mut q = p.clone();
  q.eps[0][0] += delta * d;
  q.eps[0][1] -= d;
  assert!(NIFS::<E, V>::verify(
    pp,
    std::slice::from_ref(&st.run.0),
    std::slice::from_ref(&st.inc.0),
    &q
  )
  .is_ok());
  report.reject(
    format!("{pre}: eps[0][0..2] compensated (keeps c_y)"),
    Layer::Decider,
    check(run, inc, &q),
  );
  let mut q = p.clone();
  q.eps[0][t] += d;
  q.eps[0][t - 1] -= delta * d;
  assert!(NIFS::<E, V>::verify(
    pp,
    std::slice::from_ref(&st.run.0),
    std::slice::from_ref(&st.inc.0),
    &q
  )
  .is_ok());
  report.reject(
    format!("{pre}: eps[0][t-1..=t] compensated (z-claim)"),
    Layer::Decider,
    check(run, inc, &q),
  );
  let mut q = p.clone();
  q.theta[0][0] += delta * d;
  q.theta[0][1] -= d;
  assert!(NIFS::<E, V>::verify(
    pp,
    std::slice::from_ref(&st.run.0),
    std::slice::from_ref(&st.inc.0),
    &q
  )
  .is_ok());
  report.reject(
    format!("{pre}: theta[0][0..2] compensated (keeps c_y)"),
    Layer::Decider,
    check(run, inc, &q),
  );

  // Incoming instance: commitment, io, predicate id (after the proof was made).
  let other = st.run.0.comm_w;
  let mut i2 = st.inc.clone();
  i2.0.comm_w = other;
  report.reject(
    format!("{pre}: incoming comm_W replaced"),
    Layer::Verifier,
    check(run, &[i2], p),
  );
  let mut i2 = st.inc.clone();
  i2.0.io[0] += F::ONE;
  report.reject(
    format!("{pre}: incoming io[0] + 1"),
    Layer::Verifier,
    check(run, &[i2], p),
  );
  let mut i2 = st.inc.clone();
  i2.0.k = 1 - i2.0.k;
  report.reject(
    format!("{pre}: incoming predicate id flipped"),
    Layer::Verifier,
    check(run, &[i2], p),
  );

  // Running instance (after the proof was made).
  let tamper_run = |f: &dyn Fn(&mut RunningInstance<E, V>)| {
    let mut r = st.run.clone();
    f(&mut r.0);
    check(&[r], inc, p)
  };
  report.reject(
    format!("{pre}: running comm_W replaced"),
    Layer::Verifier,
    tamper_run(&|u| u.comm_w = st.inc.0.comm_w),
  );
  report.reject(
    format!("{pre}: running index replaced by the incoming one"),
    Layer::Verifier,
    tamper_run(&|u| u.index = V::incoming_index(pp, 1)),
  );
  report.reject(
    format!("{pre}: running u + 1"),
    Layer::Verifier,
    tamper_run(&|u| u.u += F::ONE),
  );
  report.reject(
    format!("{pre}: running io[1] + 1"),
    Layer::Verifier,
    tamper_run(&|u| u.io[1] += F::ONE),
  );
  report.reject(
    format!("{pre}: running r_x[0] + 1"),
    Layer::Verifier,
    tamper_run(&|u| u.r_x[0] += F::ONE),
  );
  report.reject(
    format!("{pre}: running r_y[0] + 1"),
    Layer::Verifier,
    tamper_run(&|u| u.r_y[0] += F::ONE),
  );
  report.reject(
    format!("{pre}: running v[t] + 1"),
    Layer::Verifier,
    tamper_run(&|u| u.v[t] += F::ONE),
  );

  // Field order: the v1 reversed point convention, swapped io entries, swapped claims, swapped
  // rounds.
  report.reject(
    format!("{pre}: running r_y reversed (v1 order)"),
    Layer::Verifier,
    tamper_run(&|u| u.r_y.reverse()),
  );
  let mut i2 = st.inc.clone();
  i2.0.io.swap(0, 1);
  report.reject(
    format!("{pre}: incoming io entries swapped"),
    Layer::Verifier,
    check(run, &[i2], p),
  );
  let mut q = p.clone();
  q.sigma[0].swap(0, 1);
  report.reject(
    format!("{pre}: sigma entries swapped"),
    Layer::Verifier,
    check(run, inc, &q),
  );
  let mut q = p.clone();
  q.sc_y.swap(0, 1);
  report.reject(
    format!("{pre}: Y rounds swapped"),
    Layer::Verifier,
    check(run, inc, &q),
  );

  // Transcript tags: prover and verifier disagree on a tag. The prover keeps the witness it
  // folded with its own ρ, so the decider runs on (verifier's instance, prover's witness).
  // A different input or x-claims tag changes the sum-check challenges and is rejected by the
  // verifier. The y-claims tag only feeds ρ: the verifier accepts and folds with another ρ, and
  // the mismatch is caught by the decider (comm_W of the verifier's instance does not open to
  // the prover's witness).
  let with_prover_witness = |ptags: &Tags, vtags: &Tags| -> Result<(), HfsError> {
    let out = NIFS::<E, V>::prove_with_tags(
      pp,
      std::slice::from_ref(&st.run.0),
      std::slice::from_ref(&st.run.1),
      std::slice::from_ref(&st.inc.0),
      std::slice::from_ref(&st.inc.1),
      ptags,
    )
    .unwrap();
    let (u, _) = NIFS::<E, V>::verify_with_tags(
      pp,
      std::slice::from_ref(&st.run.0),
      std::slice::from_ref(&st.inc.0),
      &out.proof,
      vtags,
    )?;
    let d = decide(pp, &u, &out.witness);
    assert_eq!(d.is_ok(), oracle(pp, fam, &u, &out.witness).is_ok());
    d
  };
  assert!(with_prover_witness(&tags, &tags).is_ok());
  let v1 = [
    transcript::HFS_TAG_INPUT,
    transcript::HFS_TAG_X_CLAIMS,
    transcript::HFS_TAG_Y_CLAIMS,
  ];
  for (i, name) in ["input", "x_claims", "y_claims"].iter().enumerate() {
    let mut tg = tags;
    match i {
      0 => tg.input = v1[0],
      1 => tg.x_claims = v1[1],
      _ => tg.y_claims = v1[2],
    }
    let layer = if i == 2 {
      Layer::Decider
    } else {
      Layer::Verifier
    };
    report.reject(
      format!("{pre}: verifier tag {name} = v1 value"),
      layer,
      with_prover_witness(&tags, &tg),
    );
    report.reject(
      format!("{pre}: prover tag {name} = v1 value"),
      layer,
      with_prover_witness(&tg, &tags),
    );
  }
  let mut tg = tags;
  tg.input = if tags.input == v2::TAG_INPUT_DIRECT {
    v2::TAG_INPUT_SPAN
  } else {
    v2::TAG_INPUT_DIRECT
  };
  report.reject(
    format!("{pre}: verifier input tag of the other variant"),
    Layer::Verifier,
    with_prover_witness(&tags, &tg),
  );

  // Honest proofs over inconsistent inputs pass the bare verifier and fail at the decider.
  let honest = |run: &[Run<V>], inc: &[Inc]| {
    let (ru, rw): (Vec<_>, Vec<_>) = run.iter().cloned().unzip();
    let (iu, iw): (Vec<_>, Vec<_>) = inc.iter().cloned().unzip();
    let q = NIFS::<E, V>::prove(pp, &ru, &rw, &iu, &iw).unwrap().proof;
    check(run, inc, &q)
  };
  let mut r = st.run.clone();
  r.0.comm_w = st.inc.0.comm_w;
  report.reject(
    format!("{pre}: running comm_W inconsistent, honestly proved"),
    Layer::Decider,
    honest(&[r], inc),
  );
  let mut r = st.run.clone();
  r.0.index = V::incoming_index(pp, 1);
  report.reject(
    format!("{pre}: running index inconsistent, honestly proved"),
    Layer::Decider,
    honest(&[r], inc),
  );
  let mut i2 = st.inc.clone();
  i2.0.comm_w = st.run.0.comm_w;
  report.reject(
    format!("{pre}: incoming comm_W inconsistent, honestly proved"),
    Layer::Decider,
    honest(run, &[i2]),
  );
  let mut r = st.run.clone();
  r.0.v[0] += F::ONE;
  report.reject(
    format!("{pre}: running v[0] wrong, honestly proved"),
    Layer::Verifier,
    honest(&[r], inc),
  );

  // Unsatisfied incoming witness: the honest prover's proof fails at X round 0.
  let mut i2 = st.inc.clone();
  i2.0.io[1] += F::ONE;
  let res = honest(run, &[i2]);
  assert_eq!(
    res,
    Err(HfsError::SumcheckRound {
      phase: Phase::X,
      round: 0
    })
  );
  report.reject(
    format!("{pre}: unsatisfied incoming witness"),
    Layer::Verifier,
    res,
  );

  // Tampered fold output (instance or witness): decider and oracle.
  let (u, w) = (&st.out.instance, &st.out.witness);
  let both = |u: &RunningInstance<E, V>, w: &RunningWitness<E>| {
    let d = decide(pp, u, w);
    assert!(
      oracle(pp, fam, u, w).is_err(),
      "oracle accepted a tampered output"
    );
    d.map(|_| ())
  };
  let mut u2 = u.clone();
  u2.v[0] += F::ONE;
  report.reject(
    format!("{pre}: output v[0] + 1"),
    Layer::Decider,
    both(&u2, w),
  );
  let mut u2 = u.clone();
  u2.u += F::ONE;
  report.reject(format!("{pre}: output u + 1"), Layer::Decider, both(&u2, w));
  let mut u2 = u.clone();
  u2.io[0] += F::ONE;
  report.reject(
    format!("{pre}: output io[0] + 1"),
    Layer::Decider,
    both(&u2, w),
  );
  let mut u2 = u.clone();
  u2.r_x[0] += F::ONE;
  report.reject(
    format!("{pre}: output r_x[0] + 1"),
    Layer::Decider,
    both(&u2, w),
  );
  let mut w2 = w.clone();
  w2.w[0] += F::ONE;
  report.reject(
    format!("{pre}: output W[0] + 1"),
    Layer::Decider,
    both(u, &w2),
  );
  let mut w2 = w.clone();
  w2.lambda[0] += F::ONE;
  report.reject(
    format!("{pre}: output lambda[0] + 1"),
    Layer::Decider,
    both(u, &w2),
  );
}

#[test]
fn test_negative_matrix() {
  let mut report = Report { rows: Vec::new() };
  for tpl in [PairTemplate::R1cs, PairTemplate::Power5] {
    negative_matrix::<Direct>(tpl, &mut report);
    negative_matrix::<Span>(tpl, &mut report);
  }
  println!(
    "[p3] negative tests ({} cases): case | layer | error",
    report.rows.len()
  );
  for (case, layer, err) in &report.rows {
    println!("[p3]   {case} | {layer:?} | {err}");
  }
  let count = |l: Layer| report.rows.iter().filter(|r| r.1 == l).count();
  println!(
    "[p3] by layer: verifier {}, decider {}",
    count(Layer::Verifier),
    count(Layer::Decider)
  );
}

/// A field element ≥ the modulus in the serialised proof is rejected when the proof is read.
#[test]
fn test_noncanonical_field_element_rejected() {
  let st = setup::<Direct>(PairTemplate::R1cs, 1, 31);
  let bytes = bincode_bytes(&st.out.proof);
  let target = st.out.proof.sc_x[0][0].to_repr();
  let pos = bytes
    .windows(32)
    .position(|w| w == target.as_ref())
    .expect("the scalar is serialised as its 32-byte representation");
  // p = (p − 1) + 1, little-endian.
  let mut p_bytes: Vec<u8> = (-F::ONE).to_repr().as_ref().to_vec();
  for b in p_bytes.iter_mut() {
    let (v, carry) = b.overflowing_add(1);
    *b = v;
    if !carry {
      break;
    }
  }
  let mut bad = bytes.clone();
  bad[pos..pos + 32].copy_from_slice(&p_bytes);
  let res: Result<(HfsProof<E>, usize), _> =
    bincode::serde::decode_from_slice(&bad, bincode::config::legacy());
  assert!(res.is_err(), "non-canonical scalar accepted");
}

// ---------------------------------------------------------------------------------------------
// Fixed test vectors (transcript v2)
// ---------------------------------------------------------------------------------------------

fn vector_text<V: Variant<E>>(tpl: PairTemplate) -> String {
  let fam = pair_family(tpl, 1);
  let pp = params_of(&fam);
  let a = pair_input(&pp, tpl, 0, 1, F::from(3));
  let (r0, out0) = fold_checked::<V>(&pp, &fam, &[], &[a]);
  let b = pair_input(&pp, tpl, 1, 1, F::from(5));
  let (_, out1) = fold_checked(&pp, &fam, &[r0], &[b]);
  let h = |f: &F| hex::encode(f.to_repr().as_ref());
  let mut s = String::new();
  s.push_str(&format!(
    "# HFS transcript v{} test vector: variant {}, template {}, wiring pair reps = 1.\n",
    v2::HFS_TRANSCRIPT_VERSION,
    V::NAME,
    tpl.name()
  ));
  s.push_str(
    "# Fold 0: (mu, nu) = (0, 1), predicate 0, x = 3. Fold 1: (1, 1), predicate 1, x = 5.\n",
  );
  s.push_str("# Scalars are little-endian 32-byte representations; blobs are bincode (legacy).\n");
  s.push_str(&format!("digest {}\n", h(&pp.digest())));
  for (i, out) in [&out0, &out1].iter().enumerate() {
    let c = &out.challenges;
    s.push_str(&format!("fold{i}.gamma {}\n", h(&c.gamma)));
    for (j, x) in c.alpha.iter().enumerate() {
      s.push_str(&format!("fold{i}.alpha[{j}] {}\n", h(x)));
    }
    for (j, x) in c.r_x.iter().enumerate() {
      s.push_str(&format!("fold{i}.r_x[{j}] {}\n", h(x)));
    }
    s.push_str(&format!("fold{i}.delta {}\n", h(&c.delta)));
    for (j, x) in c.r_y.iter().enumerate() {
      s.push_str(&format!("fold{i}.r_y[{j}] {}\n", h(x)));
    }
    s.push_str(&format!("fold{i}.rho {}\n", h(&c.rho)));
    s.push_str(&format!(
      "fold{i}.proof {}\n",
      hex::encode(bincode_bytes(&out.proof))
    ));
    s.push_str(&format!(
      "fold{i}.instance {}\n",
      hex::encode(bincode_bytes(&out.instance))
    ));
  }
  s
}

/// Compares against the checked-in vector `Nova/src/kilonova/hfs/vectors/<name>`.
/// `KN_UPDATE_VECTORS=1` rewrites it; that is only legitimate together with a transcript
/// version bump (`docs/protocol-spec.md` §8).
fn check_vector(name: &str, actual: &str) {
  let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("src/kilonova/hfs/vectors")
    .join(name);
  if std::env::var_os("KN_UPDATE_VECTORS").is_some() {
    std::fs::write(&path, actual).unwrap();
    return;
  }
  let expected = std::fs::read_to_string(&path)
    .unwrap_or_else(|e| panic!("missing test vector {}: {e}", path.display()));
  assert!(
    expected == actual,
    "HFS v2 test vector {name} changed; a transcript or protocol change needs a version bump.\n--- expected\n{expected}\n--- actual\n{actual}"
  );
}

#[test]
fn test_vectors_v2_direct_r1cs() {
  check_vector(
    "v2_direct_r1cs.txt",
    &vector_text::<Direct>(PairTemplate::R1cs),
  );
}

#[test]
fn test_vectors_v2_span_r1cs() {
  check_vector("v2_span_r1cs.txt", &vector_text::<Span>(PairTemplate::R1cs));
}

#[test]
fn test_vectors_v2_direct_power5() {
  check_vector(
    "v2_direct_power5.txt",
    &vector_text::<Direct>(PairTemplate::Power5),
  );
}

#[test]
fn test_vectors_v2_span_power5() {
  check_vector(
    "v2_span_power5.txt",
    &vector_text::<Span>(PairTemplate::Power5),
  );
}

// ---------------------------------------------------------------------------------------------
// Property tests (deterministic proptest runner)
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Case {
  template: usize,
  k: usize,
  m: usize,
  num_w: usize,
  num_io: usize,
  mu: usize,
  nu: usize,
  seed: u64,
}

fn case_strategy() -> impl proptest::strategy::Strategy<Value = Case> {
  use proptest::prelude::*;
  (
    0usize..9,
    1usize..4,
    1usize..7,
    0usize..5,
    0usize..4,
    0usize..3,
    0usize..3,
    any::<u64>(),
  )
    .prop_filter("mu + nu >= 1", |c| c.5 + c.6 >= 1)
    .prop_map(|(template, k, m, num_w, num_io, mu, nu, seed)| Case {
      template,
      k,
      m,
      num_w,
      num_io,
      mu,
      nu,
      seed,
    })
}

fn case_template(i: usize) -> Template<F> {
  match i {
    0 => Template::r1cs(),
    1..=5 => Template::power(i + 1),
    _ => Template::product(i - 4),
  }
}

/// Random satisfiable family members and their assignments.
fn random_family(c: &Case) -> (Family<F>, Vec<Assignment<F>>) {
  let mut rng = ChaCha20Rng::seed_from_u64(c.seed);
  let tpl = case_template(c.template);
  let (members, assignments): (Vec<_>, Vec<_>) = (0..c.k)
    .map(|_| random_satisfiable(&tpl, c.m, c.num_w, c.num_io, 2, &mut rng).unwrap())
    .unzip();
  (Family::new(members).unwrap(), assignments)
}

fn random_fold<V: Variant<E>>(c: &Case) -> (HfsParams<E>, Family<F>, Vec<Run<V>>, Vec<Inc>) {
  let (fam, asg) = random_family(c);
  let pp = params_of(&fam);
  let mut rng = ChaCha20Rng::seed_from_u64(c.seed ^ 0x5eed);
  let mut pick = || (rng.next_u32() as usize) % c.k;
  let inc_of = |k: usize| {
    (
      IncomingInstance::new(&pp, k, &asg[k].w, asg[k].io.clone()).unwrap(),
      asg[k].w.clone(),
    )
  };
  let running: Vec<Run<V>> = (0..c.mu)
    .map(|_| fold_checked::<V>(&pp, &fam, &[], &[inc_of(pick()), inc_of(pick())]).0)
    .collect();
  let incoming: Vec<Inc> = (0..c.nu).map(|_| inc_of(pick())).collect();
  (pp, fam, running, incoming)
}

fn proptest_runner(cases: u32) -> proptest::test_runner::TestRunner {
  use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
  TestRunner::new_with_rng(
    Config {
      cases,
      failure_persistence: None,
      ..Config::default()
    },
    TestRng::deterministic_rng(RngAlgorithm::ChaCha),
  )
}

#[test]
fn proptest_random_ccs_fold() {
  let mut runner = proptest_runner(48);
  runner
    .run(&case_strategy(), |c| {
      let (pp, fam, run, inc) = random_fold::<Direct>(&c);
      fold_checked(&pp, &fam, &run, &inc);
      let (pp, fam, run, inc) = random_fold::<Span>(&c);
      fold_checked(&pp, &fam, &run, &inc);
      Ok(())
    })
    .unwrap();
}

#[test]
fn proptest_single_tamper_rejected() {
  use proptest::prelude::*;
  let mut runner = proptest_runner(48);
  runner
    .run(&(case_strategy(), any::<u64>()), |(c, pos)| {
      let (pp, fam, run, inc) = random_fold::<Direct>(&c);
      let (_, out) = fold_checked(&pp, &fam, &run, &inc);
      let mut q = out.proof.clone();
      let mut slots: Vec<&mut F> = q
        .sc_x
        .iter_mut()
        .chain(q.sigma.iter_mut())
        .chain(q.tau.iter_mut())
        .chain(q.sc_y.iter_mut())
        .chain(q.eps.iter_mut())
        .chain(q.theta.iter_mut())
        .flatten()
        .collect();
      let n = slots.len();
      *slots[(pos as usize) % n] += F::ONE;
      let res = full_check(&pp, &fam, &run, &inc, &q, &Tags::of::<E, Direct>());
      prop_assert!(res.is_err(), "tampered proof accepted");
      prop_assert_eq!(res.unwrap_err().layer(), Layer::Verifier);
      Ok(())
    })
    .unwrap();
}

/// The HFS is generic over the engine: one fold on Vesta (scalar field = Pallas base field).
#[test]
fn test_generic_over_engine() {
  type E2 = crate::provider::VestaEngine;
  type F2 = <E2 as Engine>::Scalar;
  let tpl = Template::<F2>::power(5);
  let mut rng = ChaCha20Rng::seed_from_u64(3);
  let (ccs, a) = random_satisfiable(&tpl, 4, 3, 2, 2, &mut rng).unwrap();
  let shape = CcsShape::new(
    ccs.m,
    ccs.num_w,
    ccs.num_io,
    ccs.matrices.iter().map(|m| m.entries().to_vec()).collect(),
  )
  .unwrap();
  let pp = HfsParams::<E2>::new(CcsTemplate::power(5).unwrap(), vec![shape]).unwrap();
  let inc = IncomingInstance::new(&pp, 0, &a.w, a.io.clone()).unwrap();
  let out = NIFS::<E2, Direct>::prove(
    &pp,
    &[],
    &[],
    std::slice::from_ref(&inc),
    std::slice::from_ref(&a.w),
  )
  .unwrap();
  let (u, _) = NIFS::<E2, Direct>::verify(&pp, &[], &[inc], &out.proof).unwrap();
  decide(&pp, &u, &out.witness).unwrap();
}
