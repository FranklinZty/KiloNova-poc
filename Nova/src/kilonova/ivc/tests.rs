//! P5 tests: CycleFold circuit, n-input fold gadget, HFS v2 gadget (native = gadget),
//! recursive chains, rejections with their detection layer, and the constraint breakdown.
//! P4 tests: φ (scheduled program), the verifier without a schedule (trace recovery), family
//! reorder/substitution, forged ids, tampered spans, non-one-hot inputs, wiring, K = 16.
//!
//! Memory: run with `--release --test-threads=1` (16 GB machines). Long chains are `#[ignore]`d
//! and run explicitly (see `docs/P5-report.md`).
use super::{
  breakdown::{primary_breakdown, CATEGORIES},
  cyclefold::{
    cf_fold_prove, cf_fold_verify, cyclefold_instance_witness, num_inputs, Coords,
    CycleFoldCircuit, CycleFoldInputs,
  },
  fixtures::{example_program, ChainPredicates},
  gadgets::{
    alloc_vec, one_hot, one_hot_with, verify_hfs, AllocIncoming, AllocIndex, AllocProof,
    AllocRunning, AllocatedRelaxedR1CSInstanceN, Expr, HfsGadgetParams, NnPoint,
  },
  primary_constraint_counts, IvcError, IvcLayer, IvcVariant, PredicateProgram, PrimaryTemplate,
  PublicParams, RecursiveSNARK, Scheduled, Tamper,
};
use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_CHALLENGE_BITS},
  frontend::{
    num::AllocatedNum, shape_cs::ShapeCS, test_cs::TestConstraintSystem, ConstraintSystem,
  },
  gadgets::{
    ecc::AllocatedPoint,
    nonnative::{bignat::BigNat, util::f_to_nat},
  },
  kilonova::{
    hfs::{
      CcsShape, CcsTemplate, Direct, HfsParams, IncomingInstance, RunningInstance, RunningWitness,
      Span, Variant, NIFS,
    },
    shape_cs_to_shape, PredicateSet,
  },
  provider::{PallasEngine, VestaEngine},
  r1cs::{RelaxedR1CSInstance, RelaxedR1CSWitness},
  traits::{
    commitment::{CommitmentEngineTrait, CommitmentTrait},
    Engine, RO2ConstantsCircuit, ROConstants, ROConstantsCircuit,
  },
};
use ff::Field;
use kn_ccs::{
  accs::check_accs,
  r#gen::{wiring_pair, PairTemplate},
  AccsInstance, Ccs, Family, Template,
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

type E1 = PallasEngine;
type E2 = VestaEngine;
type F = <E1 as Engine>::Scalar;
type B = <E1 as Engine>::Base;

// ---------------------------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------------------------

/// A random non-identity E1 point (a Pedersen commitment to random values).
fn random_point(rng: &mut ChaCha20Rng, n: usize) -> crate::Commitment<E1> {
  let ck = <E1 as Engine>::CE::setup(b"kn-p5-test-points", n);
  let v: Vec<F> = (0..n).map(|_| F::random(&mut *rng)).collect();
  <E1 as Engine>::CE::commit(&ck, &v, &F::ZERO)
}

fn random_rho(rng: &mut ChaCha20Rng) -> F {
  // < 2^128
  let mut r = F::ZERO;
  let mut c = F::ONE;
  for _ in 0..2 {
    r += c * F::from(rand_core::RngCore::next_u64(rng));
    c *= F::from(1u64 << 32).square();
  }
  r
}

/// ι coordinates of a family of K predicates with t matrices.
fn iota_coords(k: usize, t: usize) -> Vec<Vec<Coords<B>>> {
  let pp = HfsParams::<E1>::new(
    CcsTemplate::new(t, vec![vec![0]], vec![F::ONE]).unwrap(),
    vec![CcsShape::new(1, 1, 1, vec![Vec::new(); t]).unwrap(); k],
  )
  .unwrap();
  (0..k)
    .map(|i| pp.iota(i).iter().map(|c| c.to_coordinates()).collect())
    .collect()
}

fn kn_family(pp: &HfsParams<E1>) -> Family<F> {
  let tpl = pp.template();
  let template = Template {
    t: tpl.t(),
    multisets: tpl.multisets().to_vec(),
    coeffs: tpl.coeffs().to_vec(),
  };
  Family::new(
    pp.shapes()
      .iter()
      .map(|s| {
        Ccs::new(
          s.m(),
          s.num_w(),
          s.num_io(),
          template.clone(),
          s.matrices()
            .iter()
            .map(|m| kn_ccs::SparseMatrix::from_triplets(s.m(), s.n(), m.clone()).unwrap())
            .collect(),
        )
        .unwrap()
      })
      .collect(),
  )
  .unwrap()
}

/// The independent kn-ccs oracle on a running instance (plus the index opening).
fn oracle<V: Variant<E1>>(
  pp: &HfsParams<E1>,
  fam: &Family<F>,
  u: &RunningInstance<E1, V>,
  w: &RunningWitness<E1>,
) {
  let accs = AccsInstance {
    comm_w: u.comm_w,
    u: u.u,
    io: u.io.clone(),
    lambda: w.lambda.clone(),
    r_x: u.r_x.clone(),
    r_y: u.r_y.clone(),
    v: u.v.clone(),
  };
  check_accs(fam, &accs, &w.w, |x| pp.commit_w(x).unwrap()).expect("kn-ccs oracle");
  V::check_opening(pp, &u.index, &w.lambda).expect("index opening");
}

// ---------------------------------------------------------------------------------------------
// CycleFold circuit
// ---------------------------------------------------------------------------------------------

fn cf_inputs(
  rng: &mut ChaCha20Rng,
  iota: &[Vec<Coords<B>>],
  t_idx: usize,
  k: usize,
  run_identity: bool,
) -> CycleFoldInputs<E1> {
  let rho = random_rho(rng);
  let w_run = if run_identity {
    crate::Commitment::<E1>::default()
  } else {
    random_point(rng, 4)
  };
  let w_inc = random_point(rng, 4);
  let w_out = w_run + w_inc * rho;
  let m = (0..t_idx)
    .map(|j| {
      let run = if run_identity {
        crate::Commitment::<E1>::default()
      } else {
        random_point(rng, 3)
      };
      // ι_k[j] as a commitment: rebuild it from the dummy params.
      let pp = HfsParams::<E1>::new(
        CcsTemplate::new(t_idx, vec![vec![0]], vec![F::ONE]).unwrap(),
        vec![CcsShape::new(1, 1, 1, vec![Vec::new(); t_idx]).unwrap(); iota.len()],
      )
      .unwrap();
      let out = run + pp.iota(k)[j] * rho;
      (run.to_coordinates(), out.to_coordinates())
    })
    .collect();
  CycleFoldInputs {
    rho,
    k,
    w: [
      w_run.to_coordinates(),
      w_inc.to_coordinates(),
      w_out.to_coordinates(),
    ],
    m,
  }
}

fn cf_satisfied(iota: &[Vec<Coords<B>>], t_idx: usize, v: CycleFoldInputs<E1>) -> bool {
  let c = CycleFoldCircuit::<E1> {
    iota,
    t_idx,
    inputs: Some(v.clone()),
  };
  let mut cs = TestConstraintSystem::<B>::new();
  c.synthesize(&mut cs).unwrap();
  // the public inputs are what `public_inputs` predicts
  let mut ws = crate::frontend::solver::SatisfyingAssignment::<E2>::new();
  c.synthesize(&mut ws).unwrap();
  assert_eq!(ws.input_assignment()[1..], c.public_inputs(&v)[..]);
  assert_eq!(ws.input_assignment().len(), num_inputs(t_idx) + 1);
  cs.is_satisfied()
}

/// The CycleFold circuit accepts honest RLCs (including identity running points) and rejects a
/// wrong output point, a wrong ρ and a wrong predicate id (ι selection).
#[test]
fn test_cyclefold_circuit() {
  let mut rng = ChaCha20Rng::seed_from_u64(55);
  for (k_family, t_idx) in [(2usize, 3usize), (4, 3), (2, 5), (3, 0)] {
    let iota = iota_coords(k_family, t_idx.max(1));
    for k in 0..k_family {
      for run_identity in [false, true] {
        let v = cf_inputs(&mut rng, &iota, t_idx, k, run_identity);
        assert!(
          cf_satisfied(&iota, t_idx, v.clone()),
          "honest K={k_family} t={t_idx} k={k}"
        );

        let mut bad = v.clone();
        bad.w[2].0 += B::ONE;
        assert!(!cf_satisfied(&iota, t_idx, bad), "wrong W_out accepted");

        let mut bad = v.clone();
        bad.rho += F::ONE;
        assert!(!cf_satisfied(&iota, t_idx, bad), "wrong rho accepted");

        if t_idx > 0 {
          let mut bad = v.clone();
          bad.k = (k + 1) % k_family;
          assert!(
            !cf_satisfied(&iota, t_idx, bad),
            "wrong predicate id accepted"
          );
          let mut bad = v.clone();
          bad.m[t_idx - 1].1 = v.w[1];
          assert!(!cf_satisfied(&iota, t_idx, bad), "wrong M_out accepted");
        }
      }
    }
  }
}

/// ρ ≥ 2^128 is rejected (range check of the bit decomposition).
#[test]
fn test_cyclefold_rejects_wide_rho() {
  let mut rng = ChaCha20Rng::seed_from_u64(56);
  let iota = iota_coords(2, 1);
  let mut v = cf_inputs(&mut rng, &iota, 0, 0, false);
  v.rho = F::from(2).pow_vartime([NUM_CHALLENGE_BITS as u64]) + F::ONE;
  let w_run = v.w[0];
  let _ = w_run;
  assert!(!cf_satisfied(&iota, 0, v));
}

// ---------------------------------------------------------------------------------------------
// n-input fold gadget
// ---------------------------------------------------------------------------------------------

/// Two CycleFold instances folded natively into the default accumulator; the second fold is
/// re-done by the gadget, which must give the same instance. The accumulator stays satisfied.
#[test]
fn test_cyclefold_fold_native_matches_gadget() {
  let mut rng = ChaCha20Rng::seed_from_u64(57);
  for t_idx in [0usize, 3] {
    let iota = iota_coords(2, t_idx.max(1));
    let circuit = CycleFoldCircuit::<E1> {
      iota: &iota,
      t_idx,
      inputs: None,
    };
    let mut cs = ShapeCS::<E2>::new();
    circuit.synthesize(&mut cs).unwrap();
    let shape = shape_cs_to_shape(&cs).pad();
    let ck = <E2 as Engine>::CE::setup(b"kn-p5-test-cf", shape.num_cons.max(shape.num_vars));
    let ro = ROConstants::<E2>::default();
    let pp_digest = F::from(4242);

    let mut acc_u = RelaxedR1CSInstance::<E2>::default(&ck, &shape);
    let mut acc_w = RelaxedR1CSWitness::<E2>::default(&shape);
    let mut last = None;
    for step in 0..2 {
      let v = cf_inputs(&mut rng, &iota, t_idx, step % 2, false);
      let c = CycleFoldCircuit::<E1> {
        iota: &iota,
        t_idx,
        inputs: Some(v),
      };
      let (u, w) = cyclefold_instance_witness::<E1, E2>(&c, &shape, &ck).unwrap();
      shape.is_sat(&ck, &u, &w).unwrap();
      let before = acc_u.clone();
      let (pf, nu, nw) =
        cf_fold_prove(&ck, &ro, pp_digest, &shape, &acc_u, &acc_w, &u, &w).unwrap();
      assert_eq!(cf_fold_verify(&ro, pp_digest, &acc_u, &u, &pf), nu);
      shape.is_sat_relaxed(&ck, &nu, &nw).unwrap();
      acc_u = nu.clone();
      acc_w = nw;
      last = Some((before, u, pf, nu));
    }

    let (before, u, pf, expected) = last.unwrap();
    let n = num_inputs(t_idx);
    let mut cs = TestConstraintSystem::<F>::new();
    let params = AllocatedNum::alloc(cs.namespace(|| "pp"), || Ok(pp_digest)).unwrap();
    let run =
      AllocatedRelaxedR1CSInstanceN::<E2>::alloc(cs.namespace(|| "U"), Some(&before), n).unwrap();
    let w =
      AllocatedPoint::<E2>::alloc(cs.namespace(|| "w"), Some(u.comm_W.to_coordinates())).unwrap();
    let t =
      AllocatedPoint::<E2>::alloc(cs.namespace(|| "t"), Some(pf.comm_t.to_coordinates())).unwrap();
    let x: Vec<BigNat<F>> = u
      .X
      .iter()
      .enumerate()
      .map(|(i, xi)| {
        let b = BigNat::alloc_from_nat(
          cs.namespace(|| format!("x{i}")),
          || Ok(f_to_nat(xi)),
          BN_LIMB_WIDTH,
          BN_N_LIMBS,
        )
        .unwrap();
        b.assert_well_formed(cs.namespace(|| format!("x{i} range")))
          .unwrap();
        b
      })
      .collect();
    let out = run
      .fold_with_r1cs(
        cs.namespace(|| "fold"),
        &params,
        &w,
        &x,
        &t,
        ROConstantsCircuit::<E2>::default(),
      )
      .unwrap();
    assert!(cs.is_satisfied(), "{:?}", cs.which_is_unsatisfied());
    let (ex, ey, einf) = expected.comm_W.to_coordinates();
    assert_eq!(out.w.x.get_value(), Some(ex));
    assert_eq!(out.w.y.get_value(), Some(ey));
    assert_eq!(
      out.w.is_infinity.get_value(),
      Some(if einf { F::ONE } else { F::ZERO })
    );
    let (ex, ey, _) = expected.comm_E.to_coordinates();
    assert_eq!(out.e.x.get_value(), Some(ex));
    assert_eq!(out.e.y.get_value(), Some(ey));
    assert_eq!(
      out.u.get_value(),
      Some(crate::gadgets::utils::scalar_as_base::<E2>(expected.u))
    );
    for (xi, ex) in out.x.iter().zip(&expected.X) {
      let limbs: Vec<F> = xi.iter().map(|l| l.get_value().unwrap()).collect();
      assert_eq!(limbs, super::gadgets::limbs_of::<B, F>(ex));
    }
  }
}

// ---------------------------------------------------------------------------------------------
// HFS v2 gadget = native verifier
// ---------------------------------------------------------------------------------------------

fn pair_family(tpl: PairTemplate) -> (Family<F>, HfsParams<E1>) {
  let fam = Family::new(
    (0..2)
      .map(|k| wiring_pair::<F>(tpl, k, 2, None).unwrap().0)
      .collect(),
  )
  .unwrap();
  let t = &fam.member(0).template;
  let shapes = (0..2)
    .map(|i| {
      let c = fam.member(i);
      CcsShape::new(
        c.m,
        c.num_w,
        c.num_io,
        c.matrices.iter().map(|m| m.entries().to_vec()).collect(),
      )
      .unwrap()
    })
    .collect();
  let pp = HfsParams::new(
    CcsTemplate::new(t.t, t.multisets.clone(), t.coeffs.clone()).unwrap(),
    shapes,
  )
  .unwrap();
  (fam, pp)
}

fn pair_input(
  pp: &HfsParams<E1>,
  tpl: PairTemplate,
  k: usize,
  x: F,
) -> (IncomingInstance<E1>, Vec<F>) {
  let (_, a) = wiring_pair(tpl, k, 2, Some(x)).unwrap();
  let a = a.unwrap();
  (
    IncomingInstance::new(pp, k, &a.w, a.io.clone()).unwrap(),
    a.w,
  )
}

/// Allocates the gadget's inputs and runs it; returns (satisfied, outputs as values).
#[allow(clippy::type_complexity)]
fn run_gadget<V: IvcVariant<E1>>(
  pp: &HfsParams<E1>,
  run: &RunningInstance<E1, V>,
  inc: &IncomingInstance<E1>,
  pf: &crate::kilonova::hfs::HfsProof<E1>,
  active: bool,
) -> (bool, Vec<F>, usize) {
  let t = pp.t();
  let iota: Vec<Vec<Coords<B>>> = (0..pp.k())
    .map(|i| pp.iota(i).iter().map(|c| c.to_coordinates()).collect())
    .collect();
  let mut cs = TestConstraintSystem::<F>::new();
  let digest = AllocatedNum::alloc(cs.namespace(|| "digest"), || Ok(pp.digest())).unwrap();
  let index = if V::DIRECT {
    AllocIndex::Direct(
      V::index_coords(&run.index)
        .iter()
        .enumerate()
        .map(|(j, c)| NnPoint::alloc(cs.namespace(|| format!("M{j}")), Some(*c), false).unwrap())
        .collect(),
    )
  } else {
    AllocIndex::Span(
      alloc_vec(
        cs.namespace(|| "lambda"),
        Some(&V::index_scalars(&run.index)),
        pp.k(),
      )
      .unwrap(),
    )
  };
  let arun = AllocRunning {
    comm_w: NnPoint::alloc(
      cs.namespace(|| "W"),
      Some(run.comm_w.to_coordinates()),
      false,
    )
    .unwrap(),
    index,
    u: AllocatedNum::alloc(cs.namespace(|| "u"), || Ok(run.u)).unwrap(),
    io: alloc_vec(cs.namespace(|| "io"), Some(&run.io), run.io.len()).unwrap(),
    r_x: alloc_vec(cs.namespace(|| "r_x"), Some(&run.r_x), run.r_x.len()).unwrap(),
    r_y: alloc_vec(cs.namespace(|| "r_y"), Some(&run.r_y), run.r_y.len()).unwrap(),
    v: alloc_vec(cs.namespace(|| "v"), Some(&run.v), run.v.len()).unwrap(),
  };
  let k = AllocatedNum::alloc(cs.namespace(|| "k"), || Ok(F::from(inc.k as u64))).unwrap();
  let k_bits = one_hot(cs.namespace(|| "k bits"), &k, pp.k()).unwrap();
  let ainc = AllocIncoming {
    k,
    k_bits,
    comm_w: NnPoint::alloc(
      cs.namespace(|| "inc W"),
      Some(inc.comm_w.to_coordinates()),
      true,
    )
    .unwrap(),
    io: alloc_vec(cs.namespace(|| "inc io"), Some(&inc.io), inc.io.len()).unwrap(),
  };
  let rounds = |cs: &mut TestConstraintSystem<F>, n: &str, m: &[Vec<F>]| {
    m.iter()
      .enumerate()
      .map(|(i, r)| alloc_vec(cs.namespace(|| format!("{n}{i}")), Some(r), r.len()).unwrap())
      .collect::<Vec<_>>()
  };
  let apf = AllocProof {
    sc_x: rounds(&mut cs, "sc_x", &pf.sc_x),
    sigma: alloc_vec(cs.namespace(|| "sigma"), Some(&pf.sigma[0]), t).unwrap(),
    tau: alloc_vec(cs.namespace(|| "tau"), Some(&pf.tau[0]), t).unwrap(),
    sc_y: rounds(&mut cs, "sc_y", &pf.sc_y),
    eps: alloc_vec(cs.namespace(|| "eps"), Some(&pf.eps[0]), t + 1).unwrap(),
    theta: alloc_vec(cs.namespace(|| "theta"), Some(&pf.theta[0]), t + 1).unwrap(),
  };
  let act = AllocatedNum::alloc(cs.namespace(|| "active"), || {
    Ok(if active { F::ONE } else { F::ZERO })
  })
  .unwrap();
  let gp = HfsGadgetParams {
    template: pp.template(),
    tag_input: V::TAG_INPUT,
    s: pp.s(),
    iota: &iota,
  };
  let before = cs.num_constraints();
  let out = verify_hfs::<E1, _>(
    cs.namespace(|| "hfs"),
    &gp,
    RO2ConstantsCircuit::<E1>::default(),
    &digest,
    &arun,
    &ainc,
    &apf,
    &Expr::num(&act),
  )
  .unwrap();
  let size = cs.num_constraints() - before;
  let mut vals = vec![out.gamma.get_value().unwrap()];
  vals.extend(out.alpha.iter().map(|x| x.get_value().unwrap()));
  vals.extend(out.r_x.iter().map(|x| x.get_value().unwrap()));
  vals.push(out.delta.get_value().unwrap());
  vals.extend(out.r_y.iter().map(|x| x.get_value().unwrap()));
  vals.push(out.rho.get_value().unwrap());
  vals.push(out.u.get_value().unwrap());
  vals.extend(out.io.iter().map(|x| x.get_value().unwrap()));
  vals.extend(out.v.iter().map(|x| x.get_value().unwrap()));
  if let Some(l) = &out.lambda {
    vals.extend(l.iter().map(|x| x.get_value().unwrap()));
  }
  (cs.is_satisfied(), vals, size)
}

fn gadget_matches_native<V: IvcVariant<E1>>(tpl: PairTemplate) {
  let (fam, pp) = pair_family(tpl);
  let mut rng = ChaCha20Rng::seed_from_u64(58);
  // A non-trivial running instance: fold a fresh instance into nothing (μ = 0, ν = 1), then
  // one more incoming instance.
  let (i0, w0) = pair_input(&pp, tpl, 0, F::random(&mut rng));
  let first = NIFS::<E1, V>::prove(&pp, &[], &[], &[i0], &[w0]).unwrap();
  oracle(&pp, &fam, &first.instance, &first.witness);
  let (i1, w1) = pair_input(&pp, tpl, 1, F::random(&mut rng));
  let out = NIFS::<E1, V>::prove(
    &pp,
    std::slice::from_ref(&first.instance),
    std::slice::from_ref(&first.witness),
    std::slice::from_ref(&i1),
    std::slice::from_ref(&w1),
  )
  .unwrap();
  let (u, ch) = NIFS::<E1, V>::verify(
    &pp,
    std::slice::from_ref(&first.instance),
    std::slice::from_ref(&i1),
    &out.proof,
  )
  .unwrap();
  oracle(&pp, &fam, &u, &out.witness);

  let (ok, vals, size) = run_gadget::<V>(&pp, &first.instance, &i1, &out.proof, true);
  assert!(ok, "gadget rejects an honest fold");
  let mut expect = vec![ch.gamma];
  expect.extend(&ch.alpha);
  expect.extend(&ch.r_x);
  expect.push(ch.delta);
  expect.extend(&ch.r_y);
  expect.push(ch.rho);
  expect.push(u.u);
  expect.extend(&u.io);
  expect.extend(&u.v);
  expect.extend(V::index_scalars(&u.index));
  assert_eq!(vals, expect, "native and gadget transcripts/folds differ");
  assert_eq!(u.r_x, ch.r_x);
  println!(
    "HFS gadget {} {}: {size} constraints (s = {}, s' = {})",
    V::NAME,
    tpl.name(),
    pp.s(),
    pp.s_prime()
  );

  // Tampering: a round message, a claim and the predicate id are rejected when active; the
  // gate turns the checks off in the base case.
  let mut bad = out.proof.clone();
  bad.sc_x[0][1] += F::ONE;
  assert!(!run_gadget::<V>(&pp, &first.instance, &i1, &bad, true).0);
  assert!(run_gadget::<V>(&pp, &first.instance, &i1, &bad, false).0);
  let mut bad = out.proof.clone();
  bad.tau[0][0] += F::ONE;
  assert!(!run_gadget::<V>(&pp, &first.instance, &i1, &bad, true).0);
  let mut bad = out.proof.clone();
  bad.sc_y[pp.s_prime() - 1][2] += F::ONE;
  assert!(!run_gadget::<V>(&pp, &first.instance, &i1, &bad, true).0);
  let mut wrong = i1.clone();
  wrong.k = 0;
  assert!(!run_gadget::<V>(&pp, &first.instance, &wrong, &out.proof, true).0);
}

/// Native `hfs::NIFS::verify` and the gadget produce the same challenges (γ, α, r_x, δ, r_y,
/// ρ) and the same folded scalars; the gadget rejects tampered proofs (Direct, R1CS).
#[test]
fn test_transcript_native_matches_gadget_v2_direct() {
  gadget_matches_native::<Direct>(PairTemplate::R1cs);
  gadget_matches_native::<Direct>(PairTemplate::Power5);
}

/// Same for Span (λ folded in-circuit).
#[test]
fn test_transcript_native_matches_gadget_v2_span() {
  gadget_matches_native::<Span>(PairTemplate::R1cs);
  gadget_matches_native::<Span>(PairTemplate::Power5);
}

// ---------------------------------------------------------------------------------------------
// Recursive chains (P4: the schedule is a program run by φ; the verifier takes no schedule)
// ---------------------------------------------------------------------------------------------

type Pp<V> = PublicParams<E1, E2, V>;
type Snark<V> = RecursiveSNARK<E1, E2, V>;
type Prog = Scheduled<ChainPredicates<F>>;

/// Application part of the initial state.
fn app0() -> Vec<F> {
  vec![F::from(3), F::from(5)]
}

/// The initial state that makes φ run `ids`.
fn z0_for<P: PredicateSet<F>>(prog: &Scheduled<P>, app: &[F], ids: &[usize]) -> Vec<F> {
  prog
    .z0(app, ids)
    .expect("schedule fits the program register")
}

fn setup_prog<V: IvcVariant<E1>>(prog: &Prog, tpl: PrimaryTemplate) -> Pp<V> {
  let (pp, report) = Pp::<V>::setup(prog, tpl).unwrap();
  println!(
    "[ivc setup] {} K={} {:?}: iterations {:?}, m = {}, num_w = {}, CycleFold {:?} -> {:?}, family digest {:?}",
    V::NAME,
    prog.num_predicates(),
    tpl,
    report.iterations,
    report.primary_m,
    report.primary_num_w,
    report.cyclefold_raw,
    report.cyclefold_padded,
    pp.family().digest()
  );
  pp
}

fn setup<V: IvcVariant<E1>>(k: usize, tpl: PrimaryTemplate) -> (Pp<V>, Prog) {
  let prog = ChainPredicates::<F>::new(k, tpl == PrimaryTemplate::R1csPow5).program();
  (setup_prog::<V>(&prog, tpl), prog)
}

/// Proves the program whose register encodes `ids` (φ chooses every step; the host only says
/// "next") and verifies after the steps in `check` (1-based) and at the end, each time with
/// the kn-ccs oracle on the running instance. `verify` gets no schedule; the recovered trace is
/// compared with `ids` (`verify_schedule`) and the state with the native run.
fn run_chain<V: IvcVariant<E1>>(pp: &Pp<V>, prog: &Prog, ids: &[usize], every: usize) -> Snark<V> {
  let fam = kn_family(pp.hfs());
  let z0 = z0_for(prog, &app0(), ids);
  let mut snark = Snark::<V>::new(pp, prog, &z0).unwrap();
  for n in 1..=ids.len() {
    if n > 1 {
      assert_eq!(
        snark.next_predicate(prog),
        Some(ids[n - 1]),
        "φ follows the program"
      );
      snark.prove_step(pp, prog).unwrap();
    }
    if n % every == 0 || n == ids.len() || n == 1 {
      let out = snark
        .verify(pp, n, &z0)
        .unwrap_or_else(|e| panic!("verify after step {n}: {e} (layer {:?})", e.layer()));
      assert_eq!(out.trace, pp.trace_of(&ids[..n]), "recovered trace");
      assert_eq!(out.last_id, ids[n - 1]);
      assert_eq!(out.zn[..2], prog.inner().run(&app0(), &ids[..n])[..]);
      assert_eq!(
        out.zn[2],
        prog.encode::<F>(&ids[n..]).unwrap(),
        "rest of the program"
      );
      assert_eq!(snark.verify_schedule(pp, n, &z0, &ids[..n]).unwrap(), out);
      let (u, w) = snark.running();
      oracle(pp.hfs(), &fam, u, w);
    }
  }
  snark
}

fn schedule(k: usize, t: usize, seed: u64) -> Vec<usize> {
  let mut rng = ChaCha20Rng::seed_from_u64(seed);
  (0..t)
    .map(|i| {
      if i < k {
        i
      } else {
        (rand_core::RngCore::next_u32(&mut rng) as usize) % k
      }
    })
    .collect()
}

/// K = 2, T = 1 and T = 16 (Direct), every step verified for T ≤ 4, then every 4th.
#[test]
fn test_ivc_chain_k2_direct() {
  let (pp, prog) = setup::<Direct>(2, PrimaryTemplate::R1cs);
  run_chain(&pp, &prog, &[1], 1);
  run_chain(&pp, &prog, &schedule(2, 16, 101), 4);
}

/// K = 2, T = 16 (Span).
#[test]
fn test_ivc_chain_k2_span() {
  let (pp, prog) = setup::<Span>(2, PrimaryTemplate::R1cs);
  run_chain(&pp, &prog, &[0], 1);
  run_chain(&pp, &prog, &schedule(2, 16, 202), 4);
}

/// K = 4, T = 16 (Direct).
#[test]
fn test_ivc_chain_k4_t16_direct() {
  let (pp, prog) = setup::<Direct>(4, PrimaryTemplate::R1cs);
  run_chain(&pp, &prog, &schedule(4, 16, 303), 8);
}

/// K = 2 and 4, T = 64 (Direct). Long: run explicitly with `--ignored`.
#[test]
#[ignore = "long (T = 64); run explicitly: cargo test --release --lib kilonova::ivc::tests::test_ivc_chain_t64 -- --ignored --test-threads=1"]
fn test_ivc_chain_t64_direct() {
  for k in [2, 4] {
    let (pp, prog) = setup::<Direct>(k, PrimaryTemplate::R1cs);
    run_chain(&pp, &prog, &schedule(k, 64, 404 + k as u64), 16);
  }
}

/// K = 4, T = 16 and K = 2/4, T = 64 (Span). Long: run explicitly with `--ignored`.
#[test]
#[ignore = "long; run explicitly: cargo test --release --lib kilonova::ivc::tests::test_ivc_chain_span_long -- --ignored --test-threads=1"]
fn test_ivc_chain_span_long() {
  for (k, t) in [(4, 16), (2, 64), (4, 64)] {
    let (pp, prog) = setup::<Span>(k, PrimaryTemplate::R1cs);
    run_chain(&pp, &prog, &schedule(k, t, 505 + (k * t) as u64), 16);
  }
}

/// K = 16, T = 16 (Direct): every member once. Long: run explicitly with `--ignored`.
#[test]
#[ignore = "long (K = 16 setup); run explicitly: cargo test --release --lib kilonova::ivc::tests::test_ivc_chain_k16 -- --ignored --test-threads=1"]
fn test_ivc_chain_k16() {
  let (pp, prog) = setup::<Direct>(16, PrimaryTemplate::R1cs);
  run_chain(&pp, &prog, &schedule(16, 16, 616), 8);
}

/// Native degree-5 application inside the loop: member 0 computes x⁵ with one native row of
/// the combined template (t = 5, d = 5). The shapes are checked not to lower it.
#[test]
fn test_ivc_native_pow5_application() {
  let (pp, prog) = setup::<Direct>(2, PrimaryTemplate::R1csPow5);
  assert_eq!(pp.hfs().template().degree(), 5);
  assert_eq!(pp.hfs().t(), 5);
  let rows = |k: usize| -> (usize, usize) {
    let s = pp.hfs().shape(k);
    (s.matrices()[3].len(), s.matrices()[4].len())
  };
  // member 0 has exactly one D row entry (x) and one E row entry (x⁵); member 1 has none.
  assert_eq!(rows(0), (1, 1));
  assert_eq!(rows(1), (0, 0));
  let ids = [0, 1, 0, 0, 1, 0];
  let snark = run_chain(&pp, &prog, &ids, 2);
  assert_eq!(snark.outputs()[..2], prog.inner().run(&app0(), &ids)[..]);
}

/// The R1CS template rejects a family with native power rows at setup.
#[test]
fn test_ivc_r1cs_template_rejects_pow5_rows() {
  let prog = ChainPredicates::<F>::new(2, true).program();
  let res = Pp::<Direct>::setup(&prog, PrimaryTemplate::R1cs);
  assert!(res.is_err());
}

// ---------------------------------------------------------------------------------------------
// The v1 B15-ignored traces, ported to v2
// ---------------------------------------------------------------------------------------------

fn v1_trace<V: IvcVariant<E1>>(ids: &[usize]) {
  let prog = example_program::<F>();
  let (pp, _) = Pp::<V>::setup(&prog, PrimaryTemplate::R1cs).unwrap();
  let z0 = z0_for(&prog, &[F::ZERO], ids);
  let mut snark = Snark::<V>::new(&pp, &prog, &z0).unwrap();
  for step in 1..ids.len() {
    snark.prove_step(&pp, &prog).unwrap();
    snark
      .verify_schedule(&pp, step + 1, &z0, &ids[..=step])
      .unwrap_or_else(|e| panic!("verify after step {}: {e}", step + 1));
  }
  let out = snark.verify_schedule(&pp, ids.len(), &z0, ids).unwrap();
  let direct = ids
    .iter()
    .fold(vec![F::ZERO], |z, &k| prog.inner().output(k, &z));
  assert_eq!(out.zn[..1], direct[..]);
}

/// v2 port of `kilonova::tests::test_ivc_nontrivial_nonuniform_smoke` (B15-ignored in v1).
#[test]
fn test_ivc_v2_nonuniform_smoke_direct() {
  v1_trace::<Direct>(&[0, 2]);
}

/// v2 port of `kilonova::tests::test_ivc_nontrivial_nonuniform` (B15-ignored in v1).
#[test]
fn test_ivc_v2_nonuniform_direct() {
  v1_trace::<Direct>(&[0, 1, 2]);
}

/// v2 port of `kilonova::span::tests::test_ivc_nontrivial_nonuniform_smoke` (B15-ignored).
#[test]
fn test_ivc_v2_nonuniform_smoke_span() {
  v1_trace::<Span>(&[0, 1]);
}

/// v2 port of `kilonova::span::tests::test_ivc_nontrivial_nonuniform` (B15-ignored).
#[test]
fn test_ivc_v2_nonuniform_span() {
  v1_trace::<Span>(&[0, 1, 0]);
}

// ---------------------------------------------------------------------------------------------
// φ and the program register (no setup)
// ---------------------------------------------------------------------------------------------

/// The scheduled program: native φ = in-circuit φ, encode/select round trip, a register that
/// is too large or a forged decomposition is unsatisfiable, and `prog' = (prog − k)/2^b`.
#[test]
fn test_phi_scheduled_program() {
  for k in [1usize, 2, 3, 4, 16] {
    let prog = ChainPredicates::<F>::new(k, false).program();
    let mut rng = ChaCha20Rng::seed_from_u64(k as u64);
    let ids: Vec<usize> = (0..prog.capacity())
      .map(|_| (rand_core::RngCore::next_u32(&mut rng) as usize) % k)
      .collect();
    let mut z = z0_for(&prog, &app0(), &ids);
    for (i, &id) in ids.iter().enumerate().take(20) {
      assert_eq!(prog.select(i, &z), Some(id));
      // in-circuit φ and the step F_k agree with the native ones
      let mut cs = TestConstraintSystem::<F>::new();
      let zi = alloc_vec(cs.namespace(|| "z"), Some(&z[..]), 3).unwrap();
      let i_var = AllocatedNum::alloc(cs.namespace(|| "i"), || Ok(F::from(i as u64))).unwrap();
      let sel = prog
        .synthesize_select(&mut cs.namespace(|| "phi"), &i_var, &zi)
        .unwrap();
      assert_eq!(sel.get_value(), Some(F::from(id as u64)));
      let next = prog.synthesize(id, &mut cs.namespace(|| "F"), &zi).unwrap();
      assert!(cs.is_satisfied(), "honest φ and step");
      let native: Vec<F> = [
        prog.inner().output(id, &z[..2]),
        vec![prog.encode(&ids[i + 1..]).unwrap()],
      ]
      .concat();
      assert_eq!(
        next
          .iter()
          .map(|v| v.get_value().unwrap())
          .collect::<Vec<_>>(),
        native
      );
      z = native;
    }
    // a register ≥ 2^L selects nothing and its decomposition is unsatisfiable
    let big = F::from(2).pow_vartime([prog.decomposed_bits() as u64]);
    assert_eq!(prog.select(0, &[F::ZERO, F::ZERO, big]), None);
    let mut cs = TestConstraintSystem::<F>::new();
    let zi = alloc_vec(cs.namespace(|| "z"), Some(&[F::ZERO, F::ZERO, big][..]), 3).unwrap();
    let i_var = AllocatedNum::alloc(cs.namespace(|| "i"), || Ok(F::ZERO)).unwrap();
    prog
      .synthesize_select(&mut cs.namespace(|| "phi"), &i_var, &zi)
      .unwrap();
    assert!(!cs.is_satisfied(), "register out of range");
  }
  // K = 3: digit 3 selects no member
  let prog = example_program::<F>();
  assert_eq!(prog.select(0, &[F::ZERO, F::from(3)]), None);
  assert_eq!(prog.encode::<F>(&[3]), None);
  assert_eq!(prog.encode::<F>(&[0; 300][..prog.capacity() + 1]), None);
}

/// At least two predicates really change the wiring: the application circuits of members 0–3
/// (and 4–15) have pairwise different sparsity patterns, not only different constants.
#[test]
fn test_p4_members_change_wiring() {
  let preds = ChainPredicates::<F>::new(16, false);
  let pattern = |id: usize| {
    let mut cs = ShapeCS::<E1>::new();
    let z = alloc_vec(cs.namespace(|| "z"), None, 2).unwrap();
    preds.synthesize(id, &mut cs.namespace(|| "F"), &z).unwrap();
    let sh = shape_cs_to_shape(&cs);
    [&sh.A, &sh.B, &sh.C]
      .iter()
      .map(|m| m.iter().map(|(r, c, _)| (r, c)).collect::<Vec<_>>())
      .collect::<Vec<_>>()
  };
  let pats: Vec<_> = (0..16).map(pattern).collect();
  for a in 0..16 {
    for b in 0..a {
      assert_ne!(pats[a], pats[b], "members {a} and {b} share the wiring");
    }
  }
}

// ---------------------------------------------------------------------------------------------
// Rejections (each names its detection layer)
// ---------------------------------------------------------------------------------------------

fn expect_layer<T>(res: Result<T, IvcError>, layer: IvcLayer, what: &str) {
  match res {
    Ok(_) => panic!("{what}: accepted"),
    Err(e) => assert_eq!(
      e.layer(),
      layer,
      "{what}: rejected at the wrong layer ({e})"
    ),
  }
}

/// Verifier-side claims about an honest chain: wrong initial state (application part or program
/// register), skipped step, wrong counter are rejected by the link hash; a host-supplied
/// schedule that disagrees with the proven one (swapped steps, wrong predicate choice, wrong
/// last predicate) is rejected by `verify_schedule` (layer Trace).
#[test]
fn test_ivc_rejects_wrong_claims() {
  let (pp, prog) = setup::<Direct>(2, PrimaryTemplate::R1cs);
  let ids = [0usize, 1, 1, 0, 1];
  let snark = run_chain(&pp, &prog, &ids, 5);
  let z0 = z0_for(&prog, &app0(), &ids);
  let n = ids.len();
  assert!(snark.verify(&pp, n, &z0).is_ok());

  let mut wrong_z0 = z0.clone();
  wrong_z0[0] += F::ONE;
  expect_layer(
    snark.verify(&pp, n, &wrong_z0),
    IvcLayer::LinkHash,
    "wrong initial state",
  );
  // the same proof claimed for a program register that encodes swapped steps
  let swapped = [0usize, 1, 0, 1, 1];
  expect_layer(
    snark.verify(&pp, n, &z0_for(&prog, &app0(), &swapped)),
    IvcLayer::LinkHash,
    "swapped steps (initial program)",
  );
  // skipped step and wrong counter
  expect_layer(
    snark.verify(&pp, n - 1, &z0),
    IvcLayer::LinkHash,
    "skipped step",
  );
  expect_layer(
    snark.verify(&pp, n + 1, &z0),
    IvcLayer::LinkHash,
    "wrong counter (n + 1)",
  );
  // expected schedules that disagree with the recovered trace
  expect_layer(
    snark.verify_schedule(&pp, n, &z0, &swapped),
    IvcLayer::Trace,
    "swapped steps (expected schedule)",
  );
  expect_layer(
    snark.verify_schedule(&pp, n, &z0, &[1, 1, 1, 0, 1]),
    IvcLayer::Trace,
    "wrong predicate choice",
  );
  expect_layer(
    snark.verify_schedule(&pp, n, &z0, &[0, 1, 1, 0, 0]),
    IvcLayer::Trace,
    "wrong last predicate",
  );
  expect_layer(
    snark.verify_schedule(&pp, n, &z0, &ids[..n - 1]),
    IvcLayer::Trace,
    "schedule of another length",
  );
}

/// A tampered prover step in the middle of a chain is caught by the final check only: the
/// in-circuit checks make that step's instance unsatisfied, the next step's in-circuit HFS
/// verifier fails, and so on, up to the last incoming instance (or the CycleFold accumulator).
fn tampered_chain(
  forced: Option<(usize, usize)>,
  tamper: Tamper,
  at: usize,
  len: usize,
) -> IvcError {
  let (pp, prog) = setup::<Direct>(2, PrimaryTemplate::R1cs);
  let ids: Vec<usize> = (0..len).map(|i| i % 2).collect();
  let z0 = z0_for(&prog, &app0(), &ids);
  // the host runs the schedule `ids` (= φ on an honest state), except a forced id at one step;
  // after a deviation φ no longer selects anything sensible, so the host keeps following `ids`
  let force = |n: usize| {
    Some(
      forced
        .and_then(|(s, k)| (s == n).then_some(k))
        .unwrap_or(ids[n]),
    )
  };
  let mut snark = Snark::<Direct>::new_tampered(&pp, &prog, &z0, force(0)).unwrap();
  for n in 1..len {
    let t = if n == at { tamper } else { Tamper::None };
    snark.prove_step_tampered(&pp, &prog, force(n), t).unwrap();
  }
  snark.verify(&pp, len, &z0).unwrap_err()
}

#[test]
fn test_ivc_rejects_broken_state_link() {
  // at the last step: the last incoming instance's in-circuit hash check fails
  let e = tampered_chain(None, Tamper::StateLink, 3, 4);
  assert_eq!(e.layer(), IvcLayer::LastIncoming, "{e}");
  // in the middle: propagates through the next in-circuit HFS verifiers
  let e = tampered_chain(None, Tamper::StateLink, 2, 4);
  assert_eq!(e.layer(), IvcLayer::LastIncoming, "{e}");
}

#[test]
fn test_ivc_rejects_repeated_counter() {
  let e = tampered_chain(None, Tamper::Counter, 2, 4);
  assert!(
    matches!(e.layer(), IvcLayer::LastIncoming | IvcLayer::LinkHash),
    "{e}"
  );
}

#[test]
fn test_ivc_rejects_wrong_incoming_predicate() {
  // folding the incoming instance as the other predicate: the in-circuit zero-check fails
  let e = tampered_chain(None, Tamper::IncomingPredicate, 2, 4);
  assert_eq!(e.layer(), IvcLayer::LastIncoming, "{e}");
}

#[test]
fn test_ivc_rejects_unbound_hint() {
  // the folded comm_W hint is not the CycleFold output: the CycleFold instance is unsatisfied
  // (and the link hash no longer matches the prover's own running instance)
  let e = tampered_chain(None, Tamper::HintW, 3, 4);
  assert!(
    matches!(e.layer(), IvcLayer::CycleFold | IvcLayer::LinkHash),
    "{e}"
  );
  let e = tampered_chain(None, Tamper::HintW, 2, 4);
  assert!(
    matches!(
      e.layer(),
      IvcLayer::CycleFold | IvcLayer::LinkHash | IvcLayer::LastIncoming
    ),
    "{e}"
  );
}

#[test]
fn test_ivc_rejects_bad_cyclefold_witness() {
  let e = tampered_chain(None, Tamper::CycleFoldWitness, 3, 4);
  assert_eq!(e.layer(), IvcLayer::CycleFold, "{e}");
}

/// P4 (G4): a host that runs a predicate φ did not select is rejected. The circuit of the
/// forced predicate enforces `φ(i, z_i) = k`, so its instance is unsatisfied: at the last step
/// the final CCS check fails (LastIncoming); at the base step or an inner step the next
/// in-circuit HFS verifier fails and the failure propagates to the last instance.
#[test]
fn test_p4_rejects_schedule_disagreeing_with_phi() {
  // the program runs [0, 1, 0, 1]; the host forces predicate 0 at step 3 (φ selects 1)
  let e = tampered_chain(Some((3, 0)), Tamper::None, usize::MAX, 4);
  assert_eq!(e.layer(), IvcLayer::LastIncoming, "last step: {e}");
  // inner step 1 (φ selects 1, the host runs 0)
  let e = tampered_chain(Some((1, 0)), Tamper::None, usize::MAX, 4);
  assert_eq!(e.layer(), IvcLayer::LastIncoming, "inner step: {e}");
  // base step (φ(0, z0) = 0, the host runs 1)
  let e = tampered_chain(Some((0, 1)), Tamper::None, usize::MAX, 3);
  assert_eq!(e.layer(), IvcLayer::LastIncoming, "base step: {e}");
}

/// P4 (G3): forged ids in the proof. A different trace hash → LinkHash; the last instance
/// relabelled as another member → LastIncoming (that member's circuit, with its φ check, is
/// not satisfied by the witness); an id outside the family → Input.
#[test]
fn test_p4_rejects_forged_ids() {
  let (pp, prog) = setup::<Direct>(4, PrimaryTemplate::R1cs);
  let ids = [0usize, 3, 2, 1, 3];
  let snark = run_chain(&pp, &prog, &ids, 5);
  let z0 = z0_for(&prog, &app0(), &ids);

  let mut s = snark.clone();
  *s.forge().0 = pp.trace_of(&[0, 3, 2, 1, 2]);
  expect_layer(s.verify(&pp, 5, &z0), IvcLayer::LinkHash, "forged trace");
  let mut s = snark.clone();
  *s.forge().1 = 2;
  expect_layer(
    s.verify(&pp, 5, &z0),
    IvcLayer::LastIncoming,
    "relabelled last id",
  );
  let mut s = snark.clone();
  *s.forge().1 = 4;
  expect_layer(
    s.verify(&pp, 5, &z0),
    IvcLayer::Input,
    "id outside the family",
  );
  // the stable ids of the family resolve the recovered positions
  assert_eq!(pp.family().ids()[3], "chain/m3");
  assert_eq!(pp.family().position("chain/m2"), Some(2));
}

/// P4: a reordered family and a substituted matrix change the family digest; setup with the
/// pinned digest rejects them (Setup), and a proof made under them is rejected by the original
/// parameters (LinkHash: the link hash binds pp_digest and the family digest).
#[test]
fn test_p4_rejects_reordered_and_substituted_family() {
  let (pp, prog) = setup::<Direct>(2, PrimaryTemplate::R1cs);
  let d = pp.family().digest();
  let ids = [1usize, 0];
  let z0 = z0_for(&prog, &app0(), &ids);
  assert!(run_chain(&pp, &prog, &ids, 2).verify(&pp, 2, &z0).is_ok());

  let reordered = ChainPredicates::<F>::reordered(2, vec![1, 0]).program();
  expect_layer(
    Pp::<Direct>::setup_pinned(&reordered, PrimaryTemplate::R1cs, d),
    IvcLayer::Setup,
    "reordered family (pinned digest)",
  );
  let substituted = ChainPredicates::<F>::substituted(2, 1).program();
  for (what, other) in [("reordered", reordered), ("substituted", substituted)] {
    let pp_o = setup_prog::<Direct>(&other, PrimaryTemplate::R1cs);
    assert_ne!(pp_o.family().digest(), d, "{what}: digest");
    assert_ne!(pp_o.digest(), pp.digest(), "{what}: pp digest");
    // the same member ids, in another order or with a substituted matrix
    let mut sorted = pp_o.family().ids().to_vec();
    sorted.sort();
    assert_eq!(sorted, pp.family().ids());
    let mut s = Snark::<Direct>::new(&pp_o, &other, &z0).unwrap();
    s.prove_step(&pp_o, &other).unwrap();
    s.verify(&pp_o, 2, &z0).unwrap();
    expect_layer(s.verify(&pp, 2, &z0), IvcLayer::LinkHash, what);
  }
}

/// P4: a tampered running span. Span: the public λ is hashed into the link hash (LinkHash);
/// the witness λ alone fails the decider (SpanIndex).
#[test]
fn test_p4_rejects_tampered_span() {
  let (pp, prog) = setup::<Span>(2, PrimaryTemplate::R1cs);
  let ids = [0usize, 1, 1];
  let snark = run_chain(&pp, &prog, &ids, 3);
  let z0 = z0_for(&prog, &app0(), &ids);
  // λ is dense after the folds (not one-hot)
  assert!(snark
    .running()
    .1
    .lambda
    .iter()
    .all(|l| !bool::from(l.is_zero())));

  let mut s = snark.clone();
  s.running_mut().0.index[1] += F::ONE;
  expect_layer(s.verify(&pp, 3, &z0), IvcLayer::LinkHash, "public span");
  let mut s = snark.clone();
  s.running_mut().1.lambda[1] += F::ONE;
  expect_layer(s.verify(&pp, 3, &z0), IvcLayer::Decider, "witness span");
  let mut s = snark.clone();
  s.running_mut().0.index[0] += F::ONE;
  s.running_mut().1.lambda[0] += F::ONE;
  expect_layer(
    s.verify(&pp, 3, &z0),
    IvcLayer::LinkHash,
    "public and witness span",
  );
}

/// P4: a non-one-hot incoming selector. The in-circuit one-hot decomposition of k_prev rejects
/// forged bit assignments (two hot bits, none, or bits that do not sum to k), and the CycleFold
/// circuit rejects an index update with a non-unit vector (ι_0 + ι_1 for k = 0).
#[test]
fn test_p4_one_hot_gadget_rejects_forged_bits() {
  let case = |k: u64, bits: Option<&[bool]>| {
    let mut cs = TestConstraintSystem::<F>::new();
    let kv = AllocatedNum::alloc(cs.namespace(|| "k"), || Ok(F::from(k))).unwrap();
    one_hot_with(cs.namespace(|| "oh"), &kv, 4, bits).unwrap();
    cs.is_satisfied()
  };
  assert!(case(1, None));
  assert!(case(1, Some(&[false, true, false, false])));
  assert!(!case(1, Some(&[true, true, false, false])), "two hot bits");
  assert!(!case(0, Some(&[false, false, false, false])), "no hot bit");
  assert!(
    !case(2, Some(&[false, true, false, false])),
    "bit does not match k"
  );
  assert!(!case(4, None), "k outside the family");
}

#[test]
fn test_p4_cyclefold_rejects_non_unit_iota() {
  let mut rng = ChaCha20Rng::seed_from_u64(57);
  let iota = iota_coords(4, 3);
  let v = cf_inputs(&mut rng, &iota, 3, 0, false);
  assert!(cf_satisfied(&iota, 3, v.clone()));
  let pp = HfsParams::<E1>::new(
    CcsTemplate::new(3, vec![vec![0]], vec![F::ONE]).unwrap(),
    vec![CcsShape::new(1, 1, 1, vec![Vec::new(); 3]).unwrap(); 4],
  )
  .unwrap();
  let mut bad = v.clone();
  for j in 0..3 {
    let run = pp.iota(0)[j]; // any point; rebuild M_out = M_run + ρ(ι_0 + ι_1)
    let out = run + (pp.iota(0)[j] + pp.iota(1)[j]) * v.rho;
    bad.m[j] = (run.to_coordinates(), out.to_coordinates());
  }
  assert!(
    !cf_satisfied(&iota, 3, bad),
    "non-unit index vector accepted"
  );
}

/// Tampering with the final accumulators directly.
#[test]
fn test_ivc_rejects_tampered_accumulators() {
  let (pp, prog) = setup::<Direct>(2, PrimaryTemplate::R1cs);
  let ids = [0usize, 1, 0];
  let snark = run_chain(&pp, &prog, &ids, 3);
  let z0 = z0_for(&prog, &app0(), &ids);

  let mut s = snark.clone();
  s.running_mut().1.w[0] += F::ONE;
  expect_layer(s.verify(&pp, 3, &z0), IvcLayer::Decider, "running witness");

  let mut s = snark.clone();
  s.running_mut().1.lambda[0] += F::ONE;
  expect_layer(s.verify(&pp, 3, &z0), IvcLayer::Decider, "running lambda");

  let mut s = snark.clone();
  s.running_mut().3.W[0] += <E2 as Engine>::Scalar::ONE;
  expect_layer(
    s.verify(&pp, 3, &z0),
    IvcLayer::CycleFold,
    "CycleFold witness",
  );

  let mut s = snark.clone();
  s.running_mut().0.v[0] += F::ONE;
  expect_layer(
    s.verify(&pp, 3, &z0),
    IvcLayer::LinkHash,
    "running instance (hash-bound)",
  );

  let mut s = snark.clone();
  s.running_mut().0.index[0] = s.running_mut().0.index[1];
  expect_layer(
    s.verify(&pp, 3, &z0),
    IvcLayer::LinkHash,
    "running comm_M (hash-bound)",
  );
}

// ---------------------------------------------------------------------------------------------
// Sizes
// ---------------------------------------------------------------------------------------------

/// Per-component constraint counts (disjoint, sum to the total) for K = 2 and 4, Direct and
/// Span, plus the CycleFold circuit; setup converges within the caps; keys cover the padded
/// shapes; the primary circuit does not grow with the K shape sizes (succinct).
#[test]
fn test_constraint_breakdown() {
  for k in [2usize, 4] {
    for direct in [true, false] {
      let (rows, cf) = if direct {
        let (pp, prog) = setup::<Direct>(k, PrimaryTemplate::R1cs);
        assert!(super::ck_covers_padded(&pp));
        (breakdown_rows(&pp, &prog), pp.cyclefold_shape().num_cons)
      } else {
        let (pp, prog) = setup::<Span>(k, PrimaryTemplate::R1cs);
        assert!(super::ck_covers_padded(&pp));
        (breakdown_rows(&pp, &prog), pp.cyclefold_shape().num_cons)
      };
      println!(
        "[breakdown] K={k} {}: {rows:?}; CycleFold padded rows {cf}",
        if direct { "direct" } else { "span" }
      );
    }
  }
}

fn breakdown_rows<V: IvcVariant<E1>>(pp: &Pp<V>, prog: &Prog) -> Vec<(String, usize)> {
  let mut out = Vec::new();
  for id in 0..prog.num_predicates() {
    let b = primary_breakdown(pp, prog, id).unwrap();
    let c = primary_constraint_counts(pp, prog, id).unwrap();
    assert_eq!(
      b.total, c.num_constraints,
      "breakdown total = CountingCS total"
    );
    assert_eq!(b.by_category.values().sum::<usize>(), b.total, "disjoint");
    for k in b.by_category.keys() {
      assert!(CATEGORIES.contains(&k.as_str()), "unknown category {k}");
    }
    if id == 0 {
      out = CATEGORIES
        .iter()
        .map(|c| (c.to_string(), *b.by_category.get(*c).unwrap_or(&0)))
        .collect();
      out.push(("total".into(), b.total));
    }
  }
  out
}

/// The HFS gadget's size depends on (s, s', t, K) only, never on a shape's non-zeros: two
/// families with the same dimensions but different wiring give the same primary size.
#[test]
fn test_primary_circuit_is_succinct() {
  let (pp2, prog2) = setup::<Direct>(2, PrimaryTemplate::R1cs);
  let a = primary_constraint_counts(&pp2, &prog2, 0).unwrap();
  let b = primary_constraint_counts(&pp2, &prog2, 1).unwrap();
  // the two members differ only in the application part
  let ba = primary_breakdown(&pp2, &prog2, 0).unwrap();
  let bb = primary_breakdown(&pp2, &prog2, 1).unwrap();
  assert_eq!(
    a.num_constraints - ba.by_category["application"],
    b.num_constraints - bb.by_category["application"]
  );
  // the circuit is far smaller than the sum of the family's matrices (no matrix in-circuit)
  let nnz: usize = pp2.hfs().shapes().iter().map(CcsShape::nnz).sum();
  assert!(a.num_constraints < nnz);
}
