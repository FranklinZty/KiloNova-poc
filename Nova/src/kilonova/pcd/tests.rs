//! P6 tests: the μ/ν-generic HFS gadget (native = gadget), the multi-input CycleFold circuit,
//! the tree CycleFold folds (native = gadget), tree PCD with root verification (a = 2, small
//! trees with dummies), the rejection suite with detection layers, the breakdown and
//! succinctness of the merge circuit, and the 64-leaf trees for every arity (`#[ignore]`).
//!
//! Memory: run with `--release --test-threads=1` (16 GB machines).
use super::{
  breakdown::{node_breakdown, TREE_CATEGORIES},
  cyclefold::{
    cf_fold_fresh_prove, cf_fold_relaxed_prove, cyclefold_instance_witness_n, num_inputs_n,
    CycleFoldCircuitN, CycleFoldInputsN,
  },
  gadgets::{verify_hfs_multi, AllocProofN, CfAcc},
  node_constraint_counts, prove_tree, prove_tree_levels, LayoutRole, LeafTask, NodeProof, NodeRole,
  NodeTamper, RootStatement, TaskCtx, TreeLayer, TreeParams, TreeTask,
};
use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS},
  frontend::{
    num::AllocatedNum, shape_cs::ShapeCS, test_cs::TestConstraintSystem, ConstraintSystem,
  },
  gadgets::{
    ecc::AllocatedPoint,
    nonnative::{bignat::BigNat, util::f_to_nat},
  },
  kilonova::{
    hfs::{
      CcsShape, CcsTemplate, Direct, HfsParams, HfsProof, IncomingInstance, RunningInstance,
      RunningWitness, Span, Variant, NIFS,
    },
    ivc::{
      cyclefold::{num_inputs, Coords, CycleFoldCircuit},
      fixtures::ChainPredicates,
      gadgets::{
        alloc_vec, limbs_of, one_hot, verify_hfs, AllocIncoming, AllocIndex, AllocProof,
        AllocRunning, Expr, HfsGadgetParams, NnPoint,
      },
      IvcVariant, PrimaryTemplate,
    },
    shape_cs_to_shape,
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
use std::sync::OnceLock;

type E1 = PallasEngine;
type E2 = VestaEngine;
type F = <E1 as Engine>::Scalar;
type B = <E1 as Engine>::Base;

// ---------------------------------------------------------------------------------------------
// Helpers (oracle, kn-ccs pair family)
// ---------------------------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------------------------
// μ/ν-generic HFS gadget = native verifier
// ---------------------------------------------------------------------------------------------

fn iota_of(pp: &HfsParams<E1>) -> Vec<Vec<Coords<B>>> {
  (0..pp.k())
    .map(|i| pp.iota(i).iter().map(|c| c.to_coordinates()).collect())
    .collect()
}

fn alloc_running<V: IvcVariant<E1>, CS: ConstraintSystem<F>>(
  cs: &mut CS,
  pp: &HfsParams<E1>,
  run: &RunningInstance<E1, V>,
  n: &str,
) -> AllocRunning<F> {
  let index = if V::DIRECT {
    AllocIndex::Direct(
      V::index_coords(&run.index)
        .iter()
        .enumerate()
        .map(|(j, c)| {
          NnPoint::alloc(cs.namespace(|| format!("{n} M{j}")), Some(*c), false).unwrap()
        })
        .collect(),
    )
  } else {
    AllocIndex::Span(
      alloc_vec(
        cs.namespace(|| format!("{n} lambda")),
        Some(&V::index_scalars(&run.index)),
        pp.k(),
      )
      .unwrap(),
    )
  };
  AllocRunning {
    comm_w: NnPoint::alloc(
      cs.namespace(|| format!("{n} W")),
      Some(run.comm_w.to_coordinates()),
      false,
    )
    .unwrap(),
    index,
    u: AllocatedNum::alloc(cs.namespace(|| format!("{n} u")), || Ok(run.u)).unwrap(),
    io: alloc_vec(
      cs.namespace(|| format!("{n} io")),
      Some(&run.io),
      run.io.len(),
    )
    .unwrap(),
    r_x: alloc_vec(
      cs.namespace(|| format!("{n} r_x")),
      Some(&run.r_x),
      run.r_x.len(),
    )
    .unwrap(),
    r_y: alloc_vec(
      cs.namespace(|| format!("{n} r_y")),
      Some(&run.r_y),
      run.r_y.len(),
    )
    .unwrap(),
    v: alloc_vec(cs.namespace(|| format!("{n} v")), Some(&run.v), run.v.len()).unwrap(),
  }
}

fn alloc_incoming<CS: ConstraintSystem<F>>(
  cs: &mut CS,
  pp: &HfsParams<E1>,
  inc: &IncomingInstance<E1>,
  n: &str,
) -> AllocIncoming<F> {
  let k = AllocatedNum::alloc(cs.namespace(|| format!("{n} k")), || {
    Ok(F::from(inc.k as u64))
  })
  .unwrap();
  let k_bits = one_hot(cs.namespace(|| format!("{n} k bits")), &k, pp.k()).unwrap();
  AllocIncoming {
    k,
    k_bits,
    comm_w: NnPoint::alloc(
      cs.namespace(|| format!("{n} W")),
      Some(inc.comm_w.to_coordinates()),
      true,
    )
    .unwrap(),
    io: alloc_vec(
      cs.namespace(|| format!("{n} io")),
      Some(&inc.io),
      inc.io.len(),
    )
    .unwrap(),
  }
}

fn alloc_rows<CS: ConstraintSystem<F>>(
  cs: &mut CS,
  n: &str,
  m: &[Vec<F>],
) -> Vec<Vec<AllocatedNum<F>>> {
  m.iter()
    .enumerate()
    .map(|(i, r)| alloc_vec(cs.namespace(|| format!("{n}{i}")), Some(r), r.len()).unwrap())
    .collect()
}

/// Allocates the inputs and runs the multi gadget; returns (satisfied, outputs, gadget size).
fn run_multi<V: IvcVariant<E1>>(
  pp: &HfsParams<E1>,
  runs: &[RunningInstance<E1, V>],
  incs: &[IncomingInstance<E1>],
  pf: &HfsProof<E1>,
  active: bool,
) -> (bool, Vec<F>, usize) {
  let iota = iota_of(pp);
  let mut cs = TestConstraintSystem::<F>::new();
  let digest = AllocatedNum::alloc(cs.namespace(|| "digest"), || Ok(pp.digest())).unwrap();
  let ar: Vec<_> = runs
    .iter()
    .enumerate()
    .map(|(i, r)| alloc_running::<V, _>(&mut cs, pp, r, &format!("run{i}")))
    .collect();
  let ai: Vec<_> = incs
    .iter()
    .enumerate()
    .map(|(i, x)| alloc_incoming(&mut cs, pp, x, &format!("inc{i}")))
    .collect();
  let apf = AllocProofN {
    sc_x: alloc_rows(&mut cs, "sc_x", &pf.sc_x),
    sigma: alloc_rows(&mut cs, "sigma", &pf.sigma),
    tau: alloc_rows(&mut cs, "tau", &pf.tau),
    sc_y: alloc_rows(&mut cs, "sc_y", &pf.sc_y),
    eps: alloc_rows(&mut cs, "eps", &pf.eps),
    theta: alloc_rows(&mut cs, "theta", &pf.theta),
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
  let out = verify_hfs_multi::<E1, _>(
    cs.namespace(|| "hfs"),
    &gp,
    RO2ConstantsCircuit::<E1>::default(),
    &digest,
    &ar,
    &ai,
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
  assert_eq!(out.rho_bits.len(), crate::constants::NUM_CHALLENGE_BITS);
  (cs.is_satisfied(), vals, size)
}

/// μ non-trivial running instances (each the fold of two fresh ones, so u ≠ 1) and ν fresh
/// incoming instances of the kn-ccs pair family.
#[allow(clippy::type_complexity)]
fn multi_inputs<V: Variant<E1>>(
  pp: &HfsParams<E1>,
  fam: &Family<F>,
  tpl: PairTemplate,
  mu: usize,
  nu: usize,
  rng: &mut ChaCha20Rng,
) -> (
  Vec<RunningInstance<E1, V>>,
  Vec<RunningWitness<E1>>,
  Vec<IncomingInstance<E1>>,
  Vec<Vec<F>>,
) {
  let mut runs = Vec::new();
  let mut run_ws = Vec::new();
  for i in 0..mu {
    let (a, wa) = pair_input(pp, tpl, i % 2, F::random(&mut *rng));
    let first = NIFS::<E1, V>::prove(pp, &[], &[], &[a], &[wa]).unwrap();
    let (b, wb) = pair_input(pp, tpl, (i + 1) % 2, F::random(&mut *rng));
    let second = NIFS::<E1, V>::prove(
      pp,
      std::slice::from_ref(&first.instance),
      std::slice::from_ref(&first.witness),
      &[b],
      &[wb],
    )
    .unwrap();
    oracle(pp, fam, &second.instance, &second.witness);
    runs.push(second.instance);
    run_ws.push(second.witness);
  }
  let mut incs = Vec::new();
  let mut inc_ws = Vec::new();
  for l in 0..nu {
    let (x, w) = pair_input(pp, tpl, l % 2, F::random(&mut *rng));
    incs.push(x);
    inc_ws.push(w);
  }
  (runs, run_ws, incs, inc_ws)
}

fn multi_matches_native<V: IvcVariant<E1>>(tpl: PairTemplate, mu: usize, nu: usize) {
  let (fam, pp) = pair_family(tpl);
  let mut rng = ChaCha20Rng::seed_from_u64(60 + (mu * 10 + nu) as u64);
  let (runs, run_ws, incs, inc_ws) = multi_inputs::<V>(&pp, &fam, tpl, mu, nu, &mut rng);
  let out = NIFS::<E1, V>::prove(&pp, &runs, &run_ws, &incs, &inc_ws).unwrap();
  let (u, ch) = NIFS::<E1, V>::verify(&pp, &runs, &incs, &out.proof).unwrap();
  assert_eq!(u, out.instance);
  oracle(&pp, &fam, &u, &out.witness);

  let (ok, vals, size) = run_multi::<V>(&pp, &runs, &incs, &out.proof, true);
  assert!(ok, "gadget rejects an honest ({mu}, {nu}) fold");
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
  println!(
    "HFS multi gadget {} {} (mu, nu) = ({mu}, {nu}): {size} constraints (s = {}, s' = {})",
    V::NAME,
    tpl.name(),
    pp.s(),
    pp.s_prime()
  );

  // Tampering is rejected when active; the gate turns the checks off.
  let mut bad = out.proof.clone();
  bad.sc_x[0][1] += F::ONE;
  assert!(!run_multi::<V>(&pp, &runs, &incs, &bad, true).0);
  assert!(run_multi::<V>(&pp, &runs, &incs, &bad, false).0);
  let mut bad = out.proof.clone();
  bad.sigma[mu - 1][0] += F::ONE;
  assert!(!run_multi::<V>(&pp, &runs, &incs, &bad, true).0, "sigma");
  if nu > 0 {
    let mut bad = out.proof.clone();
    bad.tau[nu - 1][0] += F::ONE;
    assert!(!run_multi::<V>(&pp, &runs, &incs, &bad, true).0, "tau");
    let mut wrong = incs.clone();
    wrong[nu - 1].k = 1 - wrong[nu - 1].k;
    assert!(!run_multi::<V>(&pp, &runs, &wrong, &out.proof, true).0, "k");
  }
  let mut bad = out.proof.clone();
  bad.sc_y[pp.s_prime() - 1][2] += F::ONE;
  assert!(!run_multi::<V>(&pp, &runs, &incs, &bad, true).0, "sc_y");
  if mu > 1 {
    // running inputs in another order: another transcript
    let mut swapped = runs.clone();
    swapped.swap(0, 1);
    assert!(
      !run_multi::<V>(&pp, &swapped, &incs, &out.proof, true).0,
      "order"
    );
  }
}

/// Native `hfs::NIFS::verify` and the μ/ν-generic gadget produce the same challenges and
/// folded scalars for (μ, ν) ∈ {(1, 1), (2, 2), (2, 1), (4, 4)}; tampering is rejected (Direct;
/// R1CS and power-5 templates).
#[test]
fn test_transcript_native_matches_gadget_multi_direct() {
  for (mu, nu) in [(1, 1), (2, 2), (2, 1), (4, 4)] {
    multi_matches_native::<Direct>(PairTemplate::R1cs, mu, nu);
  }
  multi_matches_native::<Direct>(PairTemplate::Power5, 2, 2);
}

/// Same for Span (λ folded in-circuit with the weights ρ^i).
#[test]
fn test_transcript_native_matches_gadget_multi_span() {
  for (mu, nu) in [(1, 1), (2, 2), (2, 1), (4, 4)] {
    multi_matches_native::<Span>(PairTemplate::R1cs, mu, nu);
  }
  multi_matches_native::<Span>(PairTemplate::Power5, 2, 2);
}

/// For μ = ν = 1 the generic gadget costs exactly as many constraints as the P5 gadget
/// (`ivc::gadgets::verify_hfs`, untouched), on the same inputs, and both are satisfied.
#[test]
fn test_multi_gadget_matches_p5_gadget_size() {
  for direct in [true, false] {
    let (fam, pp) = pair_family(PairTemplate::R1cs);
    let mut rng = ChaCha20Rng::seed_from_u64(70);
    let (sizes, oks) = if direct {
      let (r, rw, i, iw) = multi_inputs::<Direct>(&pp, &fam, PairTemplate::R1cs, 1, 1, &mut rng);
      let out = NIFS::<E1, Direct>::prove(&pp, &r, &rw, &i, &iw).unwrap();
      let (ok_m, _, multi) = run_multi::<Direct>(&pp, &r, &i, &out.proof, true);
      let (ok_p, p5) = run_p5::<Direct>(&pp, &r[0], &i[0], &out.proof);
      ((multi, p5), (ok_m, ok_p))
    } else {
      let (r, rw, i, iw) = multi_inputs::<Span>(&pp, &fam, PairTemplate::R1cs, 1, 1, &mut rng);
      let out = NIFS::<E1, Span>::prove(&pp, &r, &rw, &i, &iw).unwrap();
      let (ok_m, _, multi) = run_multi::<Span>(&pp, &r, &i, &out.proof, true);
      let (ok_p, p5) = run_p5::<Span>(&pp, &r[0], &i[0], &out.proof);
      ((multi, p5), (ok_m, ok_p))
    };
    assert!(oks.0 && oks.1);
    assert_eq!(sizes.0, sizes.1, "multi gadget (1,1) vs P5 gadget");
  }
}

fn run_p5<V: IvcVariant<E1>>(
  pp: &HfsParams<E1>,
  run: &RunningInstance<E1, V>,
  inc: &IncomingInstance<E1>,
  pf: &HfsProof<E1>,
) -> (bool, usize) {
  let iota = iota_of(pp);
  let t = pp.t();
  let mut cs = TestConstraintSystem::<F>::new();
  let digest = AllocatedNum::alloc(cs.namespace(|| "digest"), || Ok(pp.digest())).unwrap();
  let ar = alloc_running::<V, _>(&mut cs, pp, run, "run");
  let ai = alloc_incoming(&mut cs, pp, inc, "inc");
  let apf = AllocProof {
    sc_x: alloc_rows(&mut cs, "sc_x", &pf.sc_x),
    sigma: alloc_vec(cs.namespace(|| "sigma"), Some(&pf.sigma[0]), t).unwrap(),
    tau: alloc_vec(cs.namespace(|| "tau"), Some(&pf.tau[0]), t).unwrap(),
    sc_y: alloc_rows(&mut cs, "sc_y", &pf.sc_y),
    eps: alloc_vec(cs.namespace(|| "eps"), Some(&pf.eps[0]), t + 1).unwrap(),
    theta: alloc_vec(cs.namespace(|| "theta"), Some(&pf.theta[0]), t + 1).unwrap(),
  };
  let gp = HfsGadgetParams {
    template: pp.template(),
    tag_input: V::TAG_INPUT,
    s: pp.s(),
    iota: &iota,
  };
  let act = AllocatedNum::alloc(cs.namespace(|| "active"), || Ok(F::ONE)).unwrap();
  let before = cs.num_constraints();
  verify_hfs::<E1, _>(
    cs.namespace(|| "hfs"),
    &gp,
    RO2ConstantsCircuit::<E1>::default(),
    &digest,
    &ar,
    &ai,
    &apf,
    &Expr::num(&act),
  )
  .unwrap();
  (cs.is_satisfied(), cs.num_constraints() - before)
}

// ---------------------------------------------------------------------------------------------
// Multi-input CycleFold circuit and tree CycleFold folds
// ---------------------------------------------------------------------------------------------

fn random_point(rng: &mut ChaCha20Rng, n: usize) -> crate::Commitment<E1> {
  let ck = <E1 as Engine>::CE::setup(b"kn-p6-test-points", n);
  let v: Vec<F> = (0..n).map(|_| F::random(&mut *rng)).collect();
  <E1 as Engine>::CE::commit(&ck, &v, &F::ZERO)
}

fn random_rho(rng: &mut ChaCha20Rng) -> F {
  let lo = rand_core::RngCore::next_u64(rng);
  let hi = rand_core::RngCore::next_u64(rng);
  F::from(lo) + F::from(hi) * F::from(1u64 << 32).square()
}

/// Honest inputs: μ + ν random points (or identities), RLC with ρ^i.
fn cf_inputs_n(
  rng: &mut ChaCha20Rng,
  k_family: usize,
  t_idx: usize,
  mu: usize,
  nu: usize,
  identity_runs: bool,
) -> CycleFoldInputsN<E1> {
  let rho = random_rho(rng);
  let pp = HfsParams::<E1>::new(
    CcsTemplate::new(t_idx.max(1), vec![vec![0]], vec![F::ONE]).unwrap(),
    vec![CcsShape::new(1, 1, 1, vec![Vec::new(); t_idx.max(1)]).unwrap(); k_family],
  )
  .unwrap();
  let pick = |rng: &mut ChaCha20Rng, n| {
    if identity_runs {
      crate::Commitment::<E1>::default()
    } else {
      random_point(rng, n)
    }
  };
  let mut w: Vec<crate::Commitment<E1>> = (0..mu).map(|_| pick(rng, 4)).collect();
  for _ in 0..nu {
    w.push(random_point(rng, 4));
  }
  let pw: Vec<F> = (0..mu + nu)
    .scan(F::ONE, |acc, _| {
      let v = *acc;
      *acc *= rho;
      Some(v)
    })
    .collect();
  let w_out = w
    .iter()
    .zip(&pw)
    .fold(crate::Commitment::<E1>::default(), |acc, (c, p)| {
      acc + *c * *p
    });
  let ks: Vec<usize> = (0..nu)
    .map(|l| (rand_core::RngCore::next_u32(rng) as usize + l) % k_family)
    .collect();
  let m = (0..t_idx)
    .map(|j| {
      let runs: Vec<crate::Commitment<E1>> = (0..mu).map(|_| pick(rng, 3)).collect();
      let mut out = crate::Commitment::<E1>::default();
      for (i, r) in runs.iter().enumerate() {
        out = out + *r * pw[i];
      }
      for (l, k) in ks.iter().enumerate() {
        out = out + pp.iota(*k)[j] * pw[mu + l];
      }
      (
        runs.iter().map(|r| r.to_coordinates()).collect(),
        out.to_coordinates(),
      )
    })
    .collect();
  CycleFoldInputsN {
    rho,
    ks,
    w: w.iter().map(|c| c.to_coordinates()).collect(),
    w_out: w_out.to_coordinates(),
    m,
  }
}

fn cf_iota(k: usize, t_idx: usize) -> Vec<Vec<Coords<B>>> {
  let pp = HfsParams::<E1>::new(
    CcsTemplate::new(t_idx.max(1), vec![vec![0]], vec![F::ONE]).unwrap(),
    vec![CcsShape::new(1, 1, 1, vec![Vec::new(); t_idx.max(1)]).unwrap(); k],
  )
  .unwrap();
  (0..k)
    .map(|i| pp.iota(i).iter().map(|c| c.to_coordinates()).collect())
    .collect()
}

fn cf_n_satisfied(
  iota: &[Vec<Coords<B>>],
  mu: usize,
  nu: usize,
  t_idx: usize,
  v: CycleFoldInputsN<E1>,
) -> bool {
  let c = CycleFoldCircuitN::<E1> {
    iota,
    mu,
    nu,
    t_idx,
    inputs: Some(v.clone()),
  };
  let mut cs = TestConstraintSystem::<B>::new();
  c.synthesize(&mut cs).unwrap();
  let mut ws = crate::frontend::solver::SatisfyingAssignment::<E2>::new();
  c.synthesize(&mut ws).unwrap();
  assert_eq!(ws.input_assignment()[1..], c.public_inputs(&v)[..]);
  assert_eq!(ws.input_assignment().len(), num_inputs_n(mu, nu, t_idx) + 1);
  cs.is_satisfied()
}

/// The multi-input CycleFold circuit accepts honest RLCs (incl. identity running points) for
/// (μ, ν) ∈ {(1, 1), (2, 2), (4, 4)}, Direct and Span, and rejects a wrong W_out, ρ, k and
/// M_out. For μ = ν = 1 it has the P5 circuit's size and inputs.
#[test]
fn test_cyclefold_multi_circuit() {
  let mut rng = ChaCha20Rng::seed_from_u64(61);
  for (mu, nu) in [(1usize, 1usize), (2, 2), (4, 4)] {
    for (k_family, t_idx) in [(4usize, 3usize), (3, 0)] {
      let iota = cf_iota(k_family, t_idx);
      for identity_runs in [false, true] {
        let v = cf_inputs_n(&mut rng, k_family, t_idx, mu, nu, identity_runs);
        assert!(
          cf_n_satisfied(&iota, mu, nu, t_idx, v.clone()),
          "honest ({mu},{nu}) t={t_idx}"
        );
        let mut bad = v.clone();
        bad.w_out.0 += B::ONE;
        assert!(!cf_n_satisfied(&iota, mu, nu, t_idx, bad), "W_out");
        let mut bad = v.clone();
        bad.rho += F::ONE;
        assert!(!cf_n_satisfied(&iota, mu, nu, t_idx, bad), "rho");
        if t_idx > 0 {
          let mut bad = v.clone();
          bad.ks[nu - 1] = (bad.ks[nu - 1] + 1) % k_family;
          assert!(!cf_n_satisfied(&iota, mu, nu, t_idx, bad), "k");
          let mut bad = v.clone();
          bad.m[t_idx - 1].1 = v.w[0];
          assert!(!cf_n_satisfied(&iota, mu, nu, t_idx, bad), "M_out");
        }
      }
      let mut cs = ShapeCS::<E2>::new();
      CycleFoldCircuitN::<E1> {
        iota: &iota,
        mu,
        nu,
        t_idx,
        inputs: None,
      }
      .synthesize(&mut cs)
      .unwrap();
      let n = shape_cs_to_shape(&cs);
      println!(
        "CycleFold (mu, nu) = ({mu}, {nu}), t_idx = {t_idx}: {} constraints, {} inputs",
        n.num_cons, n.num_io
      );
      if mu == 1 && nu == 1 {
        let mut cs = ShapeCS::<E2>::new();
        CycleFoldCircuit::<E1> {
          iota: &iota,
          t_idx,
          inputs: None,
        }
        .synthesize(&mut cs)
        .unwrap();
        let p5 = shape_cs_to_shape(&cs);
        assert_eq!((n.num_cons, n.num_io), (p5.num_cons, p5.num_io));
        assert_eq!(n.num_io, num_inputs(t_idx));
      }
    }
  }
}

/// The relaxed–relaxed and fresh CycleFold folds of the tree: gadget = native (`W, E, u, X`),
/// and the native results are satisfied relaxed instances.
#[test]
fn test_cf_tree_fold_native_matches_gadget() {
  let mut rng = ChaCha20Rng::seed_from_u64(62);
  let (mu, nu, t_idx, k_family) = (2, 2, 3, 4);
  let iota = cf_iota(k_family, t_idx);
  let mut cs = ShapeCS::<E2>::new();
  CycleFoldCircuitN::<E1> {
    iota: &iota,
    mu,
    nu,
    t_idx,
    inputs: None,
  }
  .synthesize(&mut cs)
  .unwrap();
  let shape = shape_cs_to_shape(&cs).pad();
  let ck = <E2 as Engine>::CE::setup(b"kn-p6-test-cf", shape.num_cons.max(shape.num_vars));
  let ro = ROConstants::<E2>::default();
  let pp_digest = F::from(4343);
  let n = num_inputs_n(mu, nu, t_idx);
  let fresh = |rng: &mut ChaCha20Rng| {
    let c = CycleFoldCircuitN::<E1> {
      iota: &iota,
      mu,
      nu,
      t_idx,
      inputs: Some(cf_inputs_n(rng, k_family, t_idx, mu, nu, false)),
    };
    cyclefold_instance_witness_n::<E1, E2>(&c, &shape, &ck).unwrap()
  };
  // two accumulators, each two fresh folds into the default
  let mut accs = Vec::new();
  for _ in 0..2 {
    let mut u = RelaxedR1CSInstance::<E2>::default(&ck, &shape);
    let mut w = RelaxedR1CSWitness::<E2>::default(&shape);
    for _ in 0..2 {
      let (x, xw) = fresh(&mut rng);
      shape.is_sat(&ck, &x, &xw).unwrap();
      let (_, nu_, nw) = cf_fold_fresh_prove(&ck, &ro, pp_digest, &shape, &u, &w, &x, &xw).unwrap();
      shape.is_sat_relaxed(&ck, &nu_, &nw).unwrap();
      u = nu_;
      w = nw;
    }
    accs.push((u, w));
  }
  let (t_rel, merged_u, merged_w) = cf_fold_relaxed_prove(
    &ck, &ro, pp_digest, &shape, &accs[0].0, &accs[0].1, &accs[1].0, &accs[1].1,
  )
  .unwrap();
  shape.is_sat_relaxed(&ck, &merged_u, &merged_w).unwrap();
  let (x, xw) = fresh(&mut rng);
  let (t_fresh, final_u, final_w) =
    cf_fold_fresh_prove(&ck, &ro, pp_digest, &shape, &merged_u, &merged_w, &x, &xw).unwrap();
  shape.is_sat_relaxed(&ck, &final_u, &final_w).unwrap();

  let mut cs = TestConstraintSystem::<F>::new();
  let params = AllocatedNum::alloc(cs.namespace(|| "pp"), || Ok(pp_digest)).unwrap();
  let a0 = CfAcc::<E2>::alloc(cs.namespace(|| "U0"), Some(&accs[0].0), n).unwrap();
  let a1 = CfAcc::<E2>::alloc(cs.namespace(|| "U1"), Some(&accs[1].0), n).unwrap();
  let tr =
    AllocatedPoint::<E2>::alloc(cs.namespace(|| "T rel"), Some(t_rel.to_coordinates())).unwrap();
  let merged = a0
    .fold_relaxed(
      cs.namespace(|| "relaxed"),
      &params,
      &a1,
      &tr,
      ROConstantsCircuit::<E2>::default(),
    )
    .unwrap();
  let cw =
    AllocatedPoint::<E2>::alloc(cs.namespace(|| "w"), Some(x.comm_W.to_coordinates())).unwrap();
  let tf =
    AllocatedPoint::<E2>::alloc(cs.namespace(|| "T"), Some(t_fresh.to_coordinates())).unwrap();
  let xs: Vec<BigNat<F>> = x
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
  let out = merged
    .fold_fresh(
      cs.namespace(|| "fresh"),
      &params,
      &cw,
      &xs,
      &tf,
      ROConstantsCircuit::<E2>::default(),
    )
    .unwrap();
  assert!(cs.is_satisfied(), "{:?}", cs.which_is_unsatisfied());
  let check = |g: &CfAcc<E2>, e: &RelaxedR1CSInstance<E2>| {
    for (p, c) in [(&g.w, &e.comm_W), (&g.e, &e.comm_E)] {
      let (x, y, inf) = c.to_coordinates();
      assert_eq!(p.x.get_value(), Some(x));
      assert_eq!(p.y.get_value(), Some(y));
      assert_eq!(
        p.is_infinity.get_value(),
        Some(if inf { F::ONE } else { F::ZERO })
      );
    }
    let ul: Vec<F> = g.u.iter().map(|l| l.get_value().unwrap()).collect();
    assert_eq!(ul, limbs_of::<B, F>(&e.u), "u");
    for (xi, ex) in g.x.iter().zip(&e.X) {
      let limbs: Vec<F> = xi.iter().map(|l| l.get_value().unwrap()).collect();
      assert_eq!(limbs, limbs_of::<B, F>(ex));
    }
  };
  check(&merged, &merged_u);
  check(&out, &final_u);
}

// ---------------------------------------------------------------------------------------------
// Tree PCD (a = 2, Direct): shared parameters
// ---------------------------------------------------------------------------------------------

type Pp = TreeParams<E1, E2, Direct>;
type Proof = NodeProof<E1, E2, Direct>;
type Leaf = ChainPredicates<F>;

struct Fixture {
  leaf: Leaf,
  pp: Pp,
}

fn leaf_family() -> (Leaf, Vec<String>) {
  let leaf = ChainPredicates::<F>::new(2, false);
  let ids = (0..2).map(|k| leaf.member_id(k)).collect();
  (leaf, ids)
}

/// a = 2 parameters, shared by the tree tests of this process (setup ≈ 20 s).
fn fx() -> &'static Fixture {
  static FX: OnceLock<Fixture> = OnceLock::new();
  FX.get_or_init(|| {
    let (leaf, ids) = leaf_family();
    let (pp, rep) = Pp::setup(&leaf, &ids, 2, PrimaryTemplate::R1cs).unwrap();
    assert!(rep.iterations.len() <= crate::kilonova::MAX_SETUP_ITERATIONS);
    Fixture { leaf, pp }
  })
}

fn eval(leaf: &Leaf) -> impl Fn(usize, &[F]) -> Vec<F> + '_ {
  move |k, x| leaf.output(k, x)
}

fn expect_tree<T: std::fmt::Debug>(res: Result<T, super::TreeError>, layer: TreeLayer, what: &str) {
  match res {
    Ok(v) => panic!("{what}: accepted ({v:?})"),
    Err(e) => assert_eq!(
      e.layer(),
      layer,
      "{what}: rejected at {:?} ({e})",
      e.layer()
    ),
  }
}

fn leaves(f: &Fixture, task: &TreeTask<F>) -> Vec<Proof> {
  (0..task.num_leaves())
    .map(|p| Proof::prove_leaf(&f.pp, &f.leaf, task, p).unwrap())
    .collect()
}

/// Honest small trees (L = 4: no padding; L = 5, 6: dummy subtrees) verify without any tree
/// structure, prove the task-derived root statement, and the root accumulator passes the
/// kn-ccs oracle. The sequential and level drivers prove the same statement.
#[test]
fn test_tree_a2_small() {
  let f = fx();
  let fam = kn_family(f.pp.hfs());
  for (l, dummies) in [(4usize, 0usize), (5, 2), (6, 1)] {
    let task = TreeTask::<F>::generate(100 + l as u64, l, 2);
    let layout = task.layout(2);
    assert_eq!(layout.num_dummies(), dummies, "L = {l}");
    assert_eq!(layout.num_leaves(), l);
    let (root, run) = prove_tree(&f.pp, &f.leaf, &task).unwrap();
    assert_eq!(
      run.nodes.len(),
      layout.num_leaves() + layout.num_dummies() + layout.num_merges()
    );
    let expected = f.pp.root_statement(&task, eval(&f.leaf));
    let got = root.verify_statement(&f.pp, &expected).unwrap();
    assert_eq!(got.result, task.expected_result(eval(&f.leaf)));
    assert_eq!((got.lo, got.hi), (0, layout.capacity));
    let (u, w) = root.running();
    oracle(f.pp.hfs(), &fam, u, w);
    if l == 5 {
      let (root2, _) = prove_tree_levels(&f.pp, &f.leaf, &task, false).unwrap();
      assert_eq!(root2.verify_root(&f.pp).unwrap(), expected);
    }
  }
}

/// Two leaves with the same predicate and input at different positions are a valid task (the
/// tree hash and result separate them by position); the same position twice is rejected by
/// `test_tree_rejects_duplicate_leaf`.
#[test]
fn test_tree_same_input_different_positions() {
  let f = fx();
  let x = vec![F::from(11), F::from(13)];
  let task = TreeTask::new(
    "kn-p6-repeat",
    vec![
      LeafTask {
        k: 1,
        x: vec![F::from(2), F::from(3)],
      },
      LeafTask { k: 0, x: x.clone() },
      LeafTask { k: 0, x: x.clone() },
      LeafTask {
        k: 1,
        x: vec![F::from(5), F::from(7)],
      },
    ],
  );
  let (root, _) = prove_tree(&f.pp, &f.leaf, &task).unwrap();
  let expected = f.pp.root_statement(&task, eval(&f.leaf));
  root.verify_statement(&f.pp, &expected).unwrap();
  assert_ne!(f.pp.leaf_hash(1, 0, &x), f.pp.leaf_hash(2, 0, &x));
  // the identical leaves contribute β^1 y and β^2 y
  let y = f.leaf.output(0, &x);
  assert_ne!(y, vec![F::ZERO; 2]);
}

/// Duplicate leaves (the same position twice) are rejected: by the honest API (Input), and when
/// a prover skips the native checks, by the merge circuit (the node's CCCS is unsatisfied). A
/// root over `[(0,0), [2,4)]` has the right range, so the root verifier reaches RootIncoming; a
/// root whose children carry an impossible range is already rejected at Statement, and its own
/// circuit is unsatisfied too.
#[test]
fn test_tree_rejects_duplicate_leaf() {
  let f = fx();
  let task = TreeTask::<F>::generate(201, 4, 2);
  let ctx = TaskCtx::of(&task);
  let lv = leaves(f, &task);
  let raw = |kids: &[&Proof]| {
    Proof::prove_node_tampered(&f.pp, &f.leaf, ctx, kids, false, NodeTamper::None).unwrap()
  };
  expect_tree(
    Proof::prove_node(&f.pp, &f.leaf, &task, &[&lv[1], &lv[1]]),
    TreeLayer::Input,
    "duplicate (API)",
  );
  let dup = raw(&[&lv[0], &lv[0]]);
  expect_tree(
    dup.check_incoming(&f.pp),
    TreeLayer::RootIncoming,
    "duplicate node circuit",
  );
  let n23 = Proof::prove_node(&f.pp, &f.leaf, &task, &[&lv[2], &lv[3]]).unwrap();
  let root = raw(&[&dup, &n23]);
  expect_tree(
    root.verify_root(&f.pp),
    TreeLayer::RootIncoming,
    "duplicate below the root",
  );
  // leaf 1 twice: the root's range is no longer [0, 4)
  let dup1 = raw(&[&lv[1], &lv[1]]);
  let root = raw(&[&dup1, &n23]);
  expect_tree(
    root.verify_root(&f.pp),
    TreeLayer::Statement,
    "duplicate (range)",
  );
  expect_tree(
    root.check_incoming(&f.pp),
    TreeLayer::RootIncoming,
    "duplicate (root circuit)",
  );
  // a duplicated subtree at the root
  let root = raw(&[&n23, &n23]);
  expect_tree(
    root.verify_root(&f.pp),
    TreeLayer::Statement,
    "duplicated subtree (range)",
  );
  expect_tree(
    root.check_incoming(&f.pp),
    TreeLayer::RootIncoming,
    "duplicated subtree (circuit)",
  );
}

/// Missing leaves are rejected: a gap (Input; circuit → RootIncoming), a dummy below L
/// (Input; dummy circuit unsatisfied → RootIncoming), and a complete proof of a shorter task
/// against the full task's statement (Statement).
#[test]
fn test_tree_rejects_missing_leaf() {
  let f = fx();
  let task = TreeTask::<F>::generate(202, 4, 2);
  let ctx = TaskCtx::of(&task);
  let lv = leaves(f, &task);
  let n01 = Proof::prove_node(&f.pp, &f.leaf, &task, &[&lv[0], &lv[1]]).unwrap();
  // gap: [2, 3) then [3, 4) missing → children [0,1), [2,3)
  expect_tree(
    Proof::prove_node(&f.pp, &f.leaf, &task, &[&lv[0], &lv[2]]),
    TreeLayer::Input,
    "gap (API)",
  );
  let gap = Proof::prove_node_tampered(
    &f.pp,
    &f.leaf,
    ctx,
    &[&lv[0], &lv[2]],
    false,
    NodeTamper::None,
  )
  .unwrap();
  expect_tree(
    gap.check_incoming(&f.pp),
    TreeLayer::RootIncoming,
    "gap circuit",
  );
  // a dummy in place of the real leaf 3
  expect_tree(
    Proof::prove_dummy(&f.pp, &f.leaf, &task, 3, 4),
    TreeLayer::Input,
    "dummy below L (API)",
  );
  let d3 = Proof::prove_dummy_raw(&f.pp, &f.leaf, ctx, 3, 4).unwrap();
  expect_tree(
    d3.check_incoming(&f.pp),
    TreeLayer::RootIncoming,
    "dummy below L circuit",
  );
  let n23 =
    Proof::prove_node_tampered(&f.pp, &f.leaf, ctx, &[&lv[2], &d3], false, NodeTamper::None)
      .unwrap();
  let root = Proof::prove_node(&f.pp, &f.leaf, &task, &[&n01, &n23]).unwrap();
  expect_tree(
    root.verify_root(&f.pp),
    TreeLayer::RootIncoming,
    "dummy below L at the root",
  );
  // a valid proof of the first 3 leaves claimed for the 4-leaf task
  let short = TreeTask::new(task.label(), task.leaves()[..3].to_vec());
  let (root3, _) = prove_tree(&f.pp, &f.leaf, &short).unwrap();
  root3.verify_root(&f.pp).unwrap();
  let expected = f.pp.root_statement(&task, eval(&f.leaf));
  expect_tree(
    root3.verify_statement(&f.pp, &expected),
    TreeLayer::Statement,
    "shorter task",
  );
}

/// Cross-task splicing (a subtree of another task) is rejected: honest API (Input), merge
/// circuit (the child does not hash under this node's task context → RootIncoming), and a
/// complete proof of the other task against this task's statement (Statement).
#[test]
fn test_tree_rejects_cross_task_splice() {
  let f = fx();
  let task_a = TreeTask::<F>::generate(203, 4, 2);
  let task_b = TreeTask::<F>::generate(204, 4, 2);
  let (ctx_a, ctx_b) = (TaskCtx::of(&task_a), TaskCtx::of(&task_b));
  assert_ne!(ctx_a.task_id, ctx_b.task_id);
  let la = leaves(f, &task_a);
  let lb = leaves(f, &task_b);
  let a01 = Proof::prove_node(&f.pp, &f.leaf, &task_a, &[&la[0], &la[1]]).unwrap();
  let b23 = Proof::prove_node(&f.pp, &f.leaf, &task_b, &[&lb[2], &lb[3]]).unwrap();
  expect_tree(
    Proof::prove_node(&f.pp, &f.leaf, &task_a, &[&a01, &b23]),
    TreeLayer::Input,
    "splice (API)",
  );
  let root = Proof::prove_node_tampered(
    &f.pp,
    &f.leaf,
    ctx_a,
    &[&a01, &b23],
    false,
    NodeTamper::None,
  )
  .unwrap();
  expect_tree(
    root.check_incoming(&f.pp),
    TreeLayer::RootIncoming,
    "splice circuit",
  );
  expect_tree(
    root.verify_root(&f.pp),
    TreeLayer::RootIncoming,
    "splice root",
  );
  // a leaf of task B spliced under a node of task A
  let mixed = Proof::prove_node_tampered(
    &f.pp,
    &f.leaf,
    ctx_a,
    &[&la[0], &lb[1]],
    false,
    NodeTamper::None,
  )
  .unwrap();
  expect_tree(
    mixed.check_incoming(&f.pp),
    TreeLayer::RootIncoming,
    "spliced leaf",
  );
  // task B's whole valid tree is not a proof for task A
  let b01 = Proof::prove_node(&f.pp, &f.leaf, &task_b, &[&lb[0], &lb[1]]).unwrap();
  let root_b = Proof::prove_node(&f.pp, &f.leaf, &task_b, &[&b01, &b23]).unwrap();
  root_b.verify_root(&f.pp).unwrap();
  let expected_a = f.pp.root_statement(&task_a, eval(&f.leaf));
  expect_tree(
    root_b.verify_statement(&f.pp, &expected_a),
    TreeLayer::Statement,
    "other task",
  );
}

/// Swapped children (illegal predecessor order) are rejected at a leaf pair and at the root:
/// honest API (Input), merge circuit (RootIncoming).
#[test]
fn test_tree_rejects_swapped_children() {
  let f = fx();
  let task = TreeTask::<F>::generate(205, 4, 2);
  let ctx = TaskCtx::of(&task);
  let lv = leaves(f, &task);
  expect_tree(
    Proof::prove_node(&f.pp, &f.leaf, &task, &[&lv[1], &lv[0]]),
    TreeLayer::Input,
    "swap (API)",
  );
  let sw = Proof::prove_node_tampered(
    &f.pp,
    &f.leaf,
    ctx,
    &[&lv[1], &lv[0]],
    false,
    NodeTamper::None,
  )
  .unwrap();
  expect_tree(
    sw.check_incoming(&f.pp),
    TreeLayer::RootIncoming,
    "swapped leaves",
  );
  let n01 = Proof::prove_node(&f.pp, &f.leaf, &task, &[&lv[0], &lv[1]]).unwrap();
  let n23 = Proof::prove_node(&f.pp, &f.leaf, &task, &[&lv[2], &lv[3]]).unwrap();
  let root =
    Proof::prove_node_tampered(&f.pp, &f.leaf, ctx, &[&n23, &n01], false, NodeTamper::None)
      .unwrap();
  // the swapped root claims the range [2, 2): Statement; its own circuit is unsatisfied too
  expect_tree(
    root.verify_root(&f.pp),
    TreeLayer::Statement,
    "swapped subtrees (range)",
  );
  expect_tree(
    root.check_incoming(&f.pp),
    TreeLayer::RootIncoming,
    "swapped subtrees (circuit)",
  );
  // swapped leaves one level below the root: the range check passes, the recursion catches it
  let root =
    Proof::prove_node_tampered(&f.pp, &f.leaf, ctx, &[&sw, &n23], false, NodeTamper::None).unwrap();
  expect_tree(
    root.check_incoming(&f.pp),
    TreeLayer::RootIncoming,
    "swapped leaves below root",
  );
  // the honest root verifies
  let root = Proof::prove_node(&f.pp, &f.leaf, &task, &[&n01, &n23]).unwrap();
  root
    .verify_statement(&f.pp, &f.pp.root_statement(&task, eval(&f.leaf)))
    .unwrap();
}

/// Forged predecessors are rejected: a forged child statement, a forged child proof (garbage
/// witness under the child's io), swapped child accumulators (each makes the merge circuit
/// unsatisfied → RootIncoming, also when one level below the root), and tampered root
/// accumulators or statement (LinkHash, Decider, CycleFold, Statement). Swapping the
/// accumulators of two leaves changes nothing (both are the default), so that tamper is
/// exercised at the root, whose children carry real accumulators.
#[test]
fn test_tree_rejects_forged_predecessor() {
  let f = fx();
  let task = TreeTask::<F>::generate(206, 4, 2);
  let ctx = TaskCtx::of(&task);
  let lv = leaves(f, &task);
  let n23 = Proof::prove_node(&f.pp, &f.leaf, &task, &[&lv[2], &lv[3]]).unwrap();
  for tamper in [NodeTamper::ChildResult(0), NodeTamper::ChildIncoming(1)] {
    let bad =
      Proof::prove_node_tampered(&f.pp, &f.leaf, ctx, &[&lv[0], &lv[1]], true, tamper).unwrap();
    expect_tree(
      bad.check_incoming(&f.pp),
      TreeLayer::RootIncoming,
      &format!("{tamper:?} node"),
    );
    let root = Proof::prove_node(&f.pp, &f.leaf, &task, &[&bad, &n23]).unwrap();
    expect_tree(
      root.verify_root(&f.pp),
      TreeLayer::RootIncoming,
      &format!("{tamper:?} below root"),
    );
  }
  // at the root itself
  let n01 = Proof::prove_node(&f.pp, &f.leaf, &task, &[&lv[0], &lv[1]]).unwrap();
  for tamper in [
    NodeTamper::ChildResult(1),
    NodeTamper::ChildIncoming(0),
    NodeTamper::SwapRunning,
  ] {
    let root =
      Proof::prove_node_tampered(&f.pp, &f.leaf, ctx, &[&n01, &n23], true, tamper).unwrap();
    expect_tree(
      root.verify_root(&f.pp),
      TreeLayer::RootIncoming,
      &format!("{tamper:?} at root"),
    );
  }
  // tampered final proof
  let root = Proof::prove_node(&f.pp, &f.leaf, &task, &[&n01, &n23]).unwrap();
  root.verify_root(&f.pp).unwrap();
  let mut r = root.clone();
  r.parts_mut().0.result[1] += F::ONE;
  expect_tree(r.verify_root(&f.pp), TreeLayer::LinkHash, "result");
  let mut r = root.clone();
  r.parts_mut().0.tree_hash += F::ONE;
  expect_tree(r.verify_root(&f.pp), TreeLayer::LinkHash, "tree hash");
  let mut r = root.clone();
  r.parts_mut().0.hi = 8;
  expect_tree(r.verify_root(&f.pp), TreeLayer::Statement, "range");
  let mut r = root.clone();
  r.parts_mut().2.w[0] += F::ONE;
  expect_tree(r.verify_root(&f.pp), TreeLayer::Decider, "running witness");
  let mut r = root.clone();
  r.parts_mut().4.W[0] += <E2 as Engine>::Scalar::ONE;
  expect_tree(
    r.verify_root(&f.pp),
    TreeLayer::CycleFold,
    "cyclefold witness",
  );
  let mut r = root.clone();
  r.parts_mut().1.u += F::ONE;
  expect_tree(
    r.verify_root(&f.pp),
    TreeLayer::LinkHash,
    "running instance",
  );
}

/// Per-component counts of every member (disjoint, sum to the CountingCS total); setup within
/// the caps; keys cover the padded shapes. The merge circuit is succinct: its size does not
/// depend on the members' wiring (a different leaf family gives the same merge circuit) and is
/// far below the family's non-zeros.
#[test]
fn test_merge_circuit_breakdown_and_succinctness() {
  let f = fx();
  assert!(super::ck_covers_padded(&f.pp));
  for id in 0..f.pp.hfs().k() {
    let role = f.pp.role(id).unwrap();
    let b = node_breakdown(&f.pp, &f.leaf, role).unwrap();
    let c = node_constraint_counts(&f.pp, &f.leaf, role).unwrap();
    assert_eq!(
      b.total, c.num_constraints,
      "breakdown total = CountingCS total"
    );
    assert_eq!(b.by_category.values().sum::<usize>(), b.total, "disjoint");
    for k in b.by_category.keys() {
      assert!(
        TREE_CATEGORIES.contains(&k.as_str()),
        "unknown category {k}"
      );
    }
    println!(
      "[breakdown a=2] {role:?}: {:?} total {}",
      b.by_category, b.total
    );
  }
  let merge = node_constraint_counts(&f.pp, &f.leaf, NodeRole::Merge).unwrap();
  // members 2 and 3 of the chain family instead of 0 and 1: same merge circuit
  let other = ChainPredicates::<F>::new(4, false);
  let merge_other = node_constraint_counts(&f.pp, &other, NodeRole::Merge).unwrap();
  assert_eq!(merge.num_constraints, merge_other.num_constraints);
  let nnz: usize = f.pp.hfs().shapes().iter().map(CcsShape::nnz).sum();
  assert!(merge.num_constraints < nnz);
  // the leaf members really differ in wiring
  assert_ne!(
    f.pp.hfs().shape(0).matrices(),
    f.pp.hfs().shape(1).matrices()
  );
  assert_eq!(f.pp.mu(), 2);
  assert_eq!(f.pp.nu(), 2);
}

/// The layout rule: counts of leaves, merges and dummies for several (L, a), and every position
/// below L is covered by exactly one leaf.
#[test]
fn test_tree_layout_dummy_rule() {
  for (l, a, merges, dummies) in [
    (64usize, 2usize, 63usize, 0usize),
    (64, 4, 21, 0),
    (64, 8, 9, 0),
    (5, 2, 6, 2),
    (6, 2, 6, 1),
    (5, 4, 3, 5),
    (1, 2, 0, 0),
    (9, 8, 3, 13),
  ] {
    let task = TreeTask::<F>::generate(1, l, 2);
    let lay = task.layout(a);
    assert_eq!(lay.num_leaves(), l);
    assert_eq!(lay.num_merges(), merges, "merges L={l} a={a}");
    assert_eq!(lay.num_dummies(), dummies, "dummies L={l} a={a}");
    let mut covered = vec![0u32; lay.capacity as usize];
    for n in lay.levels[0].iter() {
      if let LayoutRole::Leaf { p, .. } = n.role {
        covered[p] += 1;
      }
    }
    assert!(covered[..l].iter().all(|&c| c == 1));
    // every dummy lies beyond L, and its parent does not
    for n in lay.levels.iter().flatten() {
      if n.role == LayoutRole::Dummy {
        assert!(n.lo >= l as u64);
      }
    }
  }
}

// ---------------------------------------------------------------------------------------------
// 64 leaves, every arity (long; run explicitly)
// ---------------------------------------------------------------------------------------------

fn tree64<V: IvcVariant<E1>>(a: usize, seed: u64) -> RootStatement<F> {
  let (leaf, ids) = leaf_family();
  let (pp, rep) = TreeParams::<E1, E2, V>::setup(&leaf, &ids, a, PrimaryTemplate::R1cs).unwrap();
  println!(
    "[tree64] {} a={a}: m = {}, CycleFold inputs {}, iterations {}",
    V::NAME,
    rep.primary_m,
    pp.cyclefold_num_inputs(),
    rep.iterations.len()
  );
  let task = TreeTask::<F>::generate(seed, 64, 2);
  let (root, run) = prove_tree(&pp, &leaf, &task).unwrap();
  let lay = task.layout(a);
  assert_eq!(run.nodes.len(), 64 + lay.num_merges());
  let expected = pp.root_statement(&task, eval(&leaf));
  root.verify_statement(&pp, &expected).unwrap()
}

/// 64 fixed real leaf tasks (mixed predicates): every supported arity proves and verifies the
/// same target result R (the tree hashes differ with the shape). Supported: Direct a = 2, 4 and
/// Span a = 8; Direct a = 8 is rejected by setup (its merge circuit exceeds
/// `MAX_SETUP_CONSTRAINTS`, which is not raised).
#[test]
#[ignore = "long: 64-leaf trees for a = 2, 4 (Direct) and 8 (Span) (run explicitly)"]
fn test_tree_64_leaves_all_arities() {
  let task = TreeTask::<F>::generate(101, 64, 2);
  let (leaf, ids) = leaf_family();
  let r = task.expected_result(eval(&leaf));
  let mut hashes = Vec::new();
  for (a, direct) in [(2usize, true), (4, true), (8, false)] {
    let st = if direct {
      tree64::<Direct>(a, 101)
    } else {
      tree64::<Span>(a, 101)
    };
    assert_eq!(st.result, r, "a = {a}");
    assert_eq!((st.lo, st.hi, st.num_leaves, st.arity), (0, 64, 64, a));
    hashes.push(st.tree_hash);
  }
  assert_ne!(hashes[0], hashes[1]);
  assert_ne!(hashes[1], hashes[2]);
  match TreeParams::<E1, E2, Direct>::setup(&leaf, &ids, 8, PrimaryTemplate::R1cs) {
    Ok(_) => panic!("a = 8 Direct is expected to exceed MAX_SETUP_CONSTRAINTS"),
    Err(e) => assert_eq!(e.layer(), TreeLayer::Setup),
  }
}

/// Only a = 2 at 64 leaves (the mandatory configuration).
#[test]
#[ignore = "long: 64-leaf a = 2 tree (run explicitly)"]
fn test_tree_64_leaves_a2() {
  let task = TreeTask::<F>::generate(101, 64, 2);
  let (leaf, _) = leaf_family();
  let st = tree64::<Direct>(2, 101);
  assert_eq!(st.result, task.expected_result(eval(&leaf)));
}
