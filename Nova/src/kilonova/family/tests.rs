//! P4 tests: canonical encoding (= kn-ccs), family digest and its rejections, the two
//! index-span paths for K = 1, 2, 4, 16, non-one-hot inputs, tampered spans and the zero-term
//! template embedding. Each rejection names its detection layer (`hfs::Layer`).
use super::*;
use crate::{
  kilonova::hfs::{
    decide, Direct, HfsParams, IncomingInstance, Layer, RunningInstance, RunningWitness, Span,
    Variant, NIFS,
  },
  provider::PallasEngine,
  traits::Engine,
};
use ff::Field;
use kn_ccs::{
  accs::check_accs,
  mle::eval_matrix_mle,
  pad::embed_zero_terms,
  r#gen::{random_satisfiable, wiring_pair, PairTemplate},
  AccsInstance, Assignment, Ccs, Family, SparseMatrix, Template,
};
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};

type E = PallasEngine;
type F = <E as Engine>::Scalar;

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

const REPS: usize = 4;

/// A family of K members with identical dimensions (m = 2·REPS, num_w = 2·REPS − 1, io = 2):
/// members 0 and 1 are the kn-ccs `wiring_pair` (different wiring, negative coefficients),
/// the others random satisfiable R1CS with their own supports. Returns the kn-ccs family and a
/// generator of satisfying assignments per member.
struct Fixture {
  fam: Family<F>,
  fixed: Vec<Option<Assignment<F>>>,
}

impl Fixture {
  fn new(k: usize) -> Self {
    let (m, num_w, num_io) = (2 * REPS, 2 * REPS - 1, 2);
    let mut members = Vec::new();
    let mut fixed = Vec::new();
    for i in 0..k {
      if i < 2 {
        members.push(
          wiring_pair::<F>(PairTemplate::R1cs, i, REPS, None)
            .unwrap()
            .0,
        );
        fixed.push(None);
      } else {
        let mut rng = ChaCha20Rng::seed_from_u64(1000 + i as u64);
        let (c, a) = random_satisfiable(&Template::r1cs(), m, num_w, num_io, 2, &mut rng).unwrap();
        members.push(c);
        fixed.push(Some(a));
      }
    }
    Self {
      fam: Family::new(members).unwrap(),
      fixed,
    }
  }

  fn family(&self, label: &str) -> PredicateFamily<F> {
    let k = self.fam.k();
    PredicateFamily::new(
      label,
      (0..k).map(|i| format!("m{i}")).collect(),
      1,
      b"test-selector".to_vec(),
      hfs_template(&self.fam.member(0).template),
      (0..k).map(|i| hfs_shape(self.fam.member(i))).collect(),
    )
    .unwrap()
  }

  /// A satisfied incoming instance of member `k`.
  fn input(
    &self,
    pp: &HfsParams<E>,
    k: usize,
    rng: &mut ChaCha20Rng,
  ) -> (IncomingInstance<E>, Vec<F>) {
    let a = match &self.fixed[k] {
      Some(a) => a.clone(),
      None => wiring_pair(PairTemplate::R1cs, k, REPS, Some(F::random(&mut *rng)))
        .unwrap()
        .1
        .unwrap(),
    };
    assert!(self.fam.member(k).is_satisfied(&a.z()).is_ok());
    (
      IncomingInstance::new(pp, k, &a.w, a.io.clone()).unwrap(),
      a.w,
    )
  }
}

fn oracle<V: Variant<E>>(
  pp: &HfsParams<E>,
  fam: &Family<F>,
  u: &RunningInstance<E, V>,
  w: &RunningWitness<E>,
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
}

fn schedule(k: usize, t: usize, seed: u64) -> Vec<usize> {
  let mut rng = ChaCha20Rng::seed_from_u64(seed);
  (0..t)
    .map(|i| {
      if i < k {
        i
      } else {
        (rng.next_u32() as usize) % k
      }
    })
    .collect()
}

type Run<V> = (RunningInstance<E, V>, RunningWitness<E>);

/// One honest fold (μ ≤ 1, ν = 1), checked by the verifier; returns the output and the weight
/// of the incoming member (1 for the first fold, ρ afterwards).
fn fold<V: Variant<E>>(
  pp: &HfsParams<E>,
  acc: &Option<Run<V>>,
  inc: &(IncomingInstance<E>, Vec<F>),
) -> (Run<V>, F) {
  let (ru, rw): (Vec<_>, Vec<_>) = acc.iter().cloned().unzip();
  let out = NIFS::<E, V>::prove(
    pp,
    &ru,
    &rw,
    std::slice::from_ref(&inc.0),
    std::slice::from_ref(&inc.1),
  )
  .unwrap();
  let (u, ch) = NIFS::<E, V>::verify(pp, &ru, std::slice::from_ref(&inc.0), &out.proof).unwrap();
  assert_eq!(u, out.instance);
  let w = if acc.is_some() { ch.rho } else { F::ONE };
  ((u, out.witness), w)
}

// ---------------------------------------------------------------------------------------------
// Canonical encoding and digest
// ---------------------------------------------------------------------------------------------

/// The canonical member encoding is byte-identical to `kn_ccs::encode::encode`, decodes back,
/// and does not depend on entry order or split duplicates.
#[test]
fn test_encoding_matches_kn_ccs() {
  let mut members: Vec<Ccs<F>> = Vec::new();
  for tpl in [PairTemplate::R1cs, PairTemplate::Power5] {
    for k in 0..2 {
      members.push(wiring_pair::<F>(tpl, k, 3, None).unwrap().0);
    }
  }
  let mut rng = ChaCha20Rng::seed_from_u64(7);
  members.push(
    random_satisfiable(&Template::<F>::r1cs(), 9, 5, 2, 3, &mut rng)
      .unwrap()
      .0,
  );
  for c in &members {
    let tpl = hfs_template(&c.template);
    let sh = hfs_shape(c);
    let ours = encode_member(&tpl, &sh);
    assert_eq!(ours, kn_ccs::encode::encode(c), "byte-identical to kn-ccs");
    assert_eq!(&kn_ccs::encode::decode::<F>(&ours).unwrap(), c);
    // reversed order and a split duplicate encode identically
    let messy: Vec<Vec<(usize, usize, F)>> = sh
      .matrices()
      .iter()
      .map(|m| {
        let mut v: Vec<_> = m.iter().rev().cloned().collect();
        if let Some(&(r, c, x)) = m.first() {
          v.retain(|e| (e.0, e.1) != (r, c));
          v.push((r, c, x - F::ONE));
          v.push((r, c, F::ONE));
          v.push((r, c, F::ZERO));
        }
        v
      })
      .collect();
    let messy = CcsShape::new(sh.m(), sh.num_w(), sh.num_io(), messy).unwrap();
    assert_eq!(encode_member(&tpl, &messy), ours);
    assert_eq!(member_digest(&tpl, &messy), member_digest(&tpl, &sh));
  }
}

fn expect_input<T>(r: Result<T, HfsError>, what: &str) {
  match r {
    Ok(_) => panic!("{what}: accepted"),
    Err(e) => assert_eq!(e.layer(), Layer::Input, "{what}: wrong layer ({e})"),
  }
}

/// Reordering, substituting a matrix entry, renaming an id, changing the selector or the label
/// all change the digest; the pinned-digest and per-member checks reject at layer Input.
#[test]
fn test_family_digest_binds_order_and_matrices() {
  let fx = Fixture::new(4);
  let fam = fx.family("p4-test");
  let d = fam.digest();
  assert_eq!(fx.family("p4-test").digest(), d, "deterministic");
  fam.meta().check_digest(d).unwrap();
  for k in 0..4 {
    fam
      .meta()
      .check_member(k, fam.template(), &fam.shapes()[k])
      .unwrap();
  }

  let rebuild = |ids: Vec<String>, shapes: Vec<CcsShape<F>>, sel: &[u8], label: &str| {
    PredicateFamily::new(label, ids, 1, sel.to_vec(), fam.template().clone(), shapes).unwrap()
  };
  let ids = fam.meta().ids().to_vec();
  let shapes = fam.shapes().to_vec();

  // reordered members (ids move with their matrices)
  let mut ids_r = ids.clone();
  let mut shapes_r = shapes.clone();
  ids_r.swap(0, 1);
  shapes_r.swap(0, 1);
  let reordered = rebuild(ids_r, shapes_r.clone(), b"test-selector", "p4-test");
  assert_ne!(reordered.digest(), d);
  expect_input(reordered.meta().check_digest(d), "reordered family");
  expect_input(
    fam.meta().check_member(0, fam.template(), &shapes_r[0]),
    "member 0 replaced by member 1",
  );
  // matrices reordered under the same ids
  let swapped_mats = rebuild(ids.clone(), shapes_r, b"test-selector", "p4-test");
  assert_ne!(swapped_mats.digest(), d);
  // ids reordered over the same matrices
  let mut ids_only = ids.clone();
  ids_only.swap(2, 3);
  assert_ne!(
    rebuild(ids_only, shapes.clone(), b"test-selector", "p4-test").digest(),
    d
  );

  // substituted matrix entry (one coefficient)
  let mut sub = shapes.clone();
  let mut mats = sub[2].matrices().to_vec();
  mats[1][0].2 += F::ONE;
  sub[2] = CcsShape::new(sub[2].m(), sub[2].num_w(), sub[2].num_io(), mats).unwrap();
  let substituted = rebuild(ids.clone(), sub.clone(), b"test-selector", "p4-test");
  assert_ne!(substituted.digest(), d);
  expect_input(substituted.meta().check_digest(d), "substituted matrix");
  expect_input(
    fam.meta().check_member(2, fam.template(), &sub[2]),
    "substituted matrix (member check)",
  );
  // selector and label
  assert_ne!(
    rebuild(ids.clone(), shapes.clone(), b"other", "p4-test").digest(),
    d
  );
  assert_ne!(
    rebuild(ids, shapes, b"test-selector", "p4-other").digest(),
    d
  );
}

/// Malformed families and unknown ids are rejected at layer Input.
#[test]
fn test_family_rejects_unknown_or_duplicate_ids() {
  let fx = Fixture::new(3);
  let fam = fx.family("p4-test");
  let tpl = fam.template().clone();
  let shapes = fam.shapes().to_vec();
  let ids = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
  expect_input(
    PredicateFamily::new(
      "f",
      ids(&["a", "b", "a"]),
      1,
      vec![],
      tpl.clone(),
      shapes.clone(),
    ),
    "duplicate id",
  );
  expect_input(
    PredicateFamily::new(
      "f",
      ids(&["a", "", "c"]),
      1,
      vec![],
      tpl.clone(),
      shapes.clone(),
    ),
    "empty id",
  );
  expect_input(
    PredicateFamily::new(
      "f",
      ids(&["a", "b"]),
      1,
      vec![],
      tpl.clone(),
      shapes.clone(),
    ),
    "id count",
  );
  expect_input(
    PredicateFamily::new("f", vec![], 1, vec![], tpl.clone(), vec![]),
    "empty family",
  );
  // a member with other dimensions
  let mut other = shapes.clone();
  other[1] = CcsShape::new(
    shapes[1].m() + 1,
    shapes[1].num_w(),
    2,
    shapes[1].matrices().to_vec(),
  )
  .unwrap();
  expect_input(
    PredicateFamily::new("f", ids(&["a", "b", "c"]), 1, vec![], tpl.clone(), other),
    "different dimensions",
  );
  // a member with another template (t = 2)
  let mut t2 = shapes.clone();
  t2[0] = CcsShape::new(
    shapes[0].m(),
    shapes[0].num_w(),
    2,
    shapes[0].matrices()[..2].to_vec(),
  )
  .unwrap();
  expect_input(
    PredicateFamily::new("f", ids(&["a", "b", "c"]), 1, vec![], tpl.clone(), t2),
    "different template",
  );
  // forged ids
  assert_eq!(fam.meta().position("m1"), Some(1));
  assert_eq!(fam.meta().position("m9"), None);
  expect_input(
    fam.meta().check_member(7, &tpl, &shapes[0]),
    "member id out of range",
  );
}

/// A fold made under a reordered or substituted family is rejected by the original family's
/// full check path (bare verifier, then decider).
#[test]
fn test_hfs_rejects_other_family() {
  fn run<V: Variant<E>>() {
    let fx = Fixture::new(4);
    let fam = fx.family("p4-test");
    let pp = HfsParams::<E>::from_family(&fam).unwrap();
    assert_eq!(
      pp.digest(),
      fam.digest(),
      "the HFS digest is the family digest"
    );
    let mut rng = ChaCha20Rng::seed_from_u64(11);

    let mut ids = fam.meta().ids().to_vec();
    let mut shapes = fam.shapes().to_vec();
    ids.swap(2, 3);
    shapes.swap(2, 3);
    let reordered = PredicateFamily::new(
      "p4-test",
      ids,
      1,
      b"test-selector".to_vec(),
      fam.template().clone(),
      shapes,
    )
    .unwrap();
    let mut shapes = fam.shapes().to_vec();
    let mut mats = shapes[2].matrices().to_vec();
    mats[0][0].2 += F::ONE;
    shapes[2] = CcsShape::new(shapes[2].m(), shapes[2].num_w(), 2, mats).unwrap();
    let substituted = PredicateFamily::new(
      "p4-test",
      fam.meta().ids().to_vec(),
      1,
      b"test-selector".to_vec(),
      fam.template().clone(),
      shapes,
    )
    .unwrap();

    for (what, other) in [("reordered", reordered), ("substituted", substituted)] {
      let pp_other = HfsParams::<E>::from_family(&other).unwrap();
      // a running instance of the original family, then member 2 folded under `other`
      let (run, _) = fold::<V>(&pp, &None, &fx.input(&pp, 0, &mut rng));
      let inc = fx.input(&pp, 2, &mut rng);
      let out = NIFS::<E, V>::prove(
        &pp_other,
        std::slice::from_ref(&run.0),
        std::slice::from_ref(&run.1),
        std::slice::from_ref(&inc.0),
        std::slice::from_ref(&inc.1),
      )
      .unwrap();
      let layer = match NIFS::<E, V>::verify(
        &pp,
        std::slice::from_ref(&run.0),
        std::slice::from_ref(&inc.0),
        &out.proof,
      ) {
        Err(e) => e.layer(),
        Ok((u, _)) => decide(&pp, &u, &out.witness)
          .expect_err("decider must reject")
          .layer(),
      };
      assert!(
        matches!(layer, Layer::Verifier | Layer::Decider),
        "{what} family ({}): {layer:?}",
        V::NAME
      );
    }
  }
  run::<Direct>();
  run::<Span>();
}

// ---------------------------------------------------------------------------------------------
// Index-span paths, K = 1, 2, 4, 16
// ---------------------------------------------------------------------------------------------

/// Folds a seeded schedule of T steps (every member first). After every step:
/// step-by-step explicit matrices = explicit from λ = weighted evaluation = the protocol's v_j
/// = kn-ccs `eval_matrix_mle` on the explicit matrix; the tracked λ is the witness λ; the
/// decider and the kn-ccs oracle `check_accs` accept. The folded support never exceeds the union
/// of supports and reaches it once every member has been folded.
fn span_paths<V: Variant<E>>(k: usize, t_steps: usize) -> Vec<usize> {
  let fx = Fixture::new(k);
  let fam = fx.family(&format!("p4-span-k{k}"));
  let stats = support_stats(fam.shapes());
  let pp = HfsParams::<E>::from_family(&fam).unwrap();
  let t = pp.t();
  let mut rng = ChaCha20Rng::seed_from_u64(77 + k as u64);
  let mut acc: Option<Run<V>> = None;
  let mut explicit = FoldedMatrices::<F>::zero(t, k);
  let mut growth = Vec::new();
  for (step, &id) in schedule(k, t_steps, 900 + k as u64).iter().enumerate() {
    let inc = fx.input(&pp, id, &mut rng);
    let (next, w) = fold::<V>(&pp, &acc, &inc);
    explicit.fold(fam.shapes(), w, id);
    let (u, wit) = &next;
    assert_eq!(explicit.lambda(), wit.lambda.as_slice(), "step {step}: λ");
    let from_lambda = FoldedMatrices::from_lambda(fam.shapes(), &wit.lambda);
    assert_eq!(from_lambda, explicit, "step {step}: step-by-step = from λ");
    let ex = explicit.eval(&u.r_x, &u.r_y);
    let wt = weighted_eval(fam.shapes(), &wit.lambda, &u.r_x, &u.r_y);
    assert_eq!(ex, wt, "step {step}: explicit = weighted");
    assert_eq!(ex[..], u.v[..t], "step {step}: = protocol claims");
    for (j, v) in ex.iter().enumerate() {
      let sm = SparseMatrix::from_triplets(pp.m(), pp.n(), explicit.matrix(j).to_vec()).unwrap();
      assert_eq!(
        eval_matrix_mle(&sm, &u.r_x, &u.r_y).unwrap(),
        *v,
        "kn-ccs MLE"
      );
    }
    decide(&pp, u, wit).unwrap();
    oracle(&pp, &fx.fam, u, wit);
    assert!(explicit.nnz() <= stats.union_nnz);
    growth.push(explicit.nnz());
    acc = Some(next);
  }
  // λ is dense, not one-hot, and the explicit support is the union of supports
  let (_, wit) = acc.unwrap();
  assert!(wit.lambda.iter().all(|l| !bool::from(l.is_zero())));
  if k > 1 {
    assert!(wit.lambda.iter().all(|l| *l != F::ONE));
  }
  assert_eq!(
    explicit.nnz(),
    stats.union_nnz,
    "support = union of supports"
  );
  println!(
    "[p4 span] {} K={k} T={t_steps}: member nnz max {} sum {}, union {} ({:.2}x max), explicit nnz per step {growth:?}; bytes base {} / explicit {} / lambda {}",
    V::NAME,
    stats.max_nnz,
    stats.sum_nnz,
    stats.union_nnz,
    stats.union_over_max,
    stats.base_bytes,
    stats.folded_bytes,
    stats.lambda_bytes
  );
  growth
}

#[test]
fn test_span_paths_agree_k1() {
  span_paths::<Direct>(1, 8);
  span_paths::<Span>(1, 8);
}

#[test]
fn test_span_paths_agree_k2() {
  span_paths::<Direct>(2, 16);
  span_paths::<Span>(2, 16);
}

#[test]
fn test_span_paths_agree_k4() {
  span_paths::<Direct>(4, 16);
  span_paths::<Span>(4, 16);
}

#[test]
fn test_span_paths_agree_k16() {
  let g = span_paths::<Direct>(16, 32);
  span_paths::<Span>(16, 32);
  // the support grows monotonically while new members arrive
  assert!(g[..16].windows(2).all(|w| w[0] <= w[1]));
}

// ---------------------------------------------------------------------------------------------
// Non-one-hot inputs and tampered spans
// ---------------------------------------------------------------------------------------------

/// The incoming index is e_k by construction (only k is transmitted). An id outside the family is
/// rejected at layer Input; a prover that folds a non-unit vector (here e_0 + e_1 for an input of
/// member 0) produces a witness λ that the folded index does not open to (layer Decider).
#[test]
fn test_non_one_hot_incoming_rejected() {
  fn run<V: Variant<E>>() -> HfsError {
    let fx = Fixture::new(4);
    let fam = fx.family("p4-test");
    let pp = HfsParams::<E>::from_family(&fam).unwrap();
    let mut rng = ChaCha20Rng::seed_from_u64(5);
    let (run, _) = fold::<V>(&pp, &None, &fx.input(&pp, 1, &mut rng));
    // out-of-range id
    let (mut bad, w) = fx.input(&pp, 0, &mut rng);
    bad.k = 4;
    let e = NIFS::<E, V>::prove(
      &pp,
      std::slice::from_ref(&run.0),
      std::slice::from_ref(&run.1),
      std::slice::from_ref(&bad),
      std::slice::from_ref(&w),
    )
    .unwrap_err();
    assert_eq!(e.layer(), Layer::Input);
    // non-unit incoming vector
    let inc = fx.input(&pp, 0, &mut rng);
    let ((u, mut wit), rho) = fold::<V>(&pp, &Some(run), &inc);
    wit.lambda[1] += rho; // λ* = λ + ρ (e_0 + e_1)
    let e = decide(&pp, &u, &wit).unwrap_err();
    assert_eq!(e.layer(), Layer::Decider);
    e
  }
  assert!(matches!(run::<Direct>(), HfsError::IndexCommitment { .. }));
  assert!(matches!(run::<Span>(), HfsError::SpanIndex));
}

/// A tampered running span: (Span) public λ changed → SpanIndex; public and witness λ changed
/// consistently → Claim (the evaluation claims no longer match); folding the tampered pair once
/// more is rejected by the bare verifier (the claims enter the next sum-check). (Direct) witness
/// λ changed → IndexCommitment.
#[test]
fn test_tampered_span_rejected() {
  let fx = Fixture::new(4);
  let fam = fx.family("p4-test");
  let pp = HfsParams::<E>::from_family(&fam).unwrap();
  let mut rng = ChaCha20Rng::seed_from_u64(9);
  let mut acc: Option<Run<Span>> = None;
  for id in [0, 1, 2, 3] {
    acc = Some(fold::<Span>(&pp, &acc, &fx.input(&pp, id, &mut rng)).0);
  }
  let (u, w) = acc.unwrap();
  let mut u1 = u.clone();
  u1.index[2] += F::ONE;
  assert_eq!(decide(&pp, &u1, &w), Err(HfsError::SpanIndex));
  let mut w1 = w.clone();
  w1.lambda[2] += F::ONE;
  let e = decide(&pp, &u1, &w1).unwrap_err();
  assert!(matches!(e, HfsError::Claim { .. }), "{e}");
  // fold the tampered (consistent) pair once more: the running claims v are the X-phase claim
  // of the next sum-check, so the bare verifier rejects (layer Verifier)
  let inc = fx.input(&pp, 3, &mut rng);
  let out = NIFS::<E, Span>::prove(
    &pp,
    std::slice::from_ref(&u1),
    std::slice::from_ref(&w1),
    std::slice::from_ref(&inc.0),
    std::slice::from_ref(&inc.1),
  )
  .unwrap();
  let e = NIFS::<E, Span>::verify(
    &pp,
    std::slice::from_ref(&u1),
    std::slice::from_ref(&inc.0),
    &out.proof,
  )
  .unwrap_err();
  assert_eq!(e.layer(), Layer::Verifier, "{e}");

  let mut acc: Option<Run<Direct>> = None;
  for id in [0, 1, 2] {
    acc = Some(fold::<Direct>(&pp, &acc, &fx.input(&pp, id, &mut rng)).0);
  }
  let (u, mut w) = acc.unwrap();
  w.lambda[0] += F::ONE;
  assert!(matches!(
    decide(&pp, &u, &w),
    Err(HfsError::IndexCommitment { .. })
  ));
}

// ---------------------------------------------------------------------------------------------
// Template embedding (zero terms)
// ---------------------------------------------------------------------------------------------

/// R1CS + native power-5 template `[A,B]·1, [C]·(−1), [D;5]·1, [E]·(−1)` (P5's R1csPow5).
fn pow5_template() -> Template<F> {
  Template {
    t: 5,
    multisets: vec![vec![0, 1], vec![2], vec![3; 5], vec![4]],
    coeffs: vec![F::ONE, -F::ONE, F::ONE, -F::ONE],
  }
}

/// A mixed family {R1CS member embedded with zero terms, native degree-5 member} folds for 12
/// steps with u ≠ 1 (relaxed) and every output passes the decider and the kn-ccs oracle. The
/// embedded member is relation-equivalent to the R1CS one on every z (satisfied and tampered).
/// `lift_degree` is not used: it is exact only for u = 1 (P2).
#[test]
fn test_zero_term_embedding_folds() {
  let r1cs = wiring_pair::<F>(PairTemplate::R1cs, 0, REPS, None)
    .unwrap()
    .0;
  let embedded =
    embed_zero_terms(&r1cs, 2, vec![(F::ONE, vec![3; 5]), (-F::ONE, vec![4])]).unwrap();
  assert_eq!(embedded.template, pow5_template());
  assert_eq!(embedded.nnz(), r1cs.nnz(), "embedding adds no non-zeros");
  let mut rng = ChaCha20Rng::seed_from_u64(31);
  let (native, native_a) = random_satisfiable(
    &pow5_template(),
    r1cs.m,
    r1cs.num_w,
    r1cs.num_io,
    2,
    &mut rng,
  )
  .unwrap();
  assert!(
    native.matrices[3].nnz() > 0,
    "member 1 has native degree-5 rows"
  );
  // semantics preserved on satisfied and on tampered assignments, for u = 1 and u ≠ 1
  for _ in 0..10 {
    let a = wiring_pair(PairTemplate::R1cs, 0, REPS, Some(F::random(&mut rng)))
      .unwrap()
      .1
      .unwrap();
    for u in [F::ONE, F::from(3)] {
      let mut z = r1cs.z(&a.w, u, &a.io).unwrap();
      assert_eq!(r1cs.residual(&z), embedded.residual(&z));
      z[0] += F::ONE;
      assert_eq!(r1cs.residual(&z), embedded.residual(&z));
    }
  }
  let kfam = Family::new(vec![embedded.clone(), native.clone()]).unwrap();
  let fam = PredicateFamily::new(
    "p4-embed",
    vec!["r1cs-embedded".into(), "native-pow5".into()],
    1,
    vec![],
    hfs_template(&pow5_template()),
    vec![hfs_shape(&embedded), hfs_shape(&native)],
  )
  .unwrap();
  let pp = HfsParams::<E>::from_family(&fam).unwrap();
  let mut acc: Option<Run<Direct>> = None;
  for step in 0..12 {
    let k = step % 2;
    let (w, io) = if k == 0 {
      let a = wiring_pair(PairTemplate::R1cs, 0, REPS, Some(F::random(&mut rng)))
        .unwrap()
        .1
        .unwrap();
      (a.w, a.io)
    } else {
      (native_a.w.clone(), native_a.io.clone())
    };
    let inc = (IncomingInstance::new(&pp, k, &w, io).unwrap(), w);
    let (next, _) = fold::<Direct>(&pp, &acc, &inc);
    decide(&pp, &next.0, &next.1).unwrap();
    oracle(&pp, &kfam, &next.0, &next.1);
    if step > 0 {
      assert_ne!(next.0.u, F::ONE, "relaxed instance");
    }
    acc = Some(next);
  }
  // expansion cost of the embedding for the folding layer: proof elements and nnz
  let r1cs_pp =
    HfsParams::<E>::new(hfs_template(&Template::r1cs()), vec![hfs_shape(&r1cs)]).unwrap();
  let proof_elems = |pp: &HfsParams<E>| {
    let (s, sp, t, dx) = (pp.s(), pp.s_prime(), pp.t(), pp.template().deg_x());
    s * (dx + 1) + 2 * t + sp * 3 + 2 * (t + 1)
  };
  println!(
    "[p4 embed] R1CS t=3 d=2: proof {} elements; embedded in R1csPow5 t=5 d=5: proof {} elements, nnz unchanged ({}), running state +2 index commitments (Direct)",
    proof_elems(&r1cs_pp),
    proof_elems(&pp),
    r1cs.nnz()
  );
  assert!(proof_elems(&pp) > proof_elems(&r1cs_pp));
}
