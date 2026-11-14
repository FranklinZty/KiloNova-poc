//! P7a tests: compression and `verify-final` for chains and trees, Direct and Span; the
//! rejection suite with detection layers; byte-level tampering; the proof-size account; the
//! verifier's inputs; the masked z opening.
//!
//! Memory: run with `--release --test-threads=1`. The four fixtures (chain/tree × Direct/Span)
//! are built once per process; each keeps only the verifier key, the proof bytes, the public
//! input and (for the terminal-layer tests) the folded instance `U*` and its witness.
use super::{
  check_cyclefold, check_index, check_matrix_eval, check_witness_opening, compress_chain,
  compress_tree, eq_table,
  format::{self, account, decode, encode, encode_head, Dims, NUM_SECTIONS, SECTIONS},
  reference_basis_eval, verify_final_chain, verify_final_tree,
  verify_final_tree_statement, CompressError, CompressLayer,
  CompressorKey, FinalStatement, FinalVariant, FinalVerifierKey, ProofKind, E1, E2, F1,
};
use crate::{
  kilonova::{
    family::{encode_member, weighted_eval},
    hfs::{decide, Direct, RunningInstance, RunningWitness, Span, NIFS},
    ivc::{fixtures::ChainPredicates, ChainOutput, PrimaryTemplate, PublicParams, RecursiveSNARK},
    pcd::{prove_tree, RootStatement, TreeParams, TreeTask},
  },
  provider::ipa_pc::{InnerProductArgument, InnerProductInstance, InnerProductWitness},
  traits::{commitment::CommitmentEngineTrait, Engine},
};
use ff::Field;
use std::{
  fs,
  io::BufReader,
  path::PathBuf,
  sync::OnceLock,
};

fn tmp_dir(name: &str) -> PathBuf {
  let d = std::env::temp_dir().join(format!("kn-p7-{}-{name}", std::process::id()));
  fs::create_dir_all(&d).unwrap();
  d
}

/// Public input of the fixture's statement.
enum Public {
  Chain {
    n: usize,
    z0: Vec<F1>,
    out: ChainOutput<F1>,
  },
  Tree {
    expected: RootStatement<F1>,
  },
}

struct Fx<V: FinalVariant> {
  vk: FinalVerifierKey<V>,
  material: PathBuf,
  proof: Vec<u8>,
  public: Public,
  /// The folded instance U* = fold(U_n, u_n) and its witness (terminal-layer tests only).
  u_star: RunningInstance<E1, V>,
  w_star: RunningWitness<E1>,
  num_w: usize,
}

fn vk_from_file<V: FinalVariant>(path: &PathBuf, expected: Option<F1>) -> Result<FinalVerifierKey<V>, CompressError> {
  let f = fs::File::open(path).unwrap();
  FinalVerifierKey::<V>::read_material(&mut BufReader::new(f), expected)
}

fn chain_fixture<V: FinalVariant>(ids: &[usize]) -> Fx<V> {
  let k = 2;
  let prog = ChainPredicates::<F1>::new(k, false).program();
  let (pp, _) = PublicParams::<E1, E2, V>::setup(&prog, PrimaryTemplate::R1cs).unwrap();
  let app = [F1::from(3), F1::from(5)];
  let z0 = prog.z0(&app, ids).unwrap();
  let mut snark = RecursiveSNARK::<E1, E2, V>::new(&pp, &prog, &z0).unwrap();
  for _ in 1..ids.len() {
    snark.prove_step(&pp, &prog).unwrap();
  }
  let out = snark.verify(&pp, ids.len(), &z0).unwrap();
  let key = CompressorKey::chain(&pp).unwrap();
  let proof = encode(&compress_chain(&pp, &key, &snark).unwrap());
  let (u_star, w_star) = final_fold(pp.hfs(), &snark);
  let dir = tmp_dir(&format!("chain-{}", V::NAME));
  let material = dir.join("material.knvm");
  let mut f = fs::File::create(&material).unwrap();
  format::write_material_chain(&pp, &mut f).unwrap();
  let pinned = pp.digest();
  let num_w = pp.hfs().num_w();
  drop((pp, snark, key));
  let vk = vk_from_file::<V>(&material, Some(pinned)).unwrap();
  Fx {
    vk,
    material,
    proof,
    public: Public::Chain {
      n: ids.len(),
      z0,
      out,
    },
    u_star,
    w_star,
    num_w,
  }
}

fn final_fold<V: FinalVariant>(
  hfs: &crate::kilonova::hfs::HfsParams<E1>,
  snark: &RecursiveSNARK<E1, E2, V>,
) -> (RunningInstance<E1, V>, RunningWitness<E1>) {
  let (r_u, r_w) = snark.running();
  let (l_u, l_w) = snark.last_incoming();
  let out = NIFS::<E1, V>::prove(
    hfs,
    std::slice::from_ref(r_u),
    std::slice::from_ref(r_w),
    std::slice::from_ref(l_u),
    &[l_w.to_vec()],
  )
  .unwrap();
  (out.instance, out.witness)
}

fn tree_fixture<V: FinalVariant>(l: usize) -> Fx<V> {
  let leaf = ChainPredicates::<F1>::new(2, false);
  let ids: Vec<String> = (0..2).map(|k| leaf.member_id(k)).collect();
  let (pp, _) = TreeParams::<E1, E2, V>::setup(&leaf, &ids, 2, PrimaryTemplate::R1cs).unwrap();
  let task = TreeTask::<F1>::generate(700 + l as u64, l, 2);
  let (root, _) = prove_tree(&pp, &leaf, &task).unwrap();
  let expected = pp.root_statement(&task, |k, x| leaf.output(k, x));
  assert_eq!(root.verify_root(&pp).unwrap(), expected);
  let key = CompressorKey::tree(&pp).unwrap();
  let proof = encode(&compress_tree(&pp, &key, &root).unwrap());
  let (r_u, r_w) = root.running();
  let (l_u, l_w) = root.own_incoming();
  let out = NIFS::<E1, V>::prove(
    pp.hfs(),
    std::slice::from_ref(r_u),
    std::slice::from_ref(r_w),
    std::slice::from_ref(l_u),
    &[l_w.to_vec()],
  )
  .unwrap();
  let dir = tmp_dir(&format!("tree-{}", V::NAME));
  let material = dir.join("material.knvm");
  let mut f = fs::File::create(&material).unwrap();
  format::write_material_tree(&pp, &mut f).unwrap();
  let pinned = pp.digest();
  let num_w = pp.hfs().num_w();
  drop((pp, root, key));
  let vk = vk_from_file::<V>(&material, Some(pinned)).unwrap();
  Fx {
    vk,
    material,
    proof,
    public: Public::Tree { expected },
    u_star: out.instance,
    w_star: out.witness,
    num_w,
  }
}

const CHAIN_IDS: [usize; 3] = [0, 1, 1];
const TREE_L: usize = 3;

fn chain_direct() -> &'static Fx<Direct> {
  static FX: OnceLock<Fx<Direct>> = OnceLock::new();
  FX.get_or_init(|| chain_fixture::<Direct>(&CHAIN_IDS))
}

fn chain_span() -> &'static Fx<Span> {
  static FX: OnceLock<Fx<Span>> = OnceLock::new();
  FX.get_or_init(|| chain_fixture::<Span>(&CHAIN_IDS))
}

fn tree_direct() -> &'static Fx<Direct> {
  static FX: OnceLock<Fx<Direct>> = OnceLock::new();
  FX.get_or_init(|| tree_fixture::<Direct>(TREE_L))
}

fn tree_span() -> &'static Fx<Span> {
  static FX: OnceLock<Fx<Span>> = OnceLock::new();
  FX.get_or_init(|| tree_fixture::<Span>(TREE_L))
}

/// Verifies `bytes` as the fixture's statement.
fn verify<V: FinalVariant>(fx: &Fx<V>, bytes: &[u8]) -> Result<(), CompressError> {
  match &fx.public {
    Public::Chain { n, z0, out } => {
      let got = verify_final_chain(&fx.vk, bytes, *n, z0)?;
      assert_eq!(&got, out, "verify-final returns what the uncompressed verifier returns");
      Ok(())
    }
    Public::Tree { expected } => verify_final_tree_statement(&fx.vk, bytes, expected).map(|_| ()),
  }
}

fn expect_layer<T: std::fmt::Debug>(res: Result<T, CompressError>, layer: CompressLayer, what: &str) {
  match res {
    Ok(v) => panic!("{what}: accepted ({v:?})"),
    Err(e) => assert_eq!(e.layer(), layer, "{what}: rejected at {:?} ({e})", e.layer()),
  }
}

/// Decodes, applies `f` to the decoded proof, re-encodes canonically and verifies.
fn tampered<V: FinalVariant>(
  fx: &Fx<V>,
  f: impl FnOnce(&mut super::CompressedProof<V>),
) -> Result<(), CompressError> {
  let mut p = decode(&fx.vk, &fx.proof).unwrap();
  f(&mut p);
  verify(fx, &encode(&p))
}

// ---------------------------------------------------------------------------------------------
// Positive cases, coverage
// ---------------------------------------------------------------------------------------------

fn positive<V: FinalVariant>(fx: &Fx<V>, kind: ProofKind) {
  verify(fx, &fx.proof).unwrap();
  let p = decode(&fx.vk, &fx.proof).unwrap();
  assert_eq!(p.head.kind, kind);
  assert_eq!(encode(&p), fx.proof, "canonical round trip");
  let d = dims(&fx.vk);
  assert_eq!(fx.proof.len(), d.proof_bytes::<V>(kind), "length formula");
  // the uncompressed decider accepts U* with its witness, so the compressed checks are about
  // the same instance
  decide(fx.vk.hfs(), &fx.u_star, &fx.w_star).unwrap();
}

fn dims<V: FinalVariant>(vk: &FinalVerifierKey<V>) -> Dims {
  let h = vk.hfs();
  Dims {
    arity: vk.arity(),
    num_io: h.num_io(),
    s: h.s(),
    s_prime: h.s_prime(),
    t: h.t(),
    k: h.k(),
    deg_x: h.template().deg_x(),
    n_cf: vk.cyclefold_shape().num_io,
    n_cf_rows: vk.cyclefold_shape().num_cons,
  }
}

/// Chain, Direct, K = 2, T = 3: compress, write the material and the proof, verify from them.
#[test]
fn test_compress_chain_direct() {
  positive(chain_direct(), ProofKind::Chain);
}

/// Chain, Span, K = 2, T = 3.
#[test]
fn test_compress_chain_span() {
  positive(chain_span(), ProofKind::Chain);
}

/// Tree root, Direct, a = 2, L = 3 (two merges, one dummy subtree).
#[test]
fn test_compress_tree_direct() {
  let fx = tree_direct();
  positive(fx, ProofKind::Tree);
  let Public::Tree { expected } = &fx.public else {
    unreachable!()
  };
  assert_eq!(&verify_final_tree(&fx.vk, &fx.proof).unwrap(), expected);
}

/// Tree root, Span, a = 2, L = 3.
#[test]
fn test_compress_tree_span() {
  positive(tree_span(), ProofKind::Tree);
}

/// Chain of one step (CycleFold accumulator still the default) and a tree whose root is a single
/// leaf (L = 1, default accumulators).
#[test]
fn test_compress_base_cases() {
  let fx = chain_fixture::<Direct>(&[1]);
  verify(&fx, &fx.proof).unwrap();
  let fx = tree_fixture::<Direct>(1);
  verify(&fx, &fx.proof).unwrap();
}

// ---------------------------------------------------------------------------------------------
// Checkpoint deleted (in process; the separate-process test is in tools/kn-run/tests)
// ---------------------------------------------------------------------------------------------

/// The prover writes a private checkpoint and the public files, everything prover-side is
/// dropped and the checkpoint directory deleted, then a verifier built from the material file
/// alone verifies the proof file.
#[test]
fn test_compress_file_roundtrip_checkpoint_deleted() {
  let dir = tmp_dir("roundtrip");
  let (private, public) = (dir.join("private"), dir.join("public"));
  fs::create_dir_all(&private).unwrap();
  fs::create_dir_all(&public).unwrap();
  let prog = ChainPredicates::<F1>::new(2, false).program();
  let ids = [1usize, 0];
  let z0 = prog.z0(&[F1::from(7), F1::from(9)], &ids).unwrap();
  let pinned = {
    let (pp, _) = PublicParams::<E1, E2, Direct>::setup(&prog, PrimaryTemplate::R1cs).unwrap();
    let mut snark = RecursiveSNARK::<E1, E2, Direct>::new(&pp, &prog, &z0).unwrap();
    snark.prove_step(&pp, &prog).unwrap();
    fs::write(
      private.join("checkpoint.bin"),
      bincode::serde::encode_to_vec(&snark, bincode::config::legacy()).unwrap(),
    )
    .unwrap();
    let key = CompressorKey::chain(&pp).unwrap();
    let proof = compress_chain(&pp, &key, &snark).unwrap();
    fs::write(public.join("proof.kncp"), encode(&proof)).unwrap();
    let mut f = fs::File::create(public.join("material.knvm")).unwrap();
    format::write_material_chain(&pp, &mut f).unwrap();
    pp.digest()
  };
  fs::remove_dir_all(&private).unwrap();
  assert!(!private.exists());
  let vk = vk_from_file::<Direct>(&public.join("material.knvm"), Some(pinned)).unwrap();
  let bytes = fs::read(public.join("proof.kncp")).unwrap();
  let out = verify_final_chain(&vk, &bytes, 2, &z0).unwrap();
  assert_eq!(out.last_id, 0);
  assert_eq!(
    out.zn[..2],
    prog.inner().run(&[F1::from(7), F1::from(9)], &ids)[..]
  );
  fs::remove_dir_all(&dir).unwrap();
}

/// The verifier's inputs carry no witness: the proof consists of exactly the declared sections,
/// its field-element count is a function of (s, s', t, K, arity, num_io, n_cf) only, far below
/// num_w, and is the same for two different witnesses; the verifier key is built from the
/// material file alone (no `PublicParams`, no `RecursiveSNARK`, no `NodeProof`).
#[test]
fn test_verifier_inputs_have_no_witness() {
  fn check<V: FinalVariant>(fx: &Fx<V>) {
    let p = decode(&fx.vk, &fx.proof).unwrap();
    let acc = account(&fx.vk, &p).unwrap();
    let names: Vec<&str> = acc.by_section.iter().map(|(s, _)| s.as_str()).collect();
    let mut expected = vec!["header", "framing"];
    expected.extend(SECTIONS);
    assert_eq!(names, expected);
    let elements: usize = acc.items.iter().map(|i| i.elements).sum();
    assert!(
      32 * elements < fx.num_w,
      "{elements} elements against num_w = {}",
      fx.num_w
    );
    for i in &acc.items {
      for w in ["witness", "W*", "cf_w", "l_w", "E vector"] {
        assert!(!i.item.contains(w), "item {} looks like a witness", i.item);
      }
    }
    // a verifier key built again from the material file alone verifies the proof
    let vk = vk_from_file::<V>(&fx.material, None).unwrap();
    assert_eq!(vk.pp_digest(), fx.vk.pp_digest());
    match &fx.public {
      Public::Chain { n, z0, .. } => {
        verify_final_chain(&vk, &fx.proof, *n, z0).unwrap();
      }
      Public::Tree { .. } => {
        verify_final_tree(&vk, &fx.proof).unwrap();
      }
    }
  }
  check(chain_direct());
  check(chain_span());
  check(tree_direct());
  // two chains with different witnesses (different schedules) give proofs of the same length
  let other = chain_fixture::<Direct>(&[1, 1, 0]);
  assert_eq!(other.proof.len(), chain_direct().proof.len());
  assert_ne!(other.proof, chain_direct().proof);
}

// ---------------------------------------------------------------------------------------------
// Proof-size account
// ---------------------------------------------------------------------------------------------

/// The item-by-item account (from the message format) sums to the real file length, section by
/// section; the Spartan sub-items match [`Dims::spartan_bytes`]; the K dependence is exactly the
/// λ items (Span: running λ; Direct: revealed λ*).
#[test]
fn test_proof_account_matches_file() {
  fn check<V: FinalVariant>(fx: &Fx<V>) {
    let p = decode(&fx.vk, &fx.proof).unwrap();
    let acc = account(&fx.vk, &p).unwrap();
    assert_eq!(acc.total, fx.proof.len(), "Σ items = file length");
    let d = dims(&fx.vk);
    let sec = d.section_bytes::<V>(p.head.kind);
    for (i, name) in SECTIONS.iter().enumerate() {
      let got = acc
        .by_section
        .iter()
        .find(|(s, _)| s == name)
        .map(|(_, b)| *b)
        .unwrap();
      assert_eq!(got, sec[i], "section {name}");
    }
    let spartan: usize = p.cf_snark.field_bytes().unwrap().iter().map(|x| x.1).sum();
    assert_eq!(spartan, Dims::spartan_bytes(d.n_cf_rows));
    let k_items: usize = acc
      .items
      .iter()
      .filter(|i| i.formula.contains('K'))
      .map(|i| i.bytes)
      .sum();
    assert_eq!(k_items, 32 * d.k, "K-dependent bytes");
    println!(
      "[P7 account] {} {:?}: {} bytes, sections {:?}",
      <V as crate::kilonova::hfs::Variant<E1>>::NAME,
      p.head.kind,
      acc.total,
      acc.by_section
    );
  }
  check(chain_direct());
  check(chain_span());
  check(tree_direct());
  check(tree_span());
}

// ---------------------------------------------------------------------------------------------
// Reference basis
// ---------------------------------------------------------------------------------------------

/// The reference-basis evaluation (every base matrix, eq tables written in the compress module)
/// agrees with the P4 weighted path and with the claims of U*.
#[test]
fn test_reference_basis_eval_matches_weighted_path() {
  let fx = chain_direct();
  let u = &fx.u_star;
  let evals = reference_basis_eval(fx.vk.hfs(), &u.r_x, &u.r_y);
  assert_eq!(evals.len(), fx.vk.hfs().k());
  let lambda = &fx.w_star.lambda;
  let w = weighted_eval(fx.vk.hfs().shapes(), lambda, &u.r_x, &u.r_y);
  for j in 0..fx.vk.hfs().t() {
    let v = evals.iter().zip(lambda).fold(F1::ZERO, |a, (e, l)| a + *l * e[j]);
    assert_eq!(v, w[j]);
    assert_eq!(v, u.v[j]);
  }
  // eq table convention: bit i of the index ↔ r_y[i]
  let t = eq_table(&u.r_y);
  let idx = 5usize;
  let direct = u.r_y.iter().enumerate().fold(F1::ONE, |a, (i, r)| {
    a * if (idx >> i) & 1 == 1 { *r } else { F1::ONE - r }
  });
  assert_eq!(t[idx], direct);
}

// ---------------------------------------------------------------------------------------------
// Rejections, with the detection layer
// ---------------------------------------------------------------------------------------------

/// Family: digests in the proof, a substituted member in the material (pinned digest: Material;
/// unpinned: the proof no longer binds, Binding), a verifier for the other variant (Material) or
/// kind (Format).
#[test]
fn test_compress_rejects_family() {
  let fx = chain_direct();
  expect_layer(
    tampered(fx, |p| p.head.pp_digest += F1::ONE),
    CompressLayer::Binding,
    "pp digest",
  );
  expect_layer(
    tampered(fx, |p| p.head.family_digest += F1::ONE),
    CompressLayer::Binding,
    "family digest",
  );
  // substitute one matrix entry of member 1 in the material file
  let (header, members) =
    format::read_material(&mut BufReader::new(fs::File::open(&fx.material).unwrap())).unwrap();
  let mut members = members;
  let (tpl, sh) = members[1].clone();
  let mut mats = sh.matrices().to_vec();
  mats[0][0].2 += F1::ONE;
  let sh2 = crate::kilonova::hfs::CcsShape::new(sh.m(), sh.num_w(), sh.num_io(), mats).unwrap();
  members[1] = (tpl.clone(), sh2);
  assert_ne!(encode_member(&tpl, &members[1].1), encode_member(&tpl, &sh));
  expect_layer(
    FinalVerifierKey::<Direct>::from_parts(header.clone(), members.clone(), Some(fx.vk.pp_digest()))
      .map(|_| ()),
    CompressLayer::Material,
    "substituted member, pinned digest",
  );
  let vk2 = FinalVerifierKey::<Direct>::from_parts(header, members, None).unwrap();
  let Public::Chain { n, z0, .. } = &fx.public else {
    unreachable!()
  };
  expect_layer(
    verify_final_chain(&vk2, &fx.proof, *n, z0),
    CompressLayer::Binding,
    "verifier of a substituted family",
  );
  expect_layer(
    vk_from_file::<Span>(&fx.material, None).map(|_| ()),
    CompressLayer::Material,
    "Span verifier on Direct material",
  );
  // a chain proof checked with the tree verifier
  expect_layer(
    verify_final_tree(&tree_direct().vk, &fx.proof),
    CompressLayer::Format,
    "chain proof, tree verifier",
  );
}

/// Final output, step count / task size, statement: chain z_n, trace, n, z_0; tree R, h, L, a,
/// range, task id.
#[test]
fn test_compress_rejects_statement_and_output() {
  let fx = chain_direct();
  let Public::Chain { n, z0, .. } = &fx.public else {
    unreachable!()
  };
  let chain = |f: fn(&mut FinalStatement)| {
    tampered(fx, |p| f(&mut p.head.statement))
  };
  expect_layer(
    chain(|s| {
      if let FinalStatement::Chain { zn, .. } = s {
        zn[0] += F1::ONE
      }
    }),
    CompressLayer::LinkHash,
    "final output z_n",
  );
  expect_layer(
    chain(|s| {
      if let FinalStatement::Chain { trace, .. } = s {
        *trace += F1::ONE
      }
    }),
    CompressLayer::LinkHash,
    "trace",
  );
  expect_layer(
    chain(|s| {
      if let FinalStatement::Chain { n, .. } = s {
        *n += 1
      }
    }),
    CompressLayer::Statement,
    "step count in the file",
  );
  expect_layer(
    verify_final_chain(&fx.vk, &fx.proof, n + 1, z0),
    CompressLayer::Statement,
    "verifier expects another step count",
  );
  let mut z0b = z0.clone();
  z0b[1] += F1::ONE;
  expect_layer(
    verify_final_chain(&fx.vk, &fx.proof, *n, &z0b),
    CompressLayer::Statement,
    "verifier expects another z_0",
  );
  // the file claims n + 1 steps and the verifier is asked for n + 1: the link hash binds n
  let mut p = decode(&fx.vk, &fx.proof).unwrap();
  if let FinalStatement::Chain { n: pn, .. } = &mut p.head.statement {
    *pn += 1;
  }
  expect_layer(
    verify_final_chain(&fx.vk, &encode(&p), n + 1, z0),
    CompressLayer::LinkHash,
    "step count, consistent claim",
  );

  let fx = tree_direct();
  let tree = |f: fn(&mut FinalStatement)| tampered(fx, |p| f(&mut p.head.statement));
  expect_layer(
    tree(|s| {
      if let FinalStatement::Tree { stmt, .. } = s {
        stmt.result[0] += F1::ONE
      }
    }),
    CompressLayer::LinkHash,
    "final output R",
  );
  expect_layer(
    tree(|s| {
      if let FinalStatement::Tree { stmt, .. } = s {
        stmt.tree_hash += F1::ONE
      }
    }),
    CompressLayer::LinkHash,
    "tree hash",
  );
  expect_layer(
    tree(|s| {
      if let FinalStatement::Tree { ctx, .. } = s {
        ctx.num_leaves += 1 // L = 3 -> 4: same capacity, link hash breaks
      }
    }),
    CompressLayer::LinkHash,
    "task size L (same capacity)",
  );
  expect_layer(
    tree(|s| {
      if let FinalStatement::Tree { ctx, .. } = s {
        ctx.num_leaves = 5 // capacity 8 != 4
      }
    }),
    CompressLayer::Statement,
    "task size L (other capacity)",
  );
  expect_layer(
    tree(|s| {
      if let FinalStatement::Tree { a, .. } = s {
        *a = 4
      }
    }),
    CompressLayer::Statement,
    "arity a",
  );
  expect_layer(
    tree(|s| {
      if let FinalStatement::Tree { stmt, .. } = s {
        stmt.hi = 8
      }
    }),
    CompressLayer::Statement,
    "root range",
  );
  expect_layer(
    tree(|s| {
      if let FinalStatement::Tree { ctx, .. } = s {
        ctx.task_id += F1::ONE
      }
    }),
    CompressLayer::LinkHash,
    "task id",
  );
  let Public::Tree { expected } = &fx.public else {
    unreachable!()
  };
  let mut other = expected.clone();
  other.result[1] += F1::ONE;
  expect_layer(
    verify_final_tree_statement(&fx.vk, &fx.proof, &other),
    CompressLayer::Statement,
    "expected statement differs",
  );
}

/// Recursive output binding: the last incoming instance's io (the link hash output), its
/// predicate id and commitment, the running instance and the CycleFold instance are all bound.
#[test]
fn test_compress_rejects_recursive_output_binding() {
  fn run<V: FinalVariant>(fx: &Fx<V>) {
    expect_layer(
      tampered(fx, |p| p.head.incoming.io[0] += F1::ONE),
      CompressLayer::LinkHash,
      "link hash output u_n.io",
    );
    expect_layer(
      tampered(fx, |p| p.head.running.u += F1::ONE),
      CompressLayer::LinkHash,
      "running u",
    );
    expect_layer(
      tampered(fx, |p| p.head.running.comm_w = p.head.running.comm_w + p.head.running.comm_w),
      CompressLayer::LinkHash,
      "running comm_W",
    );
    expect_layer(
      tampered(fx, |p| p.head.cf.X[0] += <E2 as Engine>::Scalar::ONE),
      CompressLayer::LinkHash,
      "CycleFold instance X",
    );
    expect_layer(
      tampered(fx, |p| p.head.cf.comm_E = p.head.cf.comm_W),
      CompressLayer::LinkHash,
      "CycleFold instance comm_E",
    );
    // the incoming commitment and id are not in the link hash; the final fold binds them
    expect_layer(
      tampered(fx, |p| {
        p.head.incoming.comm_w = p.head.incoming.comm_w + p.head.incoming.comm_w
      }),
      CompressLayer::FinalFold,
      "incoming comm_W",
    );
    expect_layer(
      tampered(fx, |p| p.head.incoming.k = (p.head.incoming.k + 1) % 2),
      CompressLayer::FinalFold,
      "incoming predicate id",
    );
  }
  run(chain_direct());
  run(tree_span());
}

/// Span and the index: Span λ in U_n (bound by the link hash), Direct revealed λ* (index
/// opening), and λ* of U* at the terminal checks (matrix evaluation).
#[test]
fn test_compress_rejects_span_and_index() {
  let fx = chain_span();
  expect_layer(
    tampered(fx, |p| p.head.running.index[0] += F1::ONE),
    CompressLayer::LinkHash,
    "Span running lambda",
  );
  let mut u = fx.u_star.clone();
  u.index[1] += F1::ONE;
  let lambda = check_index(&fx.vk, &u, &[]).unwrap();
  expect_layer(
    check_matrix_eval(&fx.vk, &u, &lambda),
    CompressLayer::MatrixEval,
    "Span lambda* at the terminal check",
  );

  let fx = chain_direct();
  expect_layer(
    tampered(fx, |p| p.head.lambda[0] += F1::ONE),
    CompressLayer::IndexOpening,
    "Direct revealed lambda*",
  );
  expect_layer(
    tampered(fx, |p| p.head.running.index[2] = p.head.running.index[0]),
    CompressLayer::LinkHash,
    "Direct running comm_M",
  );
  // a λ* that opens comm_M* but is not the folded index cannot exist (binding); a revealed λ*
  // for another slot layout fails slot by slot
  let mut l2 = fx.w_star.lambda.clone();
  l2.swap(0, 1);
  expect_layer(
    check_index(&fx.vk, &fx.u_star, &l2),
    CompressLayer::IndexOpening,
    "swapped lambda*",
  );
}

/// Evaluation point and value: in the file they are produced by the final fold (FinalFold); at
/// the terminal checks, a moved point or value is caught by the matrix evaluation or the
/// opening.
#[test]
fn test_compress_rejects_evaluation_point_and_value() {
  fn run<V: FinalVariant>(fx: &Fx<V>) {
    expect_layer(
      tampered(fx, |p| p.head.fold.sc_y[0][2] += F1::ONE),
      CompressLayer::FinalFold,
      "Y round message (evaluation point r_y*)",
    );
    expect_layer(
      tampered(fx, |p| p.head.fold.sc_x[1][0] += F1::ONE),
      CompressLayer::FinalFold,
      "X round message (evaluation point r_x*)",
    );
    expect_layer(
      tampered(fx, |p| p.head.fold.eps[0][0] += F1::ONE),
      CompressLayer::FinalFold,
      "matrix value eps",
    );
    expect_layer(
      tampered(fx, |p| p.head.fold.theta[0][3] += F1::ONE),
      CompressLayer::FinalFold,
      "z value theta",
    );
    expect_layer(
      tampered(fx, |p| p.head.running.r_y[0] += F1::ONE),
      CompressLayer::LinkHash,
      "running point r_y",
    );
    expect_layer(
      tampered(fx, |p| p.head.running.v[0] += F1::ONE),
      CompressLayer::LinkHash,
      "running value v",
    );
    // terminal layers on U*
    let p = decode(&fx.vk, &fx.proof).unwrap();
    let head = encode_head(&p.head);
    let lam = check_index(&fx.vk, &fx.u_star, &p.head.lambda).unwrap();
    check_matrix_eval(&fx.vk, &fx.u_star, &lam).unwrap();
    check_witness_opening(&fx.vk, &head, &fx.u_star, &p.w_open).unwrap();
    let mut u = fx.u_star.clone();
    u.r_y[3] += F1::ONE;
    expect_layer(check_matrix_eval(&fx.vk, &u, &lam), CompressLayer::MatrixEval, "moved r_y*");
    expect_layer(
      check_witness_opening(&fx.vk, &head, &u, &p.w_open),
      CompressLayer::WitnessOpening,
      "moved r_y* (opening)",
    );
    let mut u = fx.u_star.clone();
    u.r_x[0] += F1::ONE;
    expect_layer(check_matrix_eval(&fx.vk, &u, &lam), CompressLayer::MatrixEval, "moved r_x*");
    let mut u = fx.u_star.clone();
    u.v[1] += F1::ONE;
    expect_layer(check_matrix_eval(&fx.vk, &u, &lam), CompressLayer::MatrixEval, "value v*_1");
    let t = fx.vk.hfs().t();
    let mut u = fx.u_star.clone();
    u.v[t] += F1::ONE;
    expect_layer(
      check_witness_opening(&fx.vk, &head, &u, &p.w_open),
      CompressLayer::WitnessOpening,
      "value v*_t",
    );
    let mut u = fx.u_star.clone();
    u.io[0] += F1::ONE;
    expect_layer(
      check_witness_opening(&fx.vk, &head, &u, &p.w_open),
      CompressLayer::WitnessOpening,
      "public io* (z claim)",
    );
    // the opening is bound to the head digest (another statement's transcript)
    let mut h2 = head.clone();
    let last = h2.len() - 1;
    h2[last] ^= 1;
    expect_layer(
      check_witness_opening(&fx.vk, &h2, &fx.u_star, &p.w_open),
      CompressLayer::WitnessOpening,
      "opening under another head",
    );
  }
  run(chain_direct());
  run(tree_direct());
  run(chain_span());
}

/// Openings: the IPA (witness opening) and the Spartan proof (CycleFold).
#[test]
fn test_compress_rejects_openings() {
  fn run<V: FinalVariant>(fx: &Fx<V>) {
    let p = decode(&fx.vk, &fx.proof).unwrap();
    // IPA: re-encode with a modified field via bincode round trip of the section bytes
    let ipa = bincode::serde::encode_to_vec(&p.w_open, bincode::config::legacy()).unwrap();
    let n = ipa.len();
    let mut bad = ipa.clone();
    bad[n - 32] ^= 1; // a_hat
    let w2: InnerProductArgument<E1> =
      bincode::serde::decode_from_slice(&bad, bincode::config::legacy())
        .unwrap()
        .0;
    expect_layer(
      tampered(fx, |q| q.w_open = w2),
      CompressLayer::WitnessOpening,
      "IPA a_hat",
    );
    let mut sp = bincode::serde::encode_to_vec(&p.cf_snark, bincode::config::legacy()).unwrap();
    // eval_W sits after outer sum-check, claims, eval_E and the inner sum-check
    let f = p.cf_snark.field_bytes().unwrap();
    let off: usize = f.iter().take(4).map(|x| x.1).sum();
    sp[off] ^= 1;
    if let Ok((s2, _)) = bincode::serde::decode_from_slice(&sp, bincode::config::legacy()) {
      expect_layer(
        tampered(fx, |q| q.cf_snark = s2),
        CompressLayer::CycleFold,
        "Spartan eval_W",
      );
    }
    expect_layer(
      check_cyclefold(&fx.vk, &{
        let mut c = p.head.cf.clone();
        c.u += <E2 as Engine>::Scalar::ONE;
        c
      }, &p.cf_snark),
      CompressLayer::CycleFold,
      "Spartan against another CycleFold instance",
    );
  }
  run(chain_direct());
  run(tree_span());
}

/// The masked z opening: a commitment with a tail beyond num_w (generators the HFS key does not
/// have) cannot shift the public part of z*. With the unmasked eq vector a prover could open
/// `comm_W* + δ·G_{num_w+1}` to a claim whose io* is shifted by δ; the masked check rejects it.
#[test]
fn test_masked_opening_closes_tail_shift() {
  let fx = chain_direct();
  let hfs = fx.vk.hfs();
  let (num_w, n) = (fx.num_w, 1usize << hfs.s_prime());
  let ck = <E1 as Engine>::CE::setup(crate::kilonova::hfs::CK_LABEL, n);
  let ck_c = <E1 as Engine>::CE::setup(super::IPA_CK_LABEL, 1);
  let delta = F1::from(1234);
  // cheating witness: the honest W* plus δ at position num_w + 1 (the io slot of z*)
  let mut a = fx.w_star.w.clone();
  a.resize(n, F1::ZERO);
  a[num_w + 1] = delta;
  let mut u = fx.u_star.clone();
  u.comm_w = <E1 as Engine>::CE::commit(&ck, &a, &F1::ZERO);
  // the cheater's claim: z̃ with io*[0] replaced by io*[0] − δ, i.e. the io slot looks shifted
  u.io[0] -= delta;
  let p = decode(&fx.vk, &fx.proof).unwrap();
  let head = encode_head(&p.head);
  // unmasked evaluation: ⟨a, eq(r_y)⟩ = v_t − u·eq(num_w) − Σ io_j eq(num_w+1+j) holds for the
  // cheater's (shifted io, tailed commitment)
  let eq = eq_table(&u.r_y);
  let y_unmasked = {
    let mut y = u.v[hfs.t()] - u.u * eq[num_w];
    for (j, x) in u.io.iter().enumerate() {
      y -= *x * eq[num_w + 1 + j];
    }
    y
  };
  let ip = a.iter().zip(&eq).fold(F1::ZERO, |s, (x, e)| s + *x * e);
  assert_eq!(ip, y_unmasked, "the unmasked relation accepts the tail shift");
  let mut tr = super::compress_transcript(fx.vk.pp_digest(), super::head_digest(&head));
  let arg = InnerProductArgument::prove(
    &ck,
    &ck_c,
    &InnerProductInstance::new(&u.comm_w, &eq, &y_unmasked),
    &InnerProductWitness::new(&a),
    &mut tr,
  )
  .unwrap();
  expect_layer(
    check_witness_opening(&fx.vk, &head, &u, &arg),
    CompressLayer::WitnessOpening,
    "tail shift under the masked check",
  );
}

// ---------------------------------------------------------------------------------------------
// Byte-level tampering, truncation, forged lengths
// ---------------------------------------------------------------------------------------------

/// Every byte position of the header and the framing, and the first, a middle and the last byte
/// of every section payload, flipped one at a time: all rejected. Truncations and an extension
/// are Format; forged section lengths are Format.
#[test]
fn test_compress_rejects_byte_tampering() {
  fn run<V: FinalVariant>(fx: &Fx<V>) {
    let bytes = &fx.proof;
    let mut positions: Vec<usize> = (0..format::HEADER_BYTES).collect();
    let mut off = format::HEADER_BYTES;
    let mut per_section = Vec::new();
    for i in 0..NUM_SECTIONS {
      positions.extend(off..off + format::FRAMING_BYTES);
      let len = u32::from_le_bytes(bytes[off + 1..off + 5].try_into().unwrap()) as usize;
      let p0 = off + format::FRAMING_BYTES;
      if len > 0 {
        positions.extend([p0, p0 + len / 2, p0 + len - 1]);
      }
      per_section.push((SECTIONS[i], p0, len));
      off = p0 + len;
    }
    assert_eq!(off, bytes.len());
    let mut layers = std::collections::BTreeMap::<String, usize>::new();
    for &pos in &positions {
      for bit in [0u8, 7] {
        let mut b = bytes.clone();
        b[pos] ^= 1 << bit;
        match verify(fx, &b) {
          Ok(()) => panic!("byte {pos} bit {bit} flipped: accepted"),
          Err(e) => *layers.entry(format!("{:?}", e.layer())).or_default() += 1,
        }
      }
    }
    println!("[P7 byte flips] {} positions × 2 bits: {layers:?}", positions.len());
    for cut in [0, 3, 10, 15, bytes.len() / 2, bytes.len() - 1] {
      expect_layer(verify(fx, &bytes[..cut]), CompressLayer::Format, "truncated");
    }
    let mut ext = bytes.clone();
    ext.push(0);
    expect_layer(verify(fx, &ext), CompressLayer::Format, "extended");
    // forged section lengths: section 3 one shorter, section 9 one longer with an extra byte
    let (_, p3, l3) = per_section[2];
    let mut f = bytes.clone();
    f[p3 - 4..p3].copy_from_slice(&((l3 - 1) as u32).to_le_bytes());
    expect_layer(verify(fx, &f), CompressLayer::Format, "forged length (shorter)");
    let (_, p9, l9) = per_section[8];
    let mut f = bytes.clone();
    f[p9 - 4..p9].copy_from_slice(&((l9 + 1) as u32).to_le_bytes());
    f.push(0);
    expect_layer(verify(fx, &f), CompressLayer::Format, "forged length (longer)");
    let mut f = bytes.clone();
    f[p9 - 4..p9].copy_from_slice(&u32::MAX.to_le_bytes());
    expect_layer(verify(fx, &f), CompressLayer::Format, "forged length (huge)");
    // non-canonical field element (p + x) in the statement
    let (_, p2, _) = per_section[1];
    let mut f = bytes.clone();
    f[p2 + 8..p2 + 40].copy_from_slice(&[0xff; 32]);
    expect_layer(verify(fx, &f), CompressLayer::Format, "non-canonical scalar");
  }
  run(chain_direct());
  run(tree_direct());
  run(chain_span());
}
