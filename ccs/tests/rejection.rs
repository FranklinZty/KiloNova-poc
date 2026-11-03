//! P2 acceptance: tampered witnesses, out-of-range indices, wrong dimensions and non-canonical
//! encodings are rejected with the named error; all-zero matrices and boundary sizes work.
mod common;
use common::*;
use ff::{Field, PrimeField};
use halo2curves::pasta::Fp;
use kn_ccs::{
  accs::{accs_from_cccs, check_accs, check_cccs},
  encode::{decode, encode},
  gen::random_satisfiable,
  mle::{eval_matrix_mle, eval_vec_mle},
  AccsInstance, CccsInstance, Ccs, CcsError, Family, NativeCcsBuilder, SparseMatrix, Template, Var,
};

fn sample() -> (Ccs<Fp>, kn_ccs::Assignment<Fp>) {
  random_satisfiable(&Template::<Fp>::power(5), 5, 4, 2, 3, &mut rng(1)).unwrap()
}

type ToyAccs = AccsInstance<(Fp, usize), Fp>;

fn honest_accs() -> (Family<Fp>, ToyAccs, Vec<Fp>) {
  let (ccs, a) = sample();
  let family = Family::new(vec![ccs.clone()]).unwrap();
  let (r_x, r_y) = points(&ccs, &mut rng(2));
  let cccs = CccsInstance {
    comm_w: toy_commit(&a.w),
    io: a.io.clone(),
  };
  let accs = accs_from_cccs(&family, 0, &cccs, &a.w, r_x, r_y).unwrap();
  (family, accs, a.w)
}

fn is_dim(e: Result<(), CcsError>) -> bool {
  matches!(e, Err(CcsError::Dimension { .. }))
}

#[test]
fn out_of_range_indices() {
  assert!(matches!(
    SparseMatrix::<Fp>::from_triplets(2, 3, [(2, 0, Fp::ONE)]),
    Err(CcsError::IndexOutOfRange { row: 2, .. })
  ));
  assert!(matches!(
    SparseMatrix::<Fp>::from_triplets(2, 3, [(0, 3, Fp::ONE)]),
    Err(CcsError::IndexOutOfRange { col: 3, .. })
  ));
  // A builder variable that was never allocated.
  let mut b = NativeCcsBuilder::new(Template::<Fp>::power(2)).unwrap();
  b.push_row(vec![vec![(Var::W(0), Fp::ONE)], vec![]])
    .unwrap();
  assert!(matches!(b.build(), Err(CcsError::IndexOutOfRange { .. })));
}

#[test]
fn malformed_templates() {
  let bad = |t: usize, ms: Vec<Vec<usize>>, c: usize| {
    Template {
      t,
      multisets: ms,
      coeffs: vec![Fp::ONE; c],
    }
    .validate()
  };
  assert!(matches!(
    bad(2, vec![vec![0, 2]], 1),
    Err(CcsError::InvalidTemplate(_))
  ));
  assert!(matches!(
    bad(2, vec![vec![]], 1),
    Err(CcsError::InvalidTemplate(_))
  ));
  assert!(matches!(
    bad(0, vec![vec![0]], 1),
    Err(CcsError::InvalidTemplate(_))
  ));
  assert!(is_dim(bad(2, vec![vec![0]], 2)));
}

#[test]
fn wrong_dimensions() {
  let (ccs, a) = sample();
  // Wrong matrix count, wrong matrix sizes.
  let mut c = ccs.clone();
  c.matrices.pop();
  assert!(is_dim(c.validate()));
  let mut c = ccs.clone();
  c.matrices[0] = SparseMatrix::zero(ccs.m + 1, ccs.n());
  assert!(is_dim(c.validate()));
  let mut c = ccs.clone();
  c.matrices[1] = SparseMatrix::zero(ccs.m, ccs.n() - 1);
  assert!(is_dim(c.validate()));
  // Wrong z / witness / io lengths.
  assert!(matches!(
    ccs.residual(&a.z()[1..]),
    Err(CcsError::Dimension { .. })
  ));
  assert!(matches!(
    ccs.z(&a.w[1..], Fp::ONE, &a.io),
    Err(CcsError::Dimension { .. })
  ));
  assert!(matches!(
    ccs.z(&a.w, Fp::ONE, &[]),
    Err(CcsError::Dimension { .. })
  ));
  // MLE point too short for the matrix.
  assert!(eval_matrix_mle(&ccs.matrices[0], &[Fp::ONE], &[Fp::ONE]).is_err());
  assert!(eval_vec_mle(&a.z(), &[Fp::ONE]).is_err());
}

#[test]
fn accs_rejects_each_malformed_field() {
  let (family, accs, w) = honest_accs();
  check_accs(&family, &accs, &w, toy_commit).unwrap();

  let mut x = accs.clone();
  x.r_x.push(Fp::ONE);
  assert!(is_dim(check_accs(&family, &x, &w, toy_commit)));
  let mut x = accs.clone();
  x.r_y.pop();
  assert!(is_dim(check_accs(&family, &x, &w, toy_commit)));
  let mut x = accs.clone();
  x.v.pop();
  assert!(is_dim(check_accs(&family, &x, &w, toy_commit)));
  let mut x = accs.clone();
  x.lambda.push(Fp::ZERO);
  assert!(is_dim(check_accs(&family, &x, &w, toy_commit)));
  let mut x = accs.clone();
  x.io.pop();
  assert!(is_dim(check_accs(&family, &x, &w, toy_commit)));
  assert!(is_dim(check_accs(&family, &accs, &w[1..], toy_commit)));

  // Tampered witness: the commitment check names it.
  let mut w2 = w.clone();
  w2[0] += Fp::ONE;
  assert_eq!(
    check_accs(&family, &accs, &w2, toy_commit),
    Err(CcsError::Commitment)
  );
  // Tampered u or io changes z, so the z-claim v[t] fails.
  let t = family.member(0).t();
  let mut x = accs.clone();
  x.u += Fp::ONE;
  assert_eq!(
    check_accs(&family, &x, &w, toy_commit),
    Err(CcsError::Claim { index: t })
  );
  let mut x = accs.clone();
  x.io[0] += Fp::ONE;
  assert_eq!(
    check_accs(&family, &x, &w, toy_commit),
    Err(CcsError::Claim { index: t })
  );
  // Tampered λ or evaluation point changes the matrix claims.
  let mut x = accs.clone();
  x.lambda[0] += Fp::ONE;
  assert_eq!(
    check_accs(&family, &x, &w, toy_commit),
    Err(CcsError::Claim { index: 0 })
  );
  let mut x = accs.clone();
  x.r_x[0] += Fp::ONE;
  assert_eq!(
    check_accs(&family, &x, &w, toy_commit),
    Err(CcsError::Claim { index: 0 })
  );
}

#[test]
fn cccs_rejects_unsatisfied_and_wrong_commitment() {
  let (ccs, a) = sample();
  let inst = CccsInstance {
    comm_w: toy_commit(&a.w),
    io: a.io.clone(),
  };
  check_cccs(&ccs, &inst, &a.w, toy_commit).unwrap();
  let mut io = a.io.clone();
  io[0] += Fp::ONE;
  let bad = CccsInstance {
    comm_w: inst.comm_w,
    io,
  };
  // Changing io keeps the commitment but breaks the relation on some row (io is read by the
  // random matrices with overwhelming probability for this seed).
  assert!(matches!(
    check_cccs(&ccs, &bad, &a.w, toy_commit),
    Err(CcsError::Unsatisfied { .. })
  ));
  let wrong = CccsInstance {
    comm_w: (Fp::ONE, a.w.len()),
    io: a.io.clone(),
  };
  assert_eq!(
    check_cccs(&ccs, &wrong, &a.w, toy_commit),
    Err(CcsError::Commitment)
  );
}

#[test]
fn family_members_must_match() {
  let (c0, _) = sample();
  let (c1, _) = random_satisfiable(&Template::<Fp>::power(5), 6, 4, 2, 3, &mut rng(3)).unwrap();
  let (c2, _) = random_satisfiable(&Template::<Fp>::power(3), 5, 4, 2, 3, &mut rng(4)).unwrap();
  assert!(matches!(
    Family::new(vec![c0.clone(), c1]),
    Err(CcsError::Family(_))
  ));
  assert!(matches!(
    Family::new(vec![c0.clone(), c2]),
    Err(CcsError::Family(_))
  ));
  assert!(matches!(
    Family::<Fp>::new(vec![]),
    Err(CcsError::Family(_))
  ));
  let fam = Family::new(vec![c0]).unwrap();
  let inst = CccsInstance {
    comm_w: (Fp::ZERO, 0),
    io: vec![],
  };
  assert!(matches!(
    accs_from_cccs(&fam, 1, &inst, &[], vec![], vec![]),
    Err(CcsError::Family(_))
  ));
}

#[test]
fn encoding_roundtrip_and_non_canonical_inputs() {
  let (ccs, _) = sample();
  let bytes = encode(&ccs);
  assert_eq!(decode::<Fp>(&bytes).unwrap(), ccs);
  let nc = |b: &[u8]| matches!(decode::<Fp>(b), Err(CcsError::NonCanonical(_)));

  // Trailing and missing bytes, bad magic.
  assert!(nc(&[bytes.as_slice(), &[0]].concat()));
  assert!(nc(&bytes[..bytes.len() - 1]));
  let mut b = bytes.clone();
  b[5] = 2;
  assert!(nc(&b));

  let fe = 32;
  let header = 6 + 5 * 8;
  // The first template coefficient follows the header: replace it with 0xff…ff (≥ p).
  let mut b = bytes.clone();
  b[header..header + fe].fill(0xff);
  assert!(nc(&b));
  // A forged huge length must be rejected without allocating.
  let mut b = bytes.clone();
  b[6 + 4 * 8..6 + 5 * 8].copy_from_slice(&u64::MAX.to_le_bytes());
  assert!(nc(&b));

  // Non-canonical matrices: build them by hand and encode with a forged entry list.
  let enc_with = |entries: Vec<(usize, usize, Fp)>| -> Vec<u8> {
    let mut out = b"KNCCS\x01".to_vec();
    for v in [1u64, 1, 0, 2, 2] {
      out.extend_from_slice(&v.to_le_bytes());
    }
    for (c, s) in [(Fp::ONE, vec![0u64, 0]), (-Fp::ONE, vec![1])] {
      out.extend_from_slice(c.to_repr().as_ref());
      out.extend_from_slice(&(s.len() as u64).to_le_bytes());
      for j in s {
        out.extend_from_slice(&j.to_le_bytes());
      }
    }
    for mat in [entries, vec![]] {
      out.extend_from_slice(&(mat.len() as u64).to_le_bytes());
      for (r, c, v) in mat {
        out.extend_from_slice(&(r as u64).to_le_bytes());
        out.extend_from_slice(&(c as u64).to_le_bytes());
        out.extend_from_slice(v.to_repr().as_ref());
      }
    }
    out
  };
  assert!(decode::<Fp>(&enc_with(vec![(0, 0, Fp::ONE), (0, 1, Fp::ONE)])).is_ok());
  assert!(nc(&enc_with(vec![(0, 1, Fp::ONE), (0, 0, Fp::ONE)]))); // unsorted
  assert!(nc(&enc_with(vec![(0, 0, Fp::ONE), (0, 0, Fp::ONE)]))); // duplicate
  assert!(nc(&enc_with(vec![(0, 0, Fp::ZERO)]))); // explicit zero
  assert!(matches!(
    decode::<Fp>(&enc_with(vec![(0, 2, Fp::ONE)])),
    Err(CcsError::IndexOutOfRange { .. })
  ));
}

#[test]
fn all_zero_matrices_are_valid_and_trivially_satisfied() {
  let template = Template::<Fp>::product(3);
  let (m, num_w, num_io) = (4, 3, 1);
  let ccs = Ccs::new(
    m,
    num_w,
    num_io,
    template.clone(),
    (0..4)
      .map(|_| SparseMatrix::zero(m, num_w + 1 + num_io))
      .collect(),
  )
  .unwrap();
  let z: Vec<Fp> = random_point(ccs.n(), &mut rng(5));
  assert!(ccs.is_satisfied(&z).is_ok());
  let fam = Family::new(vec![ccs.clone()]).unwrap();
  let (r_x, r_y) = points(&ccs, &mut rng(6));
  let v = fam.claims(&[Fp::ONE], &z, &r_x, &r_y).unwrap();
  assert!(v[..4].iter().all(|x| bool::from(x.is_zero())));
  assert_eq!(v[4], eval_vec_mle(&z, &r_y).unwrap());
}

#[test]
fn boundary_sizes() {
  // m = 1, no witness, no io: n = 1 (only u). (u)^5 − u = 0 holds for u = 1.
  let mut b = NativeCcsBuilder::new(Template::<Fp>::power(5)).unwrap();
  b.push_row(vec![vec![(Var::One, Fp::ONE)], vec![(Var::One, Fp::ONE)]])
    .unwrap();
  let (ccs, a) = b.build().unwrap();
  let a = a.unwrap();
  assert_eq!((ccs.m, ccs.n(), ccs.num_w, ccs.num_io), (1, 1, 0, 0));
  assert!(ccs.is_satisfied(&a.z()).is_ok());
  // u = 2 fails (2^5 ≠ 2).
  assert_eq!(
    ccs.is_satisfied(&[Fp::from(2)]),
    Err(CcsError::Unsatisfied { row: 0 })
  );
  // MLEs over one entry use one variable (kilonova's .max(1)).
  let fam = Family::new(vec![ccs.clone()]).unwrap();
  assert_eq!(fam.point_dims(), (1, 1));
  let r = Fp::from(9);
  assert_eq!(eval_vec_mle(&a.z(), &[r]).unwrap(), Fp::ONE - r);
  // Zero rows: valid, vacuously satisfied.
  let (ccs, a) = NativeCcsBuilder::new(Template::<Fp>::r1cs())
    .unwrap()
    .build()
    .unwrap();
  assert_eq!(ccs.m, 0);
  assert!(ccs.is_satisfied(&a.unwrap().z()).is_ok());
}
