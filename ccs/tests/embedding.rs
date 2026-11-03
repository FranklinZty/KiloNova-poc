//! P2 acceptance: semantics are preserved across padding and template embedding, and the
//! overhead is measured. Also covers the `folding/` layout adapter.
mod common;
use common::*;
use ff::Field;
use halo2curves::pasta::Fp;
use kn_ccs::{
  accs::{accs_from_cccs, check_accs},
  gen::random_satisfiable,
  layout::{matrix_from_folding, z_from_folding, z_to_folding},
  pad::{embed_zero_terms, is_regular, lift_degree, overhead, pad, pad_z},
  CccsInstance, Ccs, Family, SparseMatrix, Template,
};

/// Every transformation maps satisfied to satisfied, and a tampered z stays unsatisfied.
fn assert_preserves(orig: &Ccs<Fp>, z: &[Fp], new: &Ccs<Fp>, z_new: &[Fp], z_bad_new: &[Fp]) {
  assert!(orig.is_satisfied(z).is_ok());
  assert!(new.is_satisfied(z_new).is_ok());
  assert!(new.is_satisfied(z_bad_new).is_err());
}

/// A tampered copy of z that breaks `orig` (the u column is read by the solved matrix).
fn tamper(orig: &Ccs<Fp>, z: &[Fp]) -> Vec<Fp> {
  let mut z2 = z.to_vec();
  z2[orig.u_col()] += Fp::ONE;
  z2
}

#[test]
fn padding_preserves_semantics() {
  let mut total = (0usize, 0usize);
  for seed in 0..100u64 {
    let mut r = rng(seed);
    let d = [2usize, 3, 5][seed as usize % 3];
    let m = 1 + seed as usize % 9;
    let num_w = 1 + seed as usize % 7;
    let num_io = seed as usize % 3;
    let (ccs, a) =
      random_satisfiable(&Template::<Fp>::power(d), m, num_w, num_io, 3, &mut r).unwrap();
    let z = a.z();
    let padded = pad(&ccs).unwrap();
    // Same rule as R1CSShape::pad: a regular shape is kept as is (m and num_w may differ);
    // otherwise both become the same power of two.
    if is_regular(&ccs) {
      assert_eq!(padded, ccs);
    } else {
      assert_eq!(padded.m, padded.num_w);
    }
    assert!(padded.m.is_power_of_two() && padded.num_w.is_power_of_two());
    let z_p = pad_z(&ccs, &padded, &z).unwrap();
    let z_bad = pad_z(&ccs, &padded, &tamper(&ccs, &z)).unwrap();
    assert!(ccs.is_satisfied(&tamper(&ccs, &z)).is_err());
    assert_preserves(&ccs, &z, &padded, &z_p, &z_bad);
    // Padding is idempotent and the honest ACCS of the padded instance checks.
    assert_eq!(pad(&padded).unwrap(), padded);
    let fam = Family::new(vec![padded.clone()]).unwrap();
    let w_p = z_p[..padded.num_w].to_vec();
    let inst = CccsInstance {
      comm_w: toy_commit(&w_p),
      io: a.io.clone(),
    };
    let (r_x, r_y) = points(&padded, &mut r);
    let accs = accs_from_cccs(&fam, 0, &inst, &w_p, r_x, r_y).unwrap();
    check_accs(&fam, &accs, &w_p, toy_commit).unwrap();
    total.0 += ccs.m * ccs.n();
    total.1 += padded.m * padded.n();
    let o = overhead(&ccs, &padded);
    assert_eq!(o.nnz.0, o.nnz.1, "padding adds no non-zeros");
  }
  println!(
    "padding over 100 instances: Σ m·n {} -> {} ({:.2}x)",
    total.0,
    total.1,
    total.1 as f64 / total.0 as f64
  );
}

#[test]
fn zero_term_embedding_preserves_semantics() {
  for seed in 0..100u64 {
    let mut r = rng(1000 + seed);
    let (ccs, a) = random_satisfiable(&Template::<Fp>::r1cs(), 5, 4, 1, 3, &mut r).unwrap();
    // Embed R1CS (t=3, q=2) into a family template with two more matrices and a degree-5 term.
    let emb = embed_zero_terms(&ccs, 2, vec![(Fp::from(3), vec![0, 3, 3, 4, 1])]).unwrap();
    let z = a.z();
    assert_preserves(&ccs, &z, &emb, &z, &tamper(&ccs, &z));
    assert_eq!(ccs.residual(&z).unwrap(), emb.residual(&z).unwrap());
    assert_eq!(
      ccs.residual(&tamper(&ccs, &z)).unwrap(),
      emb.residual(&tamper(&ccs, &z)).unwrap()
    );
    let o = overhead(&ccs, &emb);
    assert_eq!((o.t, o.q, o.d), ((3, 5), (2, 3), (2, 5)));
    assert_eq!(o.nnz.0, o.nnz.1);
  }
  // A term with no zero matrix would change the relation and is refused.
  let (ccs, _) = random_satisfiable(&Template::<Fp>::r1cs(), 2, 2, 0, 2, &mut rng(9)).unwrap();
  assert!(embed_zero_terms(&ccs, 1, vec![(Fp::ONE, vec![0, 1])]).is_err());
}

#[test]
fn degree_lifting_preserves_semantics_for_u_one() {
  for seed in 0..100u64 {
    let mut r = rng(2000 + seed);
    let (ccs, a) = random_satisfiable(&Template::<Fp>::r1cs(), 6, 5, 2, 3, &mut r).unwrap();
    let lifted = lift_degree(&ccs, 5).unwrap();
    let z = a.z();
    // Fresh instance (u = 1): residuals are identical row by row, tampered or not.
    assert_eq!(ccs.residual(&z).unwrap(), lifted.residual(&z).unwrap());
    let mut z_bad = z.clone();
    z_bad[0] += Fp::ONE;
    assert_eq!(
      ccs.residual(&z_bad).unwrap(),
      lifted.residual(&z_bad).unwrap()
    );
    let o = overhead(&ccs, &lifted);
    assert_eq!((o.t, o.d), ((3, 4), (2, 5)));
    assert_eq!(
      o.nnz.1,
      o.nnz.0 + ccs.m,
      "the u-selector adds one entry per row"
    );
  }
  // With u ≠ 1 the lifted relation differs (documented limitation): the residual changes.
  let (ccs, a) = random_satisfiable(&Template::<Fp>::r1cs(), 3, 2, 0, 2, &mut rng(7)).unwrap();
  let lifted = lift_degree(&ccs, 4).unwrap();
  let z2 = ccs.z(&a.w, Fp::from(2), &a.io).unwrap();
  assert_ne!(ccs.residual(&z2).unwrap(), lifted.residual(&z2).unwrap());
  assert!(lift_degree(&lifted, 3).is_err());
}

#[test]
fn folding_layout_adapter() {
  let (ccs, a) = random_satisfiable(&Template::<Fp>::power(3), 4, 3, 2, 3, &mut rng(11)).unwrap();
  let z = a.z();
  let zf = z_to_folding(&z, ccs.num_w, ccs.num_io).unwrap();
  assert_eq!(zf[0], Fp::ONE, "folding/ puts u first");
  assert_eq!(z_from_folding(&zf, ccs.num_w, ccs.num_io).unwrap(), z);
  // Express each matrix in the folding/ column order, convert back, and get the original.
  for mat in &ccs.matrices {
    let n = ccs.n();
    let to_f = |c: usize| -> usize {
      if c == ccs.num_w {
        0
      } else if c > ccs.num_w {
        c - ccs.num_w
      } else {
        c + 1 + ccs.num_io
      }
    };
    let mf = SparseMatrix::from_triplets(
      ccs.m,
      n,
      mat.entries().iter().map(|&(r, c, v)| (r, to_f(c), v)),
    )
    .unwrap();
    assert_eq!(
      &matrix_from_folding(&mf, ccs.num_w, ccs.num_io).unwrap(),
      mat
    );
    // M·z is the same in either layout.
    assert_eq!(mf.mul_vec(&zf).unwrap(), mat.mul_vec(&z).unwrap());
  }
}
