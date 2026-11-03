//! P2 acceptance: for d = 2, 3, 5, 8, 16, at least 100 deterministic random small instances
//! each agree with naive evaluation, for a repeated-multiset template (`power(d)`) and a
//! distinct-matrix template (`product(d)`), over two different prime fields.
mod common;
use common::*;
use ff::{Field, PrimeField};
use halo2curves::pasta::{Fp, Fq};
use kn_ccs::{
  accs::{accs_from_cccs, check_accs, check_cccs},
  gen::random_satisfiable,
  mle::{dense_matrix_mle_eval, dense_mle_eval, eval_matrix_mle, eval_vec_mle},
  CccsInstance, CcsError, Family, Template,
};
use rand_core::RngCore;

const DEGREES: [usize; 5] = [2, 3, 5, 8, 16];
const SEEDS: u64 = 100;

#[derive(Default, Debug)]
struct Tally {
  instances: usize,
  witness_tampered: usize,
}

fn run_instance<F: PrimeField>(template: &Template<F>, d: usize, seed: u64, tally: &mut Tally) {
  let mut r = rng(seed * 1_000 + d as u64);
  let m = 1 + (r.next_u64() % 8) as usize;
  let num_w = 1 + (r.next_u64() % 6) as usize;
  let num_io = (r.next_u64() % 4) as usize;
  let s = 1 + (r.next_u64() % 3) as usize;
  let (ccs, a) = random_satisfiable(template, m, num_w, num_io, s, &mut r).unwrap();
  assert_eq!(ccs.degree(), d);
  let z = a.z();

  // Satisfaction: sparse residual equals the naive dense residual, and both are zero.
  let sparse = ccs.residual(&z).unwrap();
  assert_eq!(sparse, dense_residual(&ccs, &z));
  assert!(ccs.is_satisfied(&z).is_ok());

  // MLEs: sparse eq-sums equal the dense halving evaluator.
  let (r_x, r_y) = points(&ccs, &mut r);
  for mat in &ccs.matrices {
    assert_eq!(
      eval_matrix_mle(mat, &r_x, &r_y).unwrap(),
      dense_matrix_mle_eval(mat, &r_x, &r_y).unwrap()
    );
  }
  assert_eq!(
    eval_vec_mle(&z, &r_y).unwrap(),
    dense_mle_eval(&z, &r_y).unwrap()
  );

  // CCCS and ACCS (K = 1) accept the honest pair.
  let family = Family::new(vec![ccs.clone()]).unwrap();
  let cccs = CccsInstance {
    comm_w: toy_commit(&a.w),
    io: a.io.clone(),
  };
  check_cccs(&ccs, &cccs, &a.w, toy_commit).unwrap();
  let accs = accs_from_cccs(&family, 0, &cccs, &a.w, r_x, r_y).unwrap();
  check_accs(&family, &accs, &a.w, toy_commit).unwrap();

  // Every claim is checked: perturbing v[j] is reported as Claim { j }.
  for j in 0..accs.v.len() {
    let mut bad = accs.clone();
    bad.v[j] += F::ONE;
    assert_eq!(
      check_accs(&family, &bad, &a.w, toy_commit),
      Err(CcsError::Claim { index: j })
    );
  }

  // Tampering a witness entry that the solved matrix reads makes the CCS fail, in both the
  // sparse and the dense path, and breaks the commitment.
  let l = *template.multisets.last().unwrap().first().unwrap();
  if let Some(&(_, col, _)) = ccs.matrices[l].entries().iter().find(|e| e.1 < num_w) {
    let mut w2 = a.w.clone();
    w2[col] += F::ONE;
    let z2 = ccs.z(&w2, F::ONE, &a.io).unwrap();
    assert!(ccs.is_satisfied(&z2).is_err());
    assert!(dense_residual(&ccs, &z2)
      .iter()
      .any(|x| !bool::from(x.is_zero())));
    assert_eq!(
      check_cccs(&ccs, &cccs, &w2, toy_commit),
      Err(CcsError::Commitment)
    );
    tally.witness_tampered += 1;
  }
  tally.instances += 1;
}

fn run_field<F: PrimeField>(name: &str) {
  for d in DEGREES {
    for (tname, template) in [
      ("power", Template::<F>::power(d)),
      ("product", Template::product(d)),
    ] {
      let mut tally = Tally::default();
      for seed in 0..SEEDS {
        run_instance(&template, d, seed, &mut tally);
      }
      println!("{name} d={d} {tname}: {tally:?}");
      assert_eq!(tally.instances, SEEDS as usize);
      // Most instances have a witness column in the solved matrix; the rest still ran every
      // other check.
      assert!(
        tally.witness_tampered >= 50,
        "{name} d={d} {tname}: {tally:?}"
      );
    }
  }
}

#[test]
fn agreement_pallas_base_field() {
  run_field::<Fp>("Fp");
}

#[test]
fn agreement_pallas_scalar_field() {
  run_field::<Fq>("Fq");
}

#[test]
fn r1cs_template_agreement() {
  let mut tally = Tally::default();
  for seed in 0..SEEDS {
    run_instance(&Template::<Fp>::r1cs(), 2, seed, &mut tally);
  }
  assert_eq!(tally.instances, SEEDS as usize);
}

/// K > 1: claims are λ-weighted sums over the family, as in the folded running instance.
#[test]
fn family_claims_are_lambda_weighted() {
  let mut r = rng(77);
  let template = Template::<Fp>::power(5);
  for k in [1usize, 2, 4, 16] {
    let members: Vec<_> = (0..k)
      .map(|_| random_satisfiable(&template, 4, 3, 2, 3, &mut r).unwrap())
      .collect();
    let family = Family::new(members.iter().map(|m| m.0.clone()).collect()).unwrap();
    let lambda = random_point::<Fp>(k, &mut r);
    let (r_x, r_y) = points(family.member(0), &mut r);
    let z = members[0].1.z();
    let v = family.claims(&lambda, &z, &r_x, &r_y).unwrap();
    for (j, vj) in v.iter().take(2).enumerate() {
      let direct = (0..k).fold(Fp::ZERO, |acc, i| {
        acc + lambda[i] * dense_matrix_mle_eval(&family.member(i).matrices[j], &r_x, &r_y).unwrap()
      });
      assert_eq!(*vj, direct);
    }
  }
}
