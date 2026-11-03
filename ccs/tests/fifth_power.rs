//! P2 acceptance: the fifth-power constraint uses a repeated multiset with no intermediate
//! witnesses, and its size is compared with the equivalent R1CS.
mod common;
use common::*;
use ff::Field;
use halo2curves::pasta::Fq;
use kn_ccs::{
  gen::{fifth_power_native, fifth_power_r1cs},
  CcsError,
};

#[test]
fn native_fifth_power_is_one_row_per_step() {
  for steps in [1usize, 2, 16, 64] {
    let x0 = Fq::random(&mut rng(steps as u64));
    let (native, a) = fifth_power_native(steps, Some(x0)).unwrap();
    let a = a.unwrap();
    assert_eq!(native.template.multisets[0], vec![0, 0, 0, 0, 0]);
    assert_eq!((native.t(), native.q(), native.degree()), (2, 2, 5));
    assert_eq!(native.m, steps);
    assert_eq!(native.num_w, steps - 1);
    assert_eq!(native.num_io, 2);
    assert_eq!(native.nnz(), 3 * steps);
    assert!(native.is_satisfied(&a.z()).is_ok());

    let (r1cs, b) = fifth_power_r1cs(steps, Some(x0)).unwrap();
    let b = b.unwrap();
    assert_eq!((r1cs.t(), r1cs.q(), r1cs.degree()), (3, 2, 2));
    assert_eq!(r1cs.m, 3 * steps);
    assert_eq!(r1cs.num_w, 3 * steps - 1);
    assert_eq!(r1cs.nnz(), 10 * steps);
    assert!(r1cs.is_satisfied(&b.z()).is_ok());

    // Same computation: same public input and output.
    assert_eq!(a.io, b.io);
    println!(
      "T={steps}: native CCS m={} w={} nnz={} | R1CS m={} w={} nnz={}",
      native.m,
      native.num_w,
      native.nnz(),
      r1cs.m,
      r1cs.num_w,
      r1cs.nnz()
    );
  }
}

#[test]
fn wrong_output_is_rejected() {
  let (native, a) = fifth_power_native::<Fq>(8, Some(Fq::from(3))).unwrap();
  let mut a = a.unwrap();
  a.io[1] += Fq::ONE;
  assert_eq!(
    native.is_satisfied(&a.z()),
    Err(CcsError::Unsatisfied { row: 7 })
  );
  let mut a2 = fifth_power_native::<Fq>(8, Some(Fq::from(3)))
    .unwrap()
    .1
    .unwrap();
  a2.w[3] += Fq::ONE;
  // x_4 is wrong: row 3 (x_3^5 → x_4) and row 4 (x_4^5 → x_5) both fail; the first is named.
  assert_eq!(
    native.is_satisfied(&a2.z()),
    Err(CcsError::Unsatisfied { row: 3 })
  );
}

#[test]
fn shape_without_values() {
  let (native, a) = fifth_power_native::<Fq>(4, None).unwrap();
  assert!(a.is_none());
  let (with, _) = fifth_power_native::<Fq>(4, Some(Fq::ONE)).unwrap();
  assert_eq!(native, with, "the shape does not depend on the witness");
}
