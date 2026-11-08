//! P3 fixture: two predicates with the same template and dimensions but different wiring,
//! negative coefficients and wrapping values.
use ff::Field;
use halo2curves::pasta::Fq as Fp;
use kn_ccs::r#gen::{wiring_pair, PairTemplate};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

#[test]
fn wiring_pairs_are_satisfied_and_differ() {
  let mut rng = ChaCha20Rng::seed_from_u64(7);
  for tpl in [PairTemplate::R1cs, PairTemplate::Power5] {
    for reps in [1, 2, 5] {
      let (c0, _) = wiring_pair::<Fp>(tpl, 0, reps, None).unwrap();
      let (c1, _) = wiring_pair::<Fp>(tpl, 1, reps, None).unwrap();
      assert_eq!((c0.m, c0.num_w, c0.num_io), (c1.m, c1.num_w, c1.num_io));
      assert_eq!((c0.m, c0.num_io), (2 * reps, 2));
      assert_eq!(c0.num_w, 2 * reps - 1);
      assert_eq!(c0.template, c1.template);
      assert_ne!(c0.matrices, c1.matrices, "different wiring");
      // Every member carries a negative coefficient.
      for c in [&c0, &c1] {
        assert!(c
          .matrices
          .iter()
          .flat_map(|m| m.entries())
          .any(|e| e.2 == -Fp::ONE || e.2 == -Fp::from(11) || e.2 == -Fp::from(7)));
      }
      for k in 0..2 {
        for _ in 0..20 {
          let x = Fp::random(&mut rng);
          let (c, a) = wiring_pair(tpl, k, reps, Some(x)).unwrap();
          let mut a = a.unwrap();
          assert!(c.is_satisfied(&a.z()).is_ok(), "{tpl:?} k={k} reps={reps}");
          // An output that is off by one is rejected.
          a.io[1] += Fp::ONE;
          assert!(c.is_satisfied(&a.z()).is_err());
        }
      }
    }
  }
  assert!(wiring_pair::<Fp>(PairTemplate::R1cs, 2, 1, None).is_err());
  assert!(wiring_pair::<Fp>(PairTemplate::R1cs, 0, 0, None).is_err());
}
