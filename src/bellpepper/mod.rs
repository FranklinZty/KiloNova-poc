use std::marker::PhantomData;

use bellpepper_core::{num::AllocatedNum, Circuit, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use pasta_curves::group::Group;
use spartan2::SNARK;


#[derive(Clone, Debug, Default)]
struct CubicCircuit<F: PrimeField> {
  _p: PhantomData<F>,
}

impl<F> Circuit<F> for CubicCircuit<F>
where
  F: PrimeField,
{
  fn synthesize<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
    // Consider a cubic equation: `x^3 + x + 1 = y`, where `x` and `y` are respectively the input and output.
    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(F::ONE + F::ONE))?;
    let x_sq = x.square(cs.namespace(|| "x_sq"))?;
    let x_cu = x_sq.mul(cs.namespace(|| "x_cu"), &x)?;
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(x_cu.get_value().unwrap() + x.get_value().unwrap() + F::from(1u64))
    })?;

    cs.enforce(
      || "y = x^3 + x + 1",
      |lc| lc + x_cu.get_variable() + x.get_variable() + CS::one(),
      |lc| lc + CS::one(),
      |lc| lc + y.get_variable(),
    );

    let _ = y.inputize(cs.namespace(|| "output"));

    Ok(())
  }
}


#[cfg(test)]
pub mod test {
    use super::*;
    use pasta_curves::group::Group;
    use spartan2::SNARK;

    #[test]
    fn test_bellpepper() {
        type G = pasta_curves::pallas::Point;
        type EE = spartan2::provider::ipa_pc::EvaluationEngine<G>;
        type S = spartan2::spartan::snark::RelaxedR1CSSNARK<G, EE>;

        // Create an instance of our circuit (with the preimage as a witness).
        let circuit = CubicCircuit::<<G as Group>::Scalar>::default();

        // produce keys
        let (pk, vk) = SNARK::<G, S, CubicCircuit<<G as Group>::Scalar>>::setup(circuit.clone()).unwrap();

        // produce a SNARK
        let res = SNARK::prove(&pk, circuit);
        assert!(res.is_ok());
        let snark = res.unwrap();

        // verify the SNARK
        let res = snark.verify(&vk, &[<G as Group>::Scalar::from(11u64)]);
        assert!(res.is_ok());
    }
}