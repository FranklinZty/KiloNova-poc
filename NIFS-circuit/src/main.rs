#![allow(unused)]
#[allow(non_snake_case)]
#[allow(dead_code)]
mod circuit;

use crate::circuit::{r1cs::sumcheck_prove, NovaAugmentedCircuit, NovaAugmentedCircuitInputs};
use digest::consts::U24;
use std::marker::PhantomData;
use std::time::Instant;

use ff::{Field, PrimeField};
use nova_snark::errors::NovaError;
use nova_snark::frontend::gadgets::poseidon::{
    IOPattern, Simplex, Sponge, SpongeAPI, SpongeOp, Strength,
};
use nova_snark::frontend::num::AllocatedNum;
use nova_snark::frontend::{Elt, SpongeCircuit, SynthesisError};
use nova_snark::gadgets::utils::scalar_as_base;
use nova_snark::nova::PublicParams;
use nova_snark::provider::{Bn256EngineKZG, GrumpkinEngine};
use nova_snark::spartan::polys::univariate::CompressedUniPoly;
use nova_snark::traits::circuit::StepCircuit;
use nova_snark::traits::Group;
use nova_snark::{
    frontend::{
        r1cs::{NovaShape, NovaWitness},
        test_shape_cs::TestShapeCS,
        ConstraintSystem,
    },
    provider::{PallasEngine, VestaEngine},
    traits::{
        circuit::TrivialCircuit, commitment::CommitmentEngineTrait, snark::default_ck_hint, Engine,
        ROConstantsCircuit,
    },
};
use rand_core::OsRng;

// some type aliases
type CommitmentKey<E> = <<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey;
type DerandKey<E> = <<E as Engine>::CE as CommitmentEngineTrait<E>>::DerandKey;
type Commitment<E> = <<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment;
type CE<E> = <E as Engine>::CE;

#[derive(Copy, Clone)]
pub(crate) enum Scheme {
    Nova,
    KiloNova,
    ZKPCD,
}

#[derive(Clone, Debug, Default)]
struct CubicCircuit<F: PrimeField> {
    _p: PhantomData<F>,
}

impl<F: PrimeField> StepCircuit<F> for CubicCircuit<F> {
    fn arity(&self) -> usize {
        1
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        // Consider a cubic equation: `x^3 + x + 5 = y`, where `x` and `y` are respectively the input and output.
        let x = &z[0];
        let x_sq = x.square(cs.namespace(|| "x_sq"))?;
        let x_cu = x_sq.mul(cs.namespace(|| "x_cu"), x)?;
        let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
            Ok(x_cu.get_value().unwrap() + x.get_value().unwrap() + F::from(5u64))
        })?;

        cs.enforce(
            || "y = x^3 + x + 5",
            |lc| {
                lc + x_cu.get_variable()
                    + x.get_variable()
                    + CS::one()
                    + CS::one()
                    + CS::one()
                    + CS::one()
                    + CS::one()
            },
            |lc| lc + CS::one(),
            |lc| lc + y.get_variable(),
        );

        Ok(vec![y])
    }
}

impl<F: PrimeField> CubicCircuit<F> {
    fn output(&self, z: &[F]) -> Vec<F> {
        vec![z[0] * z[0] * z[0] + z[0] + F::from(5u64)]
    }
}

fn test_recursive_circuit_with<E1, E2>(flag: Scheme, mu: usize, deg: usize)
where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
{
    // produce public parameters
    let test_circuit = TrivialCircuit::<<E1 as Engine>::Scalar>::default();
    let pp = PublicParams::<E1, E2, TrivialCircuit<<E1 as Engine>::Scalar>>::setup(
        &test_circuit,
        &*default_ck_hint(),
        &*default_ck_hint(),
    )
    .unwrap();

    // generate a sumcheck proof
    // TODO: enable the sumcheck for arbitrary degree (now is only a*b - c)
    let (proof, taus, final_evals) = sumcheck_prove::<E1>(mu).unwrap();

    // explicitly convert all E2::Scalar elements to E1::Base elements
    let polys_e1: Vec<CompressedUniPoly<<E2 as Engine>::Base>> =
        proof.compressed_polys.into_iter().collect();
    let taus_e1: Vec<<E2 as Engine>::Base> = taus.into_iter().collect();
    let evals_e1: Vec<<E2 as Engine>::Base> = final_evals.into_iter().collect();
    let ri_primary = E1::Scalar::random(&mut OsRng);

    let ro_consts = ROConstantsCircuit::<E2>::default();
    let tc = TrivialCircuit::default();

    let inputs: NovaAugmentedCircuitInputs<E2> = NovaAugmentedCircuitInputs::new(
        scalar_as_base::<E1>(pp.digest()),
        E1::Scalar::ZERO,
        vec![E1::Scalar::ZERO],
        None,
        None,
        None,
        ri_primary, // "r next"
        None,
        None,
        None,
        None,
        Some(polys_e1),
        Some(taus_e1),
        Some(evals_e1),
    );

    let circuit: NovaAugmentedCircuit<'_, E2, TrivialCircuit<<E2 as Engine>::Base>> =
        NovaAugmentedCircuit::new(
            true,
            Some(inputs),
            &tc,
            ro_consts.clone(),
            mu,
            deg,
            flag.clone(),
        );

    let mut cs: TestShapeCS<E1> = TestShapeCS::new();
    let start = Instant::now();
    let _ = circuit.synthesize(&mut cs);
    let elapsed = start.elapsed();
    let (shape1, ck1) = cs.r1cs_shape(&*default_ck_hint());

    match flag {
        Scheme::ZKPCD => {
            println!(
                "Simulating ZK-PCD recursive step with {} steps and {} degrees",
                mu, deg
            );
        }
        Scheme::KiloNova => {
            println!(
                "Simulating BCL+21 recursive step with {} steps and {} degrees",
                mu, deg
            );
        }
        Scheme::Nova => {
            println!(
                "Simulating Nova recursive step with {} steps and {} degrees",
                mu, deg
            );
        }
    }
    println!("Recursive constraint number: {}", cs.num_constraints());
    println!("Recursive synthesize time: {} ms", elapsed.as_millis());
    println!("--------------------------------------------------------------------------");
}

fn main() {
    println!("Run the baseline non-zk Nova recursive circuit");
    test_recursive_circuit_with::<PallasEngine, VestaEngine>(Scheme::Nova, 1, 1);
    for mu in [1, 2, 3] {
        for deg in [2, 3, 4] {
            test_recursive_circuit_with::<PallasEngine, VestaEngine>(Scheme::KiloNova, mu, deg);
            test_recursive_circuit_with::<PallasEngine, VestaEngine>(Scheme::ZKPCD, mu, deg);
        }
    }
}
