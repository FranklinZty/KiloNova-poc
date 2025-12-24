#![allow(unused)]
#[allow(non_snake_case)]
#[allow(dead_code)]

mod circuit;
use std::time::Instant;
use crate::circuit::{NovaAugmentedCircuit};

use ff::{Field, PrimeField};
use nova_snark::{
    frontend::{
        num::AllocatedNum,
        r1cs::{NovaShape, NovaWitness},
        solver::SatisfyingAssignment,
        test_shape_cs::TestShapeCS,
        ConstraintSystem, SynthesisError,
    },
    provider::{Bn256EngineKZG, PallasEngine, VestaEngine, Secp256k1Engine},
    traits::{
        commitment::CommitmentEngineTrait,
        circuit::TrivialCircuit,
        snark::default_ck_hint,
        Engine,
        ROConstants,
        ROConstantsCircuit,
    },
    gadgets::utils::scalar_as_base,
};

// some type aliases
type CommitmentKey<E> = <<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey;
type DerandKey<E> = <<E as Engine>::CE as CommitmentEngineTrait<E>>::DerandKey;
type Commitment<E> = <<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment;
type CE<E> = <E as Engine>::CE;

#[derive(Copy, Clone)]
pub(crate) enum Scheme {
    Nova, BCL21, ZKPCD
}

fn test_recursive_circuit_with<E1, E2>(flag: Scheme, mu: usize, deg: usize) where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
{
    let ro_consts = ROConstantsCircuit::<E2>::default();
    let tc = TrivialCircuit::default();
    // Initialize the shape and ck for the primary
    let circuit: NovaAugmentedCircuit<'_, E2, TrivialCircuit<<E2 as Engine>::Base>> =
        NovaAugmentedCircuit::new(true, None, &tc, ro_consts.clone(), mu, deg, flag.clone());

    let mut cs: TestShapeCS<E1> = TestShapeCS::new();
    let start = Instant::now();
    let _ = circuit.synthesize(&mut cs);
    let elapsed = start.elapsed();
    let (shape1, ck1) = cs.r1cs_shape(&*default_ck_hint());

    match flag {
        Scheme::ZKPCD => {
            println!("Simulating ZK-PCD recursive step with {} steps and {} degrees", mu, deg);
        },
        Scheme::BCL21 => {
            println!("Simulating BCL+21 recursive step with {} steps and {} degrees", mu, deg);
        },
        Scheme::Nova => {
            println!("Simulating Nova recursive step with {} steps and {} degrees", mu, deg);
        }
    }
    println!("Recursive constraint number: {}", cs.num_constraints());
    println!("Recursive synthesize time: {} ms", elapsed.as_millis());
    println!("--------------------------------------------------------------------------");
}

fn main() {
    println!("Run the baseline non-zk Nova recursive circuit");
    test_recursive_circuit_with::<PallasEngine, VestaEngine>(Scheme::Nova, 1, 1);
    for mu in [1,2,3] {
        for deg in [2,3,4] {
            test_recursive_circuit_with::<PallasEngine, VestaEngine>(Scheme::BCL21, mu, deg);
            test_recursive_circuit_with::<PallasEngine, VestaEngine>(Scheme::ZKPCD, mu, deg);
        }
    }
}
