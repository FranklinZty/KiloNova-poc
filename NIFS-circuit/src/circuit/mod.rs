//! There are two augmented circuits: the primary and the secondary.
//! Each of them is over a curve in a 2-cycle of elliptic curves.
//! We have two running instances. Each circuit takes as input 2 hashes: one for each
//! of the running instances. Each of these hashes is H(params = H(shape, ck), i, z0, zi, U).
//! Each circuit folds the last invocation of the other into the running instance

pub mod r1cs;
use crate::{Commitment, Scheme};
use nova_snark::spartan::polys::univariate::CompressedUniPoly;
use r1cs::{AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance};

use ff::Field;
use nova_snark::spartan::polys::univariate::UniPoly;
use nova_snark::{
    constants::NUM_HASH_BITS,
    frontend::{
        num::AllocatedNum, AllocatedBit, Assignment, Boolean, ConstraintSystem, SynthesisError,
    },
    gadgets::{
        ecc::AllocatedPoint,
        utils::{
            alloc_num_equals, alloc_one, alloc_scalar_as_base, alloc_zero,
            conditionally_select_vec, le_bits_to_num,
        },
    },
    r1cs::{R1CSInstance, RelaxedR1CSInstance},
    traits::{
        circuit::StepCircuit, commitment::CommitmentTrait, Engine, ROCircuitTrait,
        ROConstantsCircuit,
    },
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct NovaAugmentedCircuitInputs<E: Engine> {
    pp_digest: E::Scalar,
    i: E::Base,
    z0: Vec<E::Base>,
    zi: Option<Vec<E::Base>>,
    U: Option<RelaxedR1CSInstance<E>>,
    ri: Option<E::Base>,
    r_next: E::Base,
    u: Option<R1CSInstance<E>>,
    T: Option<Commitment<E>>,
    S: Option<Commitment<E>>,
    c: Option<Vec<E::Base>>,
    polys: Option<Vec<CompressedUniPoly<E::Base>>>,
    taus: Option<Vec<E::Base>>,
    evals: Option<Vec<E::Base>>,
}

impl<E: Engine> NovaAugmentedCircuitInputs<E> {
    /// Create new inputs/witness for the verification circuit
    pub fn new(
        pp_digest: E::Scalar,
        i: E::Base,
        z0: Vec<E::Base>,
        zi: Option<Vec<E::Base>>,
        U: Option<RelaxedR1CSInstance<E>>,
        ri: Option<E::Base>,
        r_next: E::Base,
        u: Option<R1CSInstance<E>>,
        T: Option<Commitment<E>>,
        S: Option<Commitment<E>>,
        c: Option<Vec<E::Base>>,
        polys: Option<Vec<CompressedUniPoly<E::Base>>>,
        taus: Option<Vec<E::Base>>,
        evals: Option<Vec<E::Base>>,
    ) -> Self {
        Self {
            pp_digest,
            i,
            z0,
            zi,
            U,
            ri,
            r_next,
            u,
            T,
            S,
            c,
            polys,
            taus,
            evals,
        }
    }
}

/// The augmented circuit F' in Nova that includes a step circuit F
/// and the circuit for the verifier in Nova's non-interactive folding scheme
pub struct NovaAugmentedCircuit<'a, E: Engine, SC: StepCircuit<E::Base>> {
    is_primary_circuit: bool, // A boolean indicating if this is the primary circuit
    ro_consts: ROConstantsCircuit<E>,
    inputs: Option<NovaAugmentedCircuitInputs<E>>,
    step_circuit: &'a SC, // The function that is applied for each step
    mu: usize,
    deg: usize,
    flag: Scheme,
}

impl<'a, E: Engine, SC: StepCircuit<E::Base>> NovaAugmentedCircuit<'a, E, SC> {
    /// Create a new verification circuit for the input relaxed r1cs instances
    pub const fn new(
        is_primary_circuit: bool,
        inputs: Option<NovaAugmentedCircuitInputs<E>>,
        step_circuit: &'a SC,
        ro_consts: ROConstantsCircuit<E>,
        mu: usize,
        deg: usize,
        flag: Scheme,
    ) -> Self {
        Self {
            is_primary_circuit,
            inputs,
            step_circuit,
            ro_consts,
            mu,
            deg,
            flag,
        }
    }

    /// Allocate all witnesses and return
    fn alloc_witness<CS: ConstraintSystem<<E as Engine>::Base>>(
        &self,
        mut cs: CS,
        arity: usize,
        mu: usize,
        deg: usize,
    ) -> Result<
        (
            AllocatedNum<E::Base>,
            AllocatedNum<E::Base>,
            Vec<AllocatedNum<E::Base>>,
            Vec<AllocatedNum<E::Base>>,
            AllocatedRelaxedR1CSInstance<E>,
            AllocatedNum<E::Base>,
            AllocatedNum<E::Base>,
            AllocatedR1CSInstance<E>,
            AllocatedPoint<E>,
            AllocatedPoint<E>,
            Vec<Vec<AllocatedNum<E::Base>>>,
            Vec<Vec<AllocatedNum<E::Base>>>,
            Vec<AllocatedNum<E::Base>>,
            Vec<AllocatedNum<E::Base>>,
        ),
        SynthesisError,
    > {
        // Allocate pp_digest
        let pp_digest = alloc_scalar_as_base::<E, _>(
            cs.namespace(|| "pp_digest"),
            self.inputs.as_ref().map(|inputs| inputs.pp_digest),
        )?;

        // Allocate i
        let i = AllocatedNum::alloc(cs.namespace(|| "i"), || Ok(self.inputs.get()?.i))?;

        // Allocate z0
        let z_0 = (0..arity)
            .map(|i| {
                AllocatedNum::alloc(cs.namespace(|| format!("z0_{i}")), || {
                    Ok(self.inputs.get()?.z0[i])
                })
            })
            .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()?;

        // Allocate zi. If inputs.zi is not provided (base case) allocate default value 0
        let zero = vec![E::Base::ZERO; arity];
        let z_i = (0..arity)
            .map(|i| {
                AllocatedNum::alloc(cs.namespace(|| format!("zi_{i}")), || {
                    Ok(self.inputs.get()?.zi.as_ref().unwrap_or(&zero)[i])
                })
            })
            .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()?;

        // Allocate the running instance
        let U: AllocatedRelaxedR1CSInstance<E> = AllocatedRelaxedR1CSInstance::alloc(
            cs.namespace(|| "Allocate U"),
            self.inputs.as_ref().and_then(|inputs| inputs.U.as_ref()),
        )?;

        // Allocate ri
        let r_i = AllocatedNum::alloc(cs.namespace(|| "ri"), || {
            Ok(self.inputs.get()?.ri.unwrap_or(E::Base::ZERO))
        })?;

        // Allocate r_i+1
        let r_next =
            AllocatedNum::alloc(cs.namespace(|| "r_i+1"), || Ok(self.inputs.get()?.r_next))?;

        // Allocate the instance to be folded in
        let u = AllocatedR1CSInstance::alloc(
            cs.namespace(|| "allocate instance u to fold"),
            self.inputs.as_ref().and_then(|inputs| inputs.u.as_ref()),
        )?;

        // Allocate T
        let T = AllocatedPoint::alloc(
            cs.namespace(|| "allocate T"),
            self.inputs
                .as_ref()
                .and_then(|inputs| inputs.T.map(|T| T.to_coordinates())),
        )?;
        T.check_on_curve(cs.namespace(|| "check T on curve"))?;

        // Allocate S
        let S = AllocatedPoint::alloc(
            cs.namespace(|| "allocate S"),
            self.inputs
                .as_ref()
                .and_then(|inputs| inputs.S.map(|S| S.to_coordinates())),
        )?;
        S.check_on_curve(cs.namespace(|| "check S on curve"))?;

        // Allocate c If c is not provided (base case) allocate default value 0
        let c: Vec<Vec<AllocatedNum<E::Base>>> = (0..mu)
            .map(|i| {
                (0..deg)
                    .map(|j| {
                        AllocatedNum::alloc(cs.namespace(|| format!("c_{i}_{j}")), || {
                            Ok(E::Base::ZERO)
                        })
                    })
                    .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()
            })
            .collect::<Result<Vec<Vec<AllocatedNum<E::Base>>>, _>>()?;

        let compressed_polys = self
            .inputs
            .get()?
            .polys
            .as_ref()
            .ok_or(SynthesisError::AssignmentMissing)?;
        let mut claim_finals = E::Base::ZERO;
        let mut polys: Vec<Vec<AllocatedNum<E::Base>>> = Vec::new();
        for i in 0..compressed_polys.len() {
            let poly = compressed_polys[i].decompress(&claim_finals);
            let poly_temp: Vec<AllocatedNum<E::Base>> = (0..poly.degree() + 1)
                .map(|j| {
                    AllocatedNum::alloc(cs.namespace(|| format!("poly_{i}_{j}")), || {
                        Ok(poly.coeffs[j])
                    })
                })
                .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()?;
            polys.push(poly_temp);
        }

        let taus = self
            .inputs
            .get()?
            .taus
            .as_ref()
            .ok_or(SynthesisError::AssignmentMissing)?;
        let taus_alloc: Vec<AllocatedNum<E::Base>> = (0..taus.len())
            .map(|j| AllocatedNum::alloc(cs.namespace(|| format!("tau_{j}")), || Ok(taus[j])))
            .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()?;

        let evals = self
            .inputs
            .get()?
            .evals
            .as_ref()
            .ok_or(SynthesisError::AssignmentMissing)?;
        let evals_alloc: Vec<AllocatedNum<E::Base>> = (0..evals.len())
            .map(|j| AllocatedNum::alloc(cs.namespace(|| format!("eval_{j}")), || Ok(evals[j])))
            .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()?;

        Ok((
            pp_digest,
            i,
            z_0,
            z_i,
            U,
            r_i,
            r_next,
            u,
            T,
            S,
            c,
            polys,
            taus_alloc,
            evals_alloc,
        ))
    }

    fn synthesize_hash_check<CS: ConstraintSystem<E::Base>>(
        &self,
        mut cs: CS,
        pp_digest: &AllocatedNum<E::Base>,
        i: &AllocatedNum<E::Base>,
        z_0: &[AllocatedNum<E::Base>],
        z_i: &[AllocatedNum<E::Base>],
        U: &AllocatedRelaxedR1CSInstance<E>,
        r_i: &AllocatedNum<E::Base>,
    ) -> Result<AllocatedNum<E::Base>, SynthesisError> {
        // Check that u.x[0] = Hash(pp_digest, i, z_0, z_i, U, r_i)
        let mut ro = E::ROCircuit::new(self.ro_consts.clone());
        ro.absorb(pp_digest);
        ro.absorb(i);
        for e in z_0 {
            ro.absorb(e);
        }
        for e in z_i {
            ro.absorb(e);
        }
        U.absorb_in_ro(cs.namespace(|| "absorb U"), &mut ro)?;
        ro.absorb(r_i);

        let hash_bits = ro.squeeze(cs.namespace(|| "Input hash"), NUM_HASH_BITS)?;
        let hash = le_bits_to_num(cs.namespace(|| "bits to hash"), &hash_bits)?;

        Ok(hash)
    }

    /// Synthesizes base case and returns the new relaxed `R1CSInstance`
    fn synthesize_base_case<CS: ConstraintSystem<E::Base>>(
        &self,
        mut cs: CS,
        u: AllocatedR1CSInstance<E>,
    ) -> Result<AllocatedRelaxedR1CSInstance<E>, SynthesisError> {
        let U_default =
            AllocatedRelaxedR1CSInstance::default(cs.namespace(|| "Allocate U_default"))?;
        Ok(U_default)
    }

    /// Synthesizes non base case and returns the new relaxed `R1CSInstance`
    /// And a boolean indicating if all checks pass
    fn synthesize_non_base_case<CS: ConstraintSystem<<E as Engine>::Base>>(
        &self,
        mut cs: CS,
        pp_digest: &AllocatedNum<E::Base>,
        U: &AllocatedRelaxedR1CSInstance<E>,
        u: &AllocatedR1CSInstance<E>,
        T: &AllocatedPoint<E>,
        S: &AllocatedPoint<E>,
        c: &Vec<Vec<AllocatedNum<E::Base>>>,
        polys: &Vec<Vec<AllocatedNum<E::Base>>>,
        taus: &Vec<AllocatedNum<E::Base>>,
        evals: &Vec<AllocatedNum<E::Base>>,
    ) -> Result<AllocatedRelaxedR1CSInstance<E>, SynthesisError> {
        // Run NIFS Verifier
        let mut U_fold;
        match self.flag {
            Scheme::Nova => {
                U_fold = U.fold_with_r1cs(
                    cs.namespace(|| "compute fold of U and u"),
                    pp_digest,
                    u,
                    T,
                    S,
                    c,
                    self.deg.clone(),
                    self.ro_consts.clone(),
                )?;
            }
            Scheme::KiloNova => {
                U_fold = U.fold_with_r1cs_blc21(
                    cs.namespace(|| "compute fold of U and u"),
                    pp_digest,
                    u,
                    T,
                    S,
                    polys,
                    taus,
                    evals,
                    self.deg.clone(),
                    self.ro_consts.clone(),
                )?;
            }
            Scheme::ZKPCD => {
                U_fold = U.fold_with_r1cs_zkpcd(
                    cs.namespace(|| "compute fold of U and u"),
                    pp_digest,
                    u,
                    T,
                    S,
                    polys,
                    taus,
                    evals,
                    self.deg.clone(),
                    self.ro_consts.clone(),
                )?;
            }
        }

        Ok(U_fold)
    }
}

impl<E: Engine, SC: StepCircuit<E::Base>> NovaAugmentedCircuit<'_, E, SC> {
    /// synthesize circuit giving constraint system
    pub fn synthesize<CS: ConstraintSystem<<E as Engine>::Base>>(
        self,
        cs: &mut CS,
    ) -> Result<Vec<AllocatedNum<E::Base>>, SynthesisError> {
        let arity = self.step_circuit.arity();

        // Allocate all witnesses
        let (pp_digest, i, z_0, z_i, U, r_i, r_next, u, T, S, c, polys, taus, evals) = self
            .alloc_witness(
                cs.namespace(|| "allocate the circuit witness"),
                arity,
                self.mu,
                self.deg,
            )?;

        // Set variable indicating if this is the base case as false permanently to test NIFS verifier
        let zero = alloc_zero(cs.namespace(|| "zero"));
        let one = alloc_one(cs.namespace(|| "one"));
        let is_base_case = alloc_num_equals(cs.namespace(|| "Check if base case"), &one, &zero)?;
        // let is_base_case = alloc_num_equals(cs.namespace(|| "Check if base case"), &i.clone(), &zero)?;

        // compute hash of the non-deterministic inputs
        let hash = self.synthesize_hash_check(
            cs.namespace(|| "synthesize input hash check"),
            &pp_digest,
            &i,
            &z_0,
            &z_i,
            &U,
            &r_i,
        )?;

        let check_non_base_pass = alloc_num_equals(
            cs.namespace(|| "check consistency of u.X[0] with H(params, U, i, z0, zi)"),
            &u.X0,
            &hash,
        )?;

        // Synthesize the circuit for the base case and get the new running instance
        let Unew_base = self.synthesize_base_case(cs.namespace(|| "base case"), u.clone())?;

        // Synthesize the circuit for the non-base case and get the new running
        // instance along with a boolean indicating if all checks have passed
        let Unew_non_base = self.synthesize_non_base_case(
            cs.namespace(|| "synthesize non base case"),
            &pp_digest,
            &U,
            &u,
            &T,
            &S,
            &c,
            &polys,
            &taus,
            &evals,
        )?;

        // Either check_non_base_pass=true or we are in the base case
        let should_be_false = AllocatedBit::nor(
            cs.namespace(|| "check_non_base_pass nor base_case"),
            &check_non_base_pass,
            &is_base_case,
        )?;
        cs.enforce(
            || "check_non_base_pass nor base_case = false",
            |lc| lc + should_be_false.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        // Compute the U_new
        let Unew = Unew_base.conditionally_select(
            cs.namespace(|| "compute U_new"),
            &Unew_non_base,
            &Boolean::from(is_base_case.clone()),
        )?;

        // Compute i + 1
        let i_new = AllocatedNum::alloc(cs.namespace(|| "i + 1"), || {
            Ok(*i.get_value().get()? + E::Base::ONE)
        })?;
        cs.enforce(
            || "check i + 1",
            |lc| lc,
            |lc| lc,
            |lc| lc + i_new.get_variable() - CS::one() - i.get_variable(),
        );

        // Compute z_{i+1}
        let z_input = conditionally_select_vec(
            cs.namespace(|| "select input to F"),
            &z_0,
            &z_i,
            &Boolean::from(is_base_case),
        )?;

        let z_next = self
            .step_circuit
            .synthesize(&mut cs.namespace(|| "F"), &z_input)?;

        if z_next.len() != arity {
            return Err(SynthesisError::IncompatibleLengthVector(
                "z_next".to_string(),
            ));
        }

        // Compute the new hash H(pp_digest, Unew, i+1, z0, z_{i+1})
        let hash = self.synthesize_hash_check(
            cs.namespace(|| "synthesize output hash check"),
            &pp_digest,
            &i_new,
            &z_0,
            &z_next,
            &Unew,
            &r_next,
        )?;

        // Outputs the computed hash and u.X[1] that corresponds to the hash of the other circuit
        u.X1.inputize(cs.namespace(|| "Output unmodified hash of the other circuit"))?;
        hash.inputize(cs.namespace(|| "output new hash of this circuit"))?;

        Ok(z_next)
    }
}
