//! This module implements various gadgets necessary for folding R1CS types.

use ff::Field;
use nova_snark::errors::NovaError;
use nova_snark::spartan::polys::univariate::CompressedUniPoly;
use nova_snark::traits::TranscriptEngineTrait;
use nova_snark::{
    constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_CHALLENGE_BITS},
    frontend::{num::AllocatedNum, Assignment, Boolean, ConstraintSystem, SynthesisError},
    gadgets::{
        ecc::AllocatedPoint,
        nonnative::{
            bignat::BigNat,
            util::{f_to_nat, Num},
        },
        utils::{
            alloc_bignat_constant, alloc_one, alloc_scalar_as_base, alloc_zero,
            conditionally_select, conditionally_select_bignat, le_bits_to_num,
        },
    },
    r1cs::{R1CSInstance, RelaxedR1CSInstance},
    spartan::{polys::eq::EqPolynomial, polys::multilinear::MultilinearPolynomial, sumcheck::*},
    traits::{commitment::CommitmentTrait, Engine, Group, ROCircuitTrait, ROConstantsCircuit},
};
use num_traits::pow;
use rand_core::OsRng;
use rand_core::RngCore;
use std::ops::{Mul, Sub};

/// An Allocated R1CS Instance
#[derive(Clone)]
pub struct AllocatedR1CSInstance<E: Engine> {
    pub(crate) comm_W: AllocatedPoint<E>,
    pub(crate) X0: AllocatedNum<E::Base>,
    pub(crate) X1: AllocatedNum<E::Base>,
}

impl<E: Engine> AllocatedR1CSInstance<E> {
    /// Takes the r1cs instance and creates a new allocated r1cs instance
    pub fn alloc<CS: ConstraintSystem<<E as Engine>::Base>>(
        mut cs: CS,
        u: Option<&R1CSInstance<E>>,
    ) -> Result<Self, SynthesisError> {
        let comm_W = AllocatedPoint::alloc(
            cs.namespace(|| "allocate comm_W"),
            u.map(|u| u.comm_W.to_coordinates()),
        )?;
        comm_W.check_on_curve(cs.namespace(|| "check comm_W on curve"))?;

        let X0 = alloc_scalar_as_base::<E, _>(cs.namespace(|| "allocate X[0]"), u.map(|u| u.X[0]))?;
        let X1 = alloc_scalar_as_base::<E, _>(cs.namespace(|| "allocate X[1]"), u.map(|u| u.X[1]))?;

        Ok(AllocatedR1CSInstance { comm_W, X0, X1 })
    }

    /// Absorb the provided instance in the RO
    pub fn absorb_in_ro(&self, ro: &mut E::ROCircuit) {
        ro.absorb(&self.comm_W.x);
        ro.absorb(&self.comm_W.y);
        ro.absorb(&self.comm_W.is_infinity);
        ro.absorb(&self.X0);
        ro.absorb(&self.X1);
    }
}

/// An Allocated Relaxed R1CS Instance
pub struct AllocatedRelaxedR1CSInstance<E: Engine> {
    pub(crate) W: AllocatedPoint<E>,
    pub(crate) R: AllocatedPoint<E>,
    pub(crate) E: AllocatedPoint<E>,
    pub(crate) u: AllocatedNum<E::Base>,
    pub(crate) X0: BigNat<E::Base>,
    pub(crate) X1: BigNat<E::Base>,
}

impl<E: Engine> AllocatedRelaxedR1CSInstance<E> {
    /// Allocates the given `RelaxedR1CSInstance` as a witness of the circuit
    pub fn alloc<CS: ConstraintSystem<<E as Engine>::Base>>(
        mut cs: CS,
        inst: Option<&RelaxedR1CSInstance<E>>,
    ) -> Result<Self, SynthesisError> {
        // We do not need to check that W or E are well-formed (e.g., on the curve) as we do a hash check
        // in the Nova augmented circuit, which ensures that the relaxed instance
        // came from a prior iteration of Nova.
        let W = AllocatedPoint::alloc(
            cs.namespace(|| "allocate W"),
            inst.map(|inst| inst.comm_W.to_coordinates()),
        )?;

        let R = AllocatedPoint::alloc(
            cs.namespace(|| "allocate R"),
            inst.map(|inst| inst.comm_W.to_coordinates()),
        )?;

        let E = AllocatedPoint::alloc(
            cs.namespace(|| "allocate E"),
            inst.map(|inst| inst.comm_E.to_coordinates()),
        )?;

        // u << |E::Base| despite the fact that u is a scalar.
        // So we parse all of its bytes as a E::Base element
        let u =
            alloc_scalar_as_base::<E, _>(cs.namespace(|| "allocate u"), inst.map(|inst| inst.u))?;

        // Allocate X0 and X1. If the input instance is None, then allocate default values 0.
        let X0 = BigNat::alloc_from_nat(
            cs.namespace(|| "allocate X[0]"),
            || Ok(f_to_nat(&inst.map_or(E::Scalar::ZERO, |inst| inst.X[0]))),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        let X1 = BigNat::alloc_from_nat(
            cs.namespace(|| "allocate X[1]"),
            || Ok(f_to_nat(&inst.map_or(E::Scalar::ZERO, |inst| inst.X[1]))),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        Ok(AllocatedRelaxedR1CSInstance { W, R, E, u, X0, X1 })
    }

    /// Allocates the hardcoded default `RelaxedR1CSInstance` in the circuit.
    /// W = E = 0, u = 0, X0 = X1 = 0
    pub fn default<CS: ConstraintSystem<<E as Engine>::Base>>(
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        let W = AllocatedPoint::default(cs.namespace(|| "allocate W"))?;
        let R = W.clone();
        let E = W.clone();

        let u = W.x.clone(); // In the default case, W.x = u = 0

        // X0 and X1 are allocated and in the honest prover case set to zero
        // If the prover is malicious, it can set to arbitrary values, but the resulting
        // relaxed R1CS instance with the checked default values of W, E, and u must still be satisfying
        let X0 = BigNat::alloc_from_nat(
            cs.namespace(|| "allocate x_default[0]"),
            || Ok(f_to_nat(&E::Scalar::ZERO)),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        let X1 = BigNat::alloc_from_nat(
            cs.namespace(|| "allocate x_default[1]"),
            || Ok(f_to_nat(&E::Scalar::ZERO)),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        Ok(AllocatedRelaxedR1CSInstance { W, R, E, u, X0, X1 })
    }

    /// Absorb the provided instance in the RO
    pub fn absorb_in_ro<CS: ConstraintSystem<<E as Engine>::Base>>(
        &self,
        mut cs: CS,
        ro: &mut E::ROCircuit,
    ) -> Result<(), SynthesisError> {
        ro.absorb(&self.W.x);
        ro.absorb(&self.W.y);
        ro.absorb(&self.W.is_infinity);
        ro.absorb(&self.R.x);
        ro.absorb(&self.R.y);
        ro.absorb(&self.R.is_infinity);
        ro.absorb(&self.E.x);
        ro.absorb(&self.E.y);
        ro.absorb(&self.E.is_infinity);
        ro.absorb(&self.u);

        // Analyze X0 as limbs
        let X0_bn = self
            .X0
            .as_limbs()
            .iter()
            .enumerate()
            .map(|(i, limb)| {
                limb.as_allocated_num(cs.namespace(|| format!("convert limb {i} of X_r[0] to num")))
            })
            .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()?;

        // absorb each of the limbs of X[0]
        for limb in X0_bn {
            ro.absorb(&limb);
        }

        // Analyze X1 as limbs
        let X1_bn = self
            .X1
            .as_limbs()
            .iter()
            .enumerate()
            .map(|(i, limb)| {
                limb.as_allocated_num(cs.namespace(|| format!("convert limb {i} of X_r[1] to num")))
            })
            .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()?;

        // absorb each of the limbs of X[1]
        for limb in X1_bn {
            ro.absorb(&limb);
        }

        Ok(())
    }

    /// Folds self with a relaxed r1cs instance and returns the result
    pub fn fold_with_r1cs_blc21<CS: ConstraintSystem<<E as Engine>::Base>>(
        &self,
        mut cs: CS,
        params: &AllocatedNum<E::Base>, // hash of R1CSShape of F'
        u: &AllocatedR1CSInstance<E>,
        T: &AllocatedPoint<E>,
        S: &AllocatedPoint<E>,
        compressed_polys: &Vec<Vec<AllocatedNum<E::Base>>>,
        taus: &Vec<AllocatedNum<E::Base>>,
        final_evals: &Vec<AllocatedNum<E::Base>>,
        deg: usize,
        ro_consts: ROConstantsCircuit<E>,
    ) -> Result<AllocatedRelaxedR1CSInstance<E>, SynthesisError> {
        // Compute r:
        let mut ro = E::ROCircuit::new(ro_consts);
        ro.absorb(params);

        // running instance `U` does not need to absorbed since u.X[0] = Hash(params, U, i, z0, zi)
        u.absorb_in_ro(&mut ro);

        ro.absorb(&T.x);
        ro.absorb(&T.y);
        ro.absorb(&T.is_infinity);
        ro.absorb(&S.x);
        ro.absorb(&S.y);
        ro.absorb(&S.is_infinity);

        let r_bits = ro.squeeze(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
        let r = le_bits_to_num(cs.namespace(|| "r"), &r_bits)?;

        // W_fold = self.W + r * u.W
        let rW = u.comm_W.scalar_mul(cs.namespace(|| "r * u.W"), &r_bits)?;
        let W_fold = self.W.add(cs.namespace(|| "self.W + r * u.W"), &rW)?;

        // R_fold = self.R + r*S + r^2*S + ... + r^{n-1}*S
        let rS = S.scalar_mul(cs.namespace(|| "r * S"), &r_bits)?;
        // let R_fold = self.R + r*S
        let mut R_fold = self.R.add(cs.namespace(|| "self.R + rS"), &rS)?;
        if deg > 1 {
            let mut r_power_S = rS;
            // For loop for computing r^2*S, r^3*S, ..., r^{n-1}*S
            for i in 2..pow(2, deg) {
                // compute the next r^i * S
                r_power_S =
                    r_power_S.scalar_mul(cs.namespace(|| format!("r^{} * S", i)), &r_bits)?;
                // accumulate to R_fold
                R_fold = R_fold.add(cs.namespace(|| format!("R_fold + r^{}*S", i)), &r_power_S)?;
            }
        }

        // Compute the Sumcheck Verification
        let mut eval_e = alloc_zero(cs.namespace(|| "zero"));
        let mut u_u = alloc_one(cs.namespace(|| "one"));
        Self::sumcheck_verify(
            &mut cs,
            ro,
            3,
            compressed_polys,
            taus,
            final_evals,
            eval_e,
            u_u,
        )
        .unwrap();

        // E_fold = self.E + r * T
        let rT = T.scalar_mul(cs.namespace(|| "r * T"), &r_bits)?;
        let E_fold = self.E.add(cs.namespace(|| "self.E + r * T"), &rT)?;

        // u_fold = u_r + r
        let u_fold = AllocatedNum::alloc(cs.namespace(|| "u_fold"), || {
            Ok(*self.u.get_value().get()? + r.get_value().get()?)
        })?;
        cs.enforce(
            || "Check u_fold",
            |lc| lc,
            |lc| lc,
            |lc| lc + u_fold.get_variable() - self.u.get_variable() - r.get_variable(),
        );

        // Fold the IO:
        // Analyze r into limbs
        let r_bn = BigNat::from_num(
            cs.namespace(|| "allocate r_bn"),
            &Num::from(r),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Allocate the order of the non-native field as a constant
        let m_bn = alloc_bignat_constant(
            cs.namespace(|| "alloc m"),
            &E::GE::group_params().2,
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Analyze X0 to bignat
        let X0_bn = BigNat::from_num(
            cs.namespace(|| "allocate X0_bn"),
            &Num::from(u.X0.clone()),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Fold self.X[0] + r * X[0]
        let (_, r_0) = X0_bn.mult_mod(cs.namespace(|| "r*X[0]"), &r_bn, &m_bn)?;
        // add X_r[0]
        let r_new_0 = self.X0.add(&r_0)?;
        // Now reduce
        let X0_fold = r_new_0.red_mod(cs.namespace(|| "reduce folded X[0]"), &m_bn)?;

        // Analyze X1 to bignat
        let X1_bn = BigNat::from_num(
            cs.namespace(|| "allocate X1_bn"),
            &Num::from(u.X1.clone()),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Fold self.X[1] + r * X[1]
        let (_, r_1) = X1_bn.mult_mod(cs.namespace(|| "r*X[1]"), &r_bn, &m_bn)?;
        // add X_r[1]
        let r_new_1 = self.X1.add(&r_1)?;
        // Now reduce
        let X1_fold = r_new_1.red_mod(cs.namespace(|| "reduce folded X[1]"), &m_bn)?;

        Ok(Self {
            W: W_fold,
            R: R_fold,
            E: E_fold,
            u: u_fold,
            X0: X0_fold,
            X1: X1_fold,
        })
    }

    pub fn sumcheck_verify<CS: ConstraintSystem<<E as Engine>::Base>>(
        mut cs: CS,
        mut ro: E::ROCircuit,
        degree_bound: usize,
        polys: &Vec<Vec<AllocatedNum<E::Base>>>,
        taus: &Vec<AllocatedNum<E::Base>>,
        evals: &Vec<AllocatedNum<E::Base>>,
        eval_e: AllocatedNum<E::Base>,
        u_u: AllocatedNum<E::Base>,
    ) -> Result<(), NovaError> {
        // --- sumcheck verification (mirrors the snippet provided) ---
        // number of rounds for the sumcheck (use same as taus length here)
        let num_rounds = taus.len();

        // verify the sumcheck proof (claim = 0, degree bound = 3)
        let mut r_vec_value: Vec<E::Base> = Vec::new(); // the challenge vector (values)
        let mut r_vec: Vec<AllocatedNum<E::Base>> = Vec::new(); // the challenge vector'
        let mut claim_finals = alloc_zero(cs.namespace(|| "claim_final"));

        // verify that there is a univariate polynomial for each round
        if polys.len() != num_rounds {
            return Err(NovaError::InvalidSumcheckProof);
        }

        let mut one = alloc_one(cs.namespace(|| format!("eq_one")));
        let mut eq_tau = alloc_zero(cs.namespace(|| format!("eq_tau")));

        for i in 0..polys.len() {
            // verify degree bound
            if polys[i].len() != degree_bound + 1 {
                return Err(NovaError::InvalidSumcheckProof);
            }

            // append the prover's message to the transcript
            for j in 0..polys[i].len() {
                ro.absorb(&polys[i][j]);
            }

            //derive the verifier's challenge for the next round
            let r_bits = ro.squeeze(cs.namespace(|| format!("r_{i} bits")), NUM_CHALLENGE_BITS)?;
            let r_i = le_bits_to_num(cs.namespace(|| format!("r_{i}")), &r_bits)?;

            // evaluate the claimed degree-ell polynomial at r_i
            let mut r_term = alloc_one(cs.namespace(|| format!("r_term_{i}")));
            for j in 0..polys[i].len() {
                let r_term_prev = r_term.clone();
                if j > 0 {
                    r_term =
                        AllocatedNum::alloc(cs.namespace(|| format!("r_term_{i}_{j}")), || {
                            Ok(*r_term_prev.get_value().get()? * r_i.get_value().get()?)
                        })?;
                    cs.enforce(
                        || format!("enforce r_term_update_{i}_{j}"),
                        |lc| lc + r_i.get_variable(),
                        |lc| lc + r_term_prev.get_variable(),
                        |lc| lc + r_term.get_variable(),
                    );
                }
                let claim_finals_prev = claim_finals.clone();
                claim_finals =
                    AllocatedNum::alloc(cs.namespace(|| format!("claim_final_{i}_{j}")), || {
                        Ok(*claim_finals_prev.get_value().get()?
                            + *r_term.get_value().get()? * polys[i][j].get_value().get()?)
                    })?;
                cs.enforce(
                    || format!("enforce claim_final_update_{i}_{j}"),
                    |lc| lc + r_term.get_variable(),
                    |lc| lc + polys[i][j].get_variable(),
                    |lc| lc + claim_finals.get_variable() - claim_finals_prev.get_variable(),
                );
            }

            // evaluate eq_tau on r_vec
            let eq_tau_prev = eq_tau.clone();
            let eq_tau_L = AllocatedNum::alloc(cs.namespace(|| format!("eq_tau_L_{i}")), || {
                Ok(*taus[i].get_value().get()? * r_i.get_value().get()?)
            })?;
            cs.enforce(
                || format!("enforce eq_tau_L_{i}"),
                |lc| lc + taus[i].get_variable(),
                |lc| lc + r_i.get_variable(),
                |lc| lc + eq_tau_L.get_variable(),
            );
            let eq_tau_R = AllocatedNum::alloc(cs.namespace(|| format!("eq_tau_R_{i}")), || {
                Ok((*one.get_value().get()? - taus[i].get_value().get()?)
                    * (*one.get_value().get()? - r_i.get_value().get()?))
            })?;
            cs.enforce(
                || format!("enforce eq_tau_R_{i}"),
                |lc| lc + one.get_variable() - taus[i].get_variable(),
                |lc| lc + one.get_variable() - r_i.get_variable(),
                |lc| lc + eq_tau_R.get_variable(),
            );
            eq_tau = AllocatedNum::alloc(cs.namespace(|| format!("eq_tau_{i}")), || {
                Ok(*eq_tau_prev.get_value().get()?
                    * (*eq_tau_L.get_value().get()? + eq_tau_R.get_value().get()?))
            })?;
            cs.enforce(
                || format!("enforce eq_tau_update_{i}"),
                |lc| lc + eq_tau_prev.get_variable(),
                |lc| lc + eq_tau_L.get_variable() + eq_tau_R.get_variable(),
                |lc| lc + eq_tau.get_variable(),
            );
        }

        let eval_ab = AllocatedNum::alloc(cs.namespace(|| format!("eval_ab")), || {
            Ok(*evals[0].get_value().get()? * evals[1].get_value().get()?)
        })?;
        cs.enforce(
            || format!("enforce eval_ab"),
            |lc| lc + evals[0].get_variable(),
            |lc| lc + evals[1].get_variable(),
            |lc| lc + eval_ab.get_variable(),
        );
        let eval_uc = AllocatedNum::alloc(cs.namespace(|| format!("eval_uc")), || {
            Ok(*u_u.get_value().get()? * evals[2].get_value().get()?)
        })?;
        cs.enforce(
            || format!("enforce eval_uc"),
            |lc| lc + u_u.get_variable(),
            |lc| lc + evals[2].get_variable(),
            |lc| lc + eval_uc.get_variable(),
        );
        let claim_final_expected =
            AllocatedNum::<E::Base>::alloc(cs.namespace(|| "claim_final_expected"), || {
                Ok(*eq_tau.get_value().get()?
                    * (*eval_ab.get_value().get()?
                        - eval_uc.get_value().get()?
                        - eval_e.get_value().get()?))
            })?;
        cs.enforce(
            || format!("enforce claim_final_expected"),
            |lc| lc + eq_tau.get_variable(),
            |lc| lc + eval_ab.get_variable() - eval_uc.get_variable() - eval_e.get_variable(),
            |lc| lc + claim_finals.get_variable(),
        );

        Ok(())
    }

    pub fn fold_with_r1cs_zkpcd<CS: ConstraintSystem<<E as Engine>::Base>>(
        &self,
        mut cs: CS,
        params: &AllocatedNum<E::Base>, // hash of R1CSShape of F'
        u: &AllocatedR1CSInstance<E>,
        T: &AllocatedPoint<E>,
        S: &AllocatedPoint<E>,
        compressed_polys: &Vec<Vec<AllocatedNum<E::Base>>>,
        taus: &Vec<AllocatedNum<E::Base>>,
        final_evals: &Vec<AllocatedNum<E::Base>>,
        deg: usize,
        ro_consts: ROConstantsCircuit<E>,
    ) -> Result<AllocatedRelaxedR1CSInstance<E>, SynthesisError> {
        // Compute r:
        let mut ro = E::ROCircuit::new(ro_consts);
        ro.absorb(params);

        // running instance `U` does not need to absorbed since u.X[0] = Hash(params, U, i, z0, zi)
        u.absorb_in_ro(&mut ro);

        ro.absorb(&T.x);
        ro.absorb(&T.y);
        ro.absorb(&T.is_infinity);
        ro.absorb(&S.x);
        ro.absorb(&S.y);
        ro.absorb(&S.is_infinity);

        let r_bits = ro.squeeze(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
        let r = le_bits_to_num(cs.namespace(|| "r"), &r_bits)?;

        // W_fold = self.W + r * u.W
        let rW = u.comm_W.scalar_mul(cs.namespace(|| "r * u.W"), &r_bits)?;
        let W_fold = self.W.add(cs.namespace(|| "self.W + r * u.W"), &rW)?;

        // R_fold = self.R + r*S + r^2*S + ... + r^{n-1}*S
        let rS = S.scalar_mul(cs.namespace(|| "r * S"), &r_bits)?;
        // let R_fold = self.R + r*S
        let mut R_fold = self.R.add(cs.namespace(|| "self.R + rS"), &rS)?;

        // Compute the Sumcheck Verification
        let mut eval_e = alloc_zero(cs.namespace(|| "zero"));
        let mut u_u = alloc_one(cs.namespace(|| "one"));
        Self::sumcheck_verify(
            &mut cs,
            ro,
            3,
            compressed_polys,
            taus,
            final_evals,
            eval_e,
            u_u,
        )
        .unwrap();

        // E_fold = self.E + r * T
        let rT = T.scalar_mul(cs.namespace(|| "r * T"), &r_bits)?;
        let E_fold = self.E.add(cs.namespace(|| "self.E + r * T"), &rT)?;

        // u_fold = u_r + r
        let u_fold = AllocatedNum::alloc(cs.namespace(|| "u_fold"), || {
            Ok(*self.u.get_value().get()? + r.get_value().get()?)
        })?;
        cs.enforce(
            || "Check u_fold",
            |lc| lc,
            |lc| lc,
            |lc| lc + u_fold.get_variable() - self.u.get_variable() - r.get_variable(),
        );

        // Fold the IO:
        // Analyze r into limbs
        let r_bn = BigNat::from_num(
            cs.namespace(|| "allocate r_bn"),
            &Num::from(r),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Allocate the order of the non-native field as a constant
        let m_bn = alloc_bignat_constant(
            cs.namespace(|| "alloc m"),
            &E::GE::group_params().2,
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Analyze X0 to bignat
        let X0_bn = BigNat::from_num(
            cs.namespace(|| "allocate X0_bn"),
            &Num::from(u.X0.clone()),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Fold self.X[0] + r * X[0]
        let (_, r_0) = X0_bn.mult_mod(cs.namespace(|| "r*X[0]"), &r_bn, &m_bn)?;
        // add X_r[0]
        let r_new_0 = self.X0.add(&r_0)?;
        // Now reduce
        let X0_fold = r_new_0.red_mod(cs.namespace(|| "reduce folded X[0]"), &m_bn)?;

        // Analyze X1 to bignat
        let X1_bn = BigNat::from_num(
            cs.namespace(|| "allocate X1_bn"),
            &Num::from(u.X1.clone()),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Fold self.X[1] + r * X[1]
        let (_, r_1) = X1_bn.mult_mod(cs.namespace(|| "r*X[1]"), &r_bn, &m_bn)?;
        // add X_r[1]
        let r_new_1 = self.X1.add(&r_1)?;
        // Now reduce
        let X1_fold = r_new_1.red_mod(cs.namespace(|| "reduce folded X[1]"), &m_bn)?;

        Ok(Self {
            W: W_fold,
            R: R_fold,
            E: E_fold,
            u: u_fold,
            X0: X0_fold,
            X1: X1_fold,
        })
    }

    pub fn fold_with_r1cs<CS: ConstraintSystem<<E as Engine>::Base>>(
        &self,
        mut cs: CS,
        params: &AllocatedNum<E::Base>, // hash of R1CSShape of F'
        u: &AllocatedR1CSInstance<E>,
        T: &AllocatedPoint<E>,
        S: &AllocatedPoint<E>,
        c: &Vec<Vec<AllocatedNum<E::Base>>>,
        deg: usize,
        ro_consts: ROConstantsCircuit<E>,
    ) -> Result<AllocatedRelaxedR1CSInstance<E>, SynthesisError> {
        // Compute r:
        let mut ro = E::ROCircuit::new(ro_consts);
        ro.absorb(params);

        // running instance `U` does not need to absorbed since u.X[0] = Hash(params, U, i, z0, zi)
        u.absorb_in_ro(&mut ro);

        ro.absorb(&T.x);
        ro.absorb(&T.y);
        ro.absorb(&T.is_infinity);
        ro.absorb(&S.x);
        ro.absorb(&S.y);
        ro.absorb(&S.is_infinity);

        let r_bits = ro.squeeze(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
        let r = le_bits_to_num(cs.namespace(|| "r"), &r_bits)?;

        // W_fold = self.W + r * u.W
        let rW = u.comm_W.scalar_mul(cs.namespace(|| "r * u.W"), &r_bits)?;
        let W_fold = self.W.add(cs.namespace(|| "self.W + r * u.W"), &rW)?;

        // R_fold = self.R + r*S + r^2*S + ... + r^{n-1}*S
        let deg = c[0].len();
        let rS = S.scalar_mul(cs.namespace(|| "r * S"), &r_bits)?;
        // let R_fold = self.R + r*S
        let mut R_fold = self.R.add(cs.namespace(|| "self.R + rS"), &rS)?;

        // E_fold = self.E + r * T
        let rT = T.scalar_mul(cs.namespace(|| "r * T"), &r_bits)?;
        let E_fold = self.E.add(cs.namespace(|| "self.E + r * T"), &rT)?;

        // u_fold = u_r + r
        let u_fold = AllocatedNum::alloc(cs.namespace(|| "u_fold"), || {
            Ok(*self.u.get_value().get()? + r.get_value().get()?)
        })?;
        cs.enforce(
            || "Check u_fold",
            |lc| lc,
            |lc| lc,
            |lc| lc + u_fold.get_variable() - self.u.get_variable() - r.get_variable(),
        );

        // Fold the IO:
        // Analyze r into limbs
        let r_bn = BigNat::from_num(
            cs.namespace(|| "allocate r_bn"),
            &Num::from(r),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Allocate the order of the non-native field as a constant
        let m_bn = alloc_bignat_constant(
            cs.namespace(|| "alloc m"),
            &E::GE::group_params().2,
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Analyze X0 to bignat
        let X0_bn = BigNat::from_num(
            cs.namespace(|| "allocate X0_bn"),
            &Num::from(u.X0.clone()),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Fold self.X[0] + r * X[0]
        let (_, r_0) = X0_bn.mult_mod(cs.namespace(|| "r*X[0]"), &r_bn, &m_bn)?;
        // add X_r[0]
        let r_new_0 = self.X0.add(&r_0)?;
        // Now reduce
        let X0_fold = r_new_0.red_mod(cs.namespace(|| "reduce folded X[0]"), &m_bn)?;

        // Analyze X1 to bignat
        let X1_bn = BigNat::from_num(
            cs.namespace(|| "allocate X1_bn"),
            &Num::from(u.X1.clone()),
            BN_LIMB_WIDTH,
            BN_N_LIMBS,
        )?;

        // Fold self.X[1] + r * X[1]
        let (_, r_1) = X1_bn.mult_mod(cs.namespace(|| "r*X[1]"), &r_bn, &m_bn)?;
        // add X_r[1]
        let r_new_1 = self.X1.add(&r_1)?;
        // Now reduce
        let X1_fold = r_new_1.red_mod(cs.namespace(|| "reduce folded X[1]"), &m_bn)?;

        Ok(Self {
            W: W_fold,
            R: R_fold,
            E: E_fold,
            u: u_fold,
            X0: X0_fold,
            X1: X1_fold,
        })
    }

    /// If the condition is true then returns this otherwise it returns the other
    pub fn conditionally_select<CS: ConstraintSystem<<E as Engine>::Base>>(
        &self,
        mut cs: CS,
        other: &AllocatedRelaxedR1CSInstance<E>,
        condition: &Boolean,
    ) -> Result<AllocatedRelaxedR1CSInstance<E>, SynthesisError> {
        let W = AllocatedPoint::conditionally_select(
            cs.namespace(|| "W = cond ? self.W : other.W"),
            &self.W,
            &other.W,
            condition,
        )?;

        let R = AllocatedPoint::conditionally_select(
            cs.namespace(|| "R = cond ? self.R : other.R"),
            &self.R,
            &other.R,
            condition,
        )?;

        let E = AllocatedPoint::conditionally_select(
            cs.namespace(|| "E = cond ? self.E : other.E"),
            &self.E,
            &other.E,
            condition,
        )?;

        let u = conditionally_select(
            cs.namespace(|| "u = cond ? self.u : other.u"),
            &self.u,
            &other.u,
            condition,
        )?;

        let X0 = conditionally_select_bignat(
            cs.namespace(|| "X[0] = cond ? self.X[0] : other.X[0]"),
            &self.X0,
            &other.X0,
            condition,
        )?;

        let X1 = conditionally_select_bignat(
            cs.namespace(|| "X[1] = cond ? self.X[1] : other.X[1]"),
            &self.X1,
            &other.X1,
            condition,
        )?;

        Ok(AllocatedRelaxedR1CSInstance { W, R, E, u, X0, X1 })
    }
}

pub fn sumcheck_prove<E: Engine>(
    n: usize,
) -> Result<(SumcheckProof<E>, Vec<E::Scalar>, Vec<E::Scalar>), NovaError> {
    // n must be > 0
    if n == 0 {
        return Err(NovaError::InvalidSumcheckProof);
    }

    // length = 2^n
    let len = 1usize
        .checked_shl(n as u32)
        .ok_or(NovaError::InvalidSumcheckProof)?;
    if len == 0 {
        return Err(NovaError::InvalidSumcheckProof);
    }

    // generate pseudorandom evals_a and evals_b from seed, evals_c = element-wise product
    let mut evals_a: Vec<E::Scalar> = Vec::with_capacity(len);
    let mut evals_b: Vec<E::Scalar> = Vec::with_capacity(len);
    let mut evals_c: Vec<E::Scalar> = Vec::with_capacity(len);

    for i in 0..len {
        let a = E::Scalar::random(&mut OsRng);
        let b = E::Scalar::random(&mut OsRng);
        let c = a * b;
        evals_a.push(a);
        evals_b.push(b);
        evals_c.push(c);
    }

    let mut taus: Vec<E::Scalar> = Vec::with_capacity(n);
    for j in 0..n {
        taus.push(E::Scalar::random(&mut OsRng));
    }

    let mut poly_a = MultilinearPolynomial::new(evals_a);
    let mut poly_b = MultilinearPolynomial::new(evals_b);
    let mut poly_c = MultilinearPolynomial::new(evals_c);

    let mut poly_abc = poly_a.clone().mul(poly_b.clone()).unwrap();
    poly_abc = poly_abc.sub(poly_c.clone()).unwrap();
    let claim = poly_abc.evaluate(&taus);

    let mut prover_transcript =
        <<E as Engine>::TE as TranscriptEngineTrait<E>>::new(b"sumcheck_test");
    let (proof, _r_vec, final_evals) = SumcheckProof::<E>::prove_cubic_with_three_inputs(
        &claim,
        taus.clone(),
        &mut poly_a,
        &mut poly_b,
        &mut poly_c,
        &mut prover_transcript,
    )
    .unwrap();

    Ok((proof, taus, final_evals))
}
