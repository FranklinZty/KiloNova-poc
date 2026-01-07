//! This module implements various gadgets necessary for folding R1CS types.

use std::ops::{Mul, Sub};
use nova_snark::{
    constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_CHALLENGE_BITS},
    frontend::{num::AllocatedNum, Assignment, Boolean, ConstraintSystem, SynthesisError},
    traits::{commitment::CommitmentTrait, Engine, Group, ROCircuitTrait, ROConstantsCircuit},
    r1cs::{R1CSInstance, RelaxedR1CSInstance},
    gadgets::{
        ecc::AllocatedPoint,
        nonnative::{
            bignat::BigNat,
            util::{f_to_nat, Num},
        },
        utils::{
            alloc_bignat_constant, alloc_zero, alloc_one, alloc_scalar_as_base, conditionally_select,
            conditionally_select_bignat, le_bits_to_num,
        },
    },
    spartan::{
        sumcheck::*,
        polys::multilinear::MultilinearPolynomial,
        polys::eq::EqPolynomial,
    }
};
use ff::Field;
use num_traits::pow;
use nova_snark::errors::NovaError;
use nova_snark::traits::TranscriptEngineTrait;

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
        let u = alloc_scalar_as_base::<E, _>(cs.namespace(|| "allocate u"), inst.map(|inst| inst.u))?;

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
        c: &Vec<Vec<AllocatedNum<E::Base>>>,
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
        if deg > 1 {
            let mut r_power_S = rS;
            // For loop for computing r^2*S, r^3*S, ..., r^{n-1}*S
            for i in 2..pow(2,deg) {
                // compute the next r^i * S
                r_power_S = r_power_S.scalar_mul(cs.namespace(|| format!("r^{} * S", i)), &r_bits)?;
                // accumulate to R_fold
                R_fold = R_fold.add(cs.namespace(|| format!("R_fold + r^{}*S", i)), &r_power_S)?;
            }
        }

        // Compute the Sumcheck Verification
        let mut c_fold = alloc_zero(cs.namespace(|| "zero"));
        let mut one = alloc_one(cs.namespace(||  format!("one")));;
        for i in 0..c.len() {
            let r_bits_i = ro.squeeze(cs.namespace(|| format!("r bits^{i}")), NUM_CHALLENGE_BITS)?;
            let r_i = le_bits_to_num(cs.namespace(|| format!("r^{i}")), &r_bits_i)?;
            let mut basis = alloc_one(cs.namespace(||  format!("basis^{i}_one")));;
            for (j, c_ij) in c[i].iter().enumerate() {
                let r_i_c_ij = AllocatedNum::alloc(cs.namespace(|| format!("r^{i} - c^{i}^{j}")), || {
                    Ok(*r_i.get_value().get()? * c_ij.get_value().get()?)
                })?;
                cs.enforce(
                    || format!("enforce r^{i} - c^{i}^{j} = r_i_c_{i}_{j}"),
                    |lc| lc + r_i.get_variable() - c_ij.get_variable(),
                    |lc| lc,
                    |lc| lc + r_i_c_ij.get_variable(),
                );
                // compute the inversion of r_i_c_ij
                let r_i_c_ij_inv = AllocatedNum::alloc(cs.namespace(|| format!("r_{i}_c_ij_inv_{j}")), || {
                    Ok(r_i_c_ij.get_value().get()?.invert().unwrap_or(E::Base::ZERO))
                })?;
                // enforce r_i_c * r_i_c_inv = 1
                cs.enforce(
                    || format!("enforce inv_{i}_{j}"),
                    |lc| lc + r_i_c_ij.get_variable(),
                    |lc| lc + r_i_c_ij_inv.get_variable(),
                    |lc| lc + one.get_variable(),
                );
                let prev_basis = basis.clone();
                basis = AllocatedNum::alloc(cs.namespace(|| format!("basis * (r^{i} - c^{i}^{j})")), || {
                    Ok(*basis.get_value().get()? * r_i_c_ij_inv.get_value().get()?)
                })?;
                cs.enforce(
                    || format!("enforce basis_update_{i}_{j}"),
                    |lc| lc + prev_basis.get_variable(),
                    |lc| lc + r_i_c_ij_inv.get_variable(),
                    |lc| lc + basis.get_variable(),
                );
            }
            for j in 0..c[i].len() {
                let basis_inv = AllocatedNum::alloc(cs.namespace(|| format!("basis_inv^{i}^{j}")), || {
                    Ok(basis.get_value().get()?.invert().unwrap_or(E::Base::ZERO))
                })?;
                cs.enforce(
                    || format!("enforce basis inv_{i}_{j}"),
                    |lc| lc + basis.get_variable(),
                    |lc| lc + basis_inv.get_variable(),
                    |lc| lc + one.get_variable(),
                );
                // compute c[i][j]/basis
                let c_ij = AllocatedNum::alloc(cs.namespace(|| format!("c^{i}^{j} * basis_inv")), || {
                    Ok(*c[i][j].get_value().get()? * basis_inv.get_value().get()?)
                })?;
                cs.enforce(
                    || format!("enforce c_{i}_{j} = c[i][j] * basis_inv"),
                    |lc| lc + c[i][j].get_variable(),
                    |lc| lc + basis_inv.get_variable(),
                    |lc| lc + c_ij.get_variable(),
                );

                // accumulate to c_fold
                let c_fold_prev = c_fold.clone();
                c_fold = AllocatedNum::alloc(cs.namespace(|| format!("c_fold + c^{i}^{j}")), || {
                    Ok(*c_fold.get_value().get()? + c_ij.get_value().get()?)
                })?;
                cs.enforce(
                    || format!("enforce c_fold_update_{i}_{j}"),
                    |lc| lc + c_fold_prev.get_variable(),
                    |lc| lc + c_ij.get_variable(),
                    |lc| lc + c_fold.get_variable(),
                );
                ro.absorb(&c[i][j]);
            }
        }

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

    pub fn sumcheck_cubic_three_inputs() -> Result<(), NovaError> {

        let evals_a = vec![
            E::Scalar::from(1u64), // x=(0,0)
            E::Scalar::from(3u64), // x=(1,0)
            E::Scalar::from(5u64), // x=(0,1)
            E::Scalar::from(7u64), // x=(1,1)
        ];
        let evals_b = vec![
            E::Scalar::from(2u64),
            E::Scalar::from(4u64),
            E::Scalar::from(6u64),
            E::Scalar::from(8u64),
        ];
        let evals_c = vec![
            E::Scalar::from(2u64),
            E::Scalar::from(12u64),
            E::Scalar::from(30u64),
            E::Scalar::from(56u64),
        ];

        let mut poly_a = MultilinearPolynomial::new(evals_a);
        let mut poly_b = MultilinearPolynomial::new(evals_b);
        let mut poly_c = MultilinearPolynomial::new(evals_c);

        let taus: Vec<E::Scalar> = vec![
            E::Scalar::from(1u64),
            E::Scalar::from(2u64),
        ];

        let mut poly_abc = poly_a.clone().mul(poly_b.clone()).unwrap();
        poly_abc = poly_abc.sub(poly_c.clone()).unwrap();
        let claim = poly_abc.evaluate(&taus);

        let mut prover_transcript = <<E as Engine>::TE as TranscriptEngineTrait<E>>::new(b"sumcheck_test");
        let (proof, _r_vec, final_evals) = SumcheckProof::<E>::prove_cubic_with_three_inputs(
            &claim,
            taus.clone(),
            &mut poly_a,
            &mut poly_b,
            &mut poly_c,
            &mut prover_transcript,
        )?;

        // construct verifier transcript using fully-qualified associated type to avoid ambiguity
        let mut verifier_transcript = <<E as Engine>::TE as TranscriptEngineTrait<E>>::new(b"sumcheck_test");

        // --- sumcheck verification (mirrors the snippet provided) ---
        // number of rounds for the sumcheck (use same as taus length here)
        let num_rounds = taus.len();

        let tau = EqPolynomial::new(taus);

        // verify the sumcheck proof (claim = 0, degree bound = 3)
        let (claim_finals, r_vec) = proof.verify(E::Scalar::ZERO, num_rounds, 3, &mut verifier_transcript)?;

        // derive expected claim from the proven inner claims
        let (claim_a, claim_b, claim_c) = (final_evals[0], final_evals[1], final_evals[2]);
        let eval_E = E::Scalar::ZERO; // in this test we don't have an extra E term
        let u_u = E::Scalar::ONE; // treat U.u as 1 for this simple test

        let taus_bound = tau.evaluate(&r_vec);
        let claim_final_expected =
            taus_bound * (claim_a * claim_b - u_u * claim_c - eval_E);

        if claim_finals != claim_final_expected {

            return Err(NovaError::InvalidSumcheckProof);
        }

        println!("Execute Sumcheck.");
        Ok(())
    }
    // TODO: separate the prove and verify
    // TODO: write the constraints for verify part

    pub fn fold_with_r1cs_zkpcd<CS: ConstraintSystem<<E as Engine>::Base>>(
        &self,
        mut cs: CS,
        params: &AllocatedNum<E::Base>, // hash of R1CSShape of F'
        u: &AllocatedR1CSInstance<E>,
        T: &AllocatedPoint<E>,
        S: &AllocatedPoint<E>,
        c: &Vec<Vec<AllocatedNum<E::Base>>>,
        ro_consts: ROConstantsCircuit<E>,
    ) -> Result<AllocatedRelaxedR1CSInstance<E>, SynthesisError> {
        Self::sumcheck_cubic_three_inputs().unwrap();

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
        // if deg > 1 {
        //     let mut r_power_S = rS;
        //     // For loop for computing r^2*S, r^3*S, ..., r^{n-1}*S
        //     for i in 2..pow(2,deg) {
        //         // compute the next r^i * S
        //         r_power_S = r_power_S.scalar_mul(cs.namespace(|| format!("r^{} * S", i)), &r_bits)?;
        //         // accumulate to R_fold
        //         R_fold = R_fold.add(cs.namespace(|| format!("R_fold + r^{}*S", i)), &r_power_S)?;
        //     }
        // }

        // Compute the Sumcheck Verification
        let mut c_fold = alloc_zero(cs.namespace(|| "zero"));
        let mut one = alloc_one(cs.namespace(||  format!("one")));;
        for i in 0..c.len() {
            let r_bits_i = ro.squeeze(cs.namespace(|| format!("r bits^{i}")), NUM_CHALLENGE_BITS)?;
            let r_i = le_bits_to_num(cs.namespace(|| format!("r^{i}")), &r_bits_i)?;
            let mut basis = alloc_one(cs.namespace(||  format!("basis^{i}_one")));;
            for (j, c_ij) in c[i].iter().enumerate() {
                let r_i_c_ij = AllocatedNum::alloc(cs.namespace(|| format!("r^{i} - c^{i}^{j}")), || {
                    Ok(*r_i.get_value().get()? * c_ij.get_value().get()?)
                })?;
                cs.enforce(
                    || format!("enforce r^{i} - c^{i}^{j} = r_i_c_{i}_{j}"),
                    |lc| lc + r_i.get_variable() - c_ij.get_variable(),
                    |lc| lc,
                    |lc| lc + r_i_c_ij.get_variable(),
                );
                // compute the inversion of r_i_c_ij
                let r_i_c_ij_inv = AllocatedNum::alloc(cs.namespace(|| format!("r_{i}_c_ij_inv_{j}")), || {
                    Ok(r_i_c_ij.get_value().get()?.invert().unwrap_or(E::Base::ZERO))
                })?;
                // enforce r_i_c * r_i_c_inv = 1
                cs.enforce(
                    || format!("enforce inv_{i}_{j}"),
                    |lc| lc + r_i_c_ij.get_variable(),
                    |lc| lc + r_i_c_ij_inv.get_variable(),
                    |lc| lc + one.get_variable(),
                );
                let prev_basis = basis.clone();
                basis = AllocatedNum::alloc(cs.namespace(|| format!("basis * (r^{i} - c^{i}^{j})")), || {
                    Ok(*basis.get_value().get()? * r_i_c_ij_inv.get_value().get()?)
                })?;
                cs.enforce(
                    || format!("enforce basis_update_{i}_{j}"),
                    |lc| lc + prev_basis.get_variable(),
                    |lc| lc + r_i_c_ij_inv.get_variable(),
                    |lc| lc + basis.get_variable(),
                );
            }
            for j in 0..c[i].len() {
                let basis_inv = AllocatedNum::alloc(cs.namespace(|| format!("basis_inv^{i}^{j}")), || {
                    Ok(basis.get_value().get()?.invert().unwrap_or(E::Base::ZERO))
                })?;
                cs.enforce(
                    || format!("enforce basis inv_{i}_{j}"),
                    |lc| lc + basis.get_variable(),
                    |lc| lc + basis_inv.get_variable(),
                    |lc| lc + one.get_variable(),
                );
                // compute c[i][j]/basis
                let c_ij = AllocatedNum::alloc(cs.namespace(|| format!("c^{i}^{j} * basis_inv")), || {
                    Ok(*c[i][j].get_value().get()? * basis_inv.get_value().get()?)
                })?;
                cs.enforce(
                    || format!("enforce c_{i}_{j} = c[i][j] * basis_inv"),
                    |lc| lc + c[i][j].get_variable(),
                    |lc| lc + basis_inv.get_variable(),
                    |lc| lc + c_ij.get_variable(),
                );

                // accumulate to c_fold
                let c_fold_prev = c_fold.clone();
                c_fold = AllocatedNum::alloc(cs.namespace(|| format!("c_fold + c^{i}^{j}")), || {
                    Ok(*c_fold.get_value().get()? + c_ij.get_value().get()?)
                })?;
                cs.enforce(
                    || format!("enforce c_fold_update_{i}_{j}"),
                    |lc| lc + c_fold_prev.get_variable(),
                    |lc| lc + c_ij.get_variable(),
                    |lc| lc + c_fold.get_variable(),
                );
                ro.absorb(&c[i][j]);
            }
        }

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
