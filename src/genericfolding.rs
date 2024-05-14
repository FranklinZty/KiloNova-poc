use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_std::{One, Zero};
use std::ops::Add;

use subroutines::PolyIOP;
use transcript::IOPTranscript;

use crate::ccs::cccs::{Witness, CCCS};
use crate::ccs::ccs::CCS;
use crate::ccs::accs::ACCS;
use crate::ccs::pedersen::Commitment;
use crate::ccs::util::{compute_all_sum_Mz_evals, compute_all_sum_eqM_evals};
use crate::espresso::sum_check::structs::IOPProof as SumCheckProof;
use crate::espresso::sum_check::{verifier::interpolate_uni_poly, SumCheck};
use crate::espresso::virtual_polynomial::{eq_eval, VPAuxInfo, VirtualPolynomial};
use crate::util::hypercube::BooleanHypercube;

use std::marker::PhantomData;
use std::time::Instant;

/// Proof defines a multifolding proof
#[derive(Debug)]
pub struct Proof<C: CurveGroup> {
    pub sc_proof: SumCheckProof<C::ScalarField>,
    pub sigmas: Vec<Vec<C::ScalarField>>,
    pub taus: Vec<Vec<C::ScalarField>>,
}

#[derive(Debug)]
pub struct Genericfolding<C: CurveGroup> {
    pub _c: PhantomData<C>,
}

impl<C: CurveGroup> Genericfolding<C> {
    /// Compute the arrays of sigma_j and tau_j from step 5 corresponding to the ACCS and CCCS
    pub fn compute_sigmas_and_taus(
        ccs: &CCS<C>,
        z_accs: &[Vec<C::ScalarField>],
        z_cccs: &[Vec<C::ScalarField>],
        r_y: &Vec<C::ScalarField>,
        r_x_prime: &[C::ScalarField],
    ) -> (Vec<Vec<C::ScalarField>>, Vec<Vec<C::ScalarField>>) {
        // sigma_j = \sum_y eq(r_y, y) M(r_x', y) for accs
        let mut sigmas: Vec<Vec<C::ScalarField>> = Vec::new();
        for _ in z_accs {
            // sigmas
            let sigma_i = compute_all_sum_eqM_evals(&ccs.M, r_y, r_x_prime, ccs.s_prime);
            sigmas.push(sigma_i);
        }
        // tau_j = \sum_y M_j(r_x', y) z(y) for cccs
        let mut taus: Vec<Vec<C::ScalarField>> = Vec::new();
        for z_cccs_i in z_cccs {
            // taus
            let tau_i = compute_all_sum_Mz_evals(&ccs.M, z_cccs_i, r_x_prime, ccs.s_prime);
            taus.push(tau_i);
        }
        (sigmas, taus)
    }

    /// Compute the right-hand-side of step 5 of the multifolding scheme
    pub fn compute_c_from_sigmas_and_taus(
        ccs: &CCS<C>,
        vec_sigmas: &[Vec<C::ScalarField>],
        vec_taus: &[Vec<C::ScalarField>],
        gamma: C::ScalarField,
        alpha: &[C::ScalarField],
        vec_r_x: &Vec<Vec<C::ScalarField>>,
        r_x_prime: &[C::ScalarField],
    ) -> C::ScalarField {
        let mut c = C::ScalarField::zero();

        let mut e_accs = Vec::new();
        for r_x in vec_r_x {
            e_accs.push(eq_eval(r_x, r_x_prime).unwrap());
        }
        println!("mu: {:?}", vec_sigmas.len());
        for (i, sigmas) in vec_sigmas.iter().enumerate() {
            // (sum gamma^j * e_i * sigma_j)
            for (j, sigma_j) in sigmas.iter().enumerate() {
                let gamma_j = gamma.pow([(i * ccs.t + j) as u64]);
                c += gamma_j * e_accs[i] * sigma_j;
            }
        }

        let mu = vec_sigmas.len();
        let e2 = eq_eval(alpha, r_x_prime).unwrap();
        for (k, taus) in vec_taus.iter().enumerate() {
            // + gamma^{t+1} * e2 * sum c_i * prod theta_j
            let mut lhs = C::ScalarField::zero();
            for i in 0..ccs.q {
                let mut prod = C::ScalarField::one();
                for j in ccs.S[i].clone() {
                    prod *= taus[j];
                }
                lhs += ccs.c[i] * prod;
            }
            let gamma_t1 = gamma.pow([(mu * ccs.t + k) as u64]);
            c += gamma_t1 * e2 * lhs;
        }
        c
    }

    /// Compute f(x) polynomial for the given inputs.
    /// where f(x) = \sum_j gamma^j L_j(x) + gamma^t Q(x)
    pub fn compute_fx(
        running_instances: &[ACCS<C>],
        cccs_instances: &[CCCS<C>],
        z_cccs: &[Vec<C::ScalarField>],
        gamma: C::ScalarField,
        alpha: &[C::ScalarField],
    ) -> VirtualPolynomial<C::ScalarField> {
        let mu: usize = running_instances.len();
        // compute L(x) for all accs instances (amount: mu*t)
        let mut vec_Ls: Vec<VirtualPolynomial<C::ScalarField>> = Vec::new();
        for (_, running_instance) in running_instances.iter().enumerate() {
            let mut Ls = running_instance.compute_Ls();
            vec_Ls.append(&mut Ls);
        }
        // compute Q(x) for all cccs instances (amount: v)
        let mut vec_Q: Vec<VirtualPolynomial<C::ScalarField>> = Vec::new();
        for (i, cccs_instance) in cccs_instances.iter().enumerate() {
            let Q = cccs_instance.compute_Q(&z_cccs[i], alpha);
            vec_Q.push(Q);
        }
        let mut f = vec_Ls[0].clone();

        // note: the following two loops can be integrated in the previous two loops, but left
        // separated for clarity in the PoC implementation.
        // compute RLC of L_j(x) as \sum_j gamma^j L_j(x)
        for (j, L_j) in vec_Ls.iter_mut().enumerate().skip(1) {
            let gamma_j = gamma.pow([j as u64]);
            L_j.scalar_mul(&gamma_j);
            f = f.add(L_j);
        }
        // compute RLC of Q_j(x) as \sum_j gamma^{mu*t + j} Q_j(x)
        for (i, Q_i) in vec_Q.iter_mut().enumerate() {
            let gamma_mut_i = gamma.pow([(mu * cccs_instances[0].ccs.t + i) as u64]);
            Q_i.scalar_mul(&gamma_mut_i);
            f = f.add(Q_i);
        }
        f
    }

    /// Compute g(y) polynomial for the given inputs.
    pub fn compute_gy(
        running_instances: &[ACCS<C>],
        cccs_instances: &[CCCS<C>],
        z_accs: &[Vec<C::ScalarField>],
        z_cccs: &[Vec<C::ScalarField>],
        delta: C::ScalarField,
        r_x_prime: &[C::ScalarField],
    ) -> VirtualPolynomial<C::ScalarField> {
        let mu = running_instances.len();
        let mut vec_RS: Vec<VirtualPolynomial<C::ScalarField>> = Vec::new();
        for (i, running_instance) in running_instances.iter().enumerate() {
            let mut RS = running_instance.compute_R_S(r_x_prime, &z_accs[i]);
            vec_RS.append(&mut RS);
        }
        let mut vec_T: Vec<VirtualPolynomial<C::ScalarField>> = Vec::new();
        for (i, cccs_instance) in cccs_instances.iter().enumerate() {
            let mut T = cccs_instance.compute_T(r_x_prime, &z_cccs[i]);
            vec_T.append(&mut T);
        }
        let mut g = vec_RS[0].clone();

        // note: the following two loops can be integrated in the previous two loops, but left
        // separated for clarity in the PoC implementation.
        for (j, R_j) in vec_RS.iter_mut().enumerate().skip(1) {
            let gamma_j = delta.pow([j as u64]);
            R_j.scalar_mul(&gamma_j);
            g = g.add(R_j);
        }
        for (i, T_i) in vec_T.iter_mut().enumerate() {
            let gamma_mut_i = delta.pow([(mu * (cccs_instances[0].ccs.t+1) + i) as u64]);
            T_i.scalar_mul(&gamma_mut_i);
            g = g.add(T_i);
        }
        g
    }

    pub fn fold(
        accs: &[ACCS<C>],
        cccs: &[CCCS<C>],
        sigmas: &[Vec<C::ScalarField>],
        thetas: &[Vec<C::ScalarField>],
        r_x_prime: Vec<C::ScalarField>,
        r_y_prime: Vec<C::ScalarField>,
        rho: C::ScalarField,
    ) -> ACCS<C> {
        let mut C_folded = C::zero();
        let mut u_folded = C::ScalarField::zero();
        let mut x_folded: Vec<C::ScalarField> = vec![C::ScalarField::zero(); accs[0].x.len()];
        let mut v_folded: Vec<C::ScalarField> = vec![C::ScalarField::zero(); sigmas[0].len()];

        for i in 0..(accs.len() + cccs.len()) {
            let rho_i = rho.pow([i as u64]);

            let c: C;
            let u: C::ScalarField;
            let x: Vec<C::ScalarField>;
            let v: Vec<C::ScalarField>;
            if i < accs.len() {
                c = accs[i].C.0;
                u = accs[i].u;
                x = accs[i].x.clone();
                v = sigmas[i].clone();
            } else {
                c = cccs[i - accs.len()].C.0;
                u = C::ScalarField::one();
                x = cccs[i - accs.len()].x.clone();
                v = thetas[i - accs.len()].clone();
            }

            C_folded += c.mul(rho_i);
            u_folded += rho_i * u;
            x_folded = x_folded
                .iter()
                .zip(
                    x.iter()
                        .map(|x_i| *x_i * rho_i)
                        .collect::<Vec<C::ScalarField>>(),
                )
                .map(|(a_i, b_i)| *a_i + b_i)
                .collect();

            v_folded = v_folded
                .iter()
                .zip(
                    v.iter()
                        .map(|x_i| *x_i * rho_i)
                        .collect::<Vec<C::ScalarField>>(),
                )
                .map(|(a_i, b_i)| *a_i + b_i)
                .collect();
        }

        ACCS::<C> {
            C: Commitment(C_folded),
            ccs: accs[0].ccs.clone(),
            u: u_folded,
            x: x_folded,
            r_x: r_x_prime,
            r_y: r_y_prime,
            v: v_folded,
        }
    }

    pub fn fold_witness(
        w_accs: &[Witness<C::ScalarField>],
        w_cccs: &[Witness<C::ScalarField>],
        rho: C::ScalarField,
    ) -> Witness<C::ScalarField> {
        let mut w_folded: Vec<C::ScalarField> = vec![C::ScalarField::zero(); w_accs[0].w.len()];
        let mut r_w_folded = C::ScalarField::zero();

        for i in 0..(w_accs.len() + w_cccs.len()) {
            let rho_i = rho.pow([i as u64]);
            let w: Vec<C::ScalarField>;
            let r_w: C::ScalarField;

            if i < w_accs.len() {
                w = w_accs[i].w.clone();
                r_w = w_accs[i].r_w;
            } else {
                w = w_cccs[i - w_accs.len()].w.clone();
                r_w = w_cccs[i - w_accs.len()].r_w;
            }

            w_folded = w_folded
                .iter()
                .zip(
                    w.iter()
                        .map(|x_i| *x_i * rho_i)
                        .collect::<Vec<C::ScalarField>>(),
                )
                .map(|(a_i, b_i)| *a_i + b_i)
                .collect();

            r_w_folded += rho_i * r_w;
        }
        Witness {
            w: w_folded,
            r_w: r_w_folded,
        }
    }

    /// Perform the multifolding prover.
    ///
    /// Given μ accs instances and ν CCS instances, fold them into a single accs instance. Since
    /// this is the prover, also fold their witness.
    ///
    /// Return the final folded accs, the folded witness, the sumcheck proof, and the helper
    /// sumcheck claims sigmas and thetas.
    pub fn prove(
        transcript: &mut IOPTranscript<C::ScalarField>,
        running_instances: &[ACCS<C>],
        new_instances: &[CCCS<C>],
        w_accs: &[Witness<C::ScalarField>],
        w_cccs: &[Witness<C::ScalarField>],
    ) -> (Proof<C>, ACCS<C>, Witness<C::ScalarField>) {
        // TODO appends to transcript

        assert!(!running_instances.is_empty());
        assert!(!new_instances.is_empty());

        // construct the accs z vector from the relaxation factor, public IO and witness
        // XXX this deserves its own function in accs
        let mut z_accs = Vec::new();
        for (i, running_instance) in running_instances.iter().enumerate() {
            let z_1: Vec<C::ScalarField> = [
                vec![running_instance.u],
                running_instance.x.clone(),
                w_accs[i].w.to_vec(),
            ]
            .concat();
            z_accs.push(z_1);
        }
        // construct the CCCS z vector from the public IO and witness
        let mut z_cccs = Vec::new();
        for (i, new_instance) in new_instances.iter().enumerate() {
            let z_2: Vec<C::ScalarField> = [
                vec![C::ScalarField::one()],
                new_instance.x.clone(),
                w_cccs[i].w.to_vec(),
            ]
            .concat();
            z_cccs.push(z_2);
        }

        // Step 1: Get some challenges
        let gamma: C::ScalarField = transcript.get_and_append_challenge(b"gamma").unwrap();
        let alpha: Vec<C::ScalarField> = transcript
            .get_and_append_challenge_vectors(b"alpha", running_instances[0].ccs.s)
            .unwrap();

        // Compute g(x)
        let gx = Self::compute_fx(
            running_instances,
            new_instances,
            &z_cccs,
            gamma,
            &alpha,
        );

        // Step 3: Run the sumcheck prover
        let sumcheck_proof_x =
            <PolyIOP<C::ScalarField> as SumCheck<C::ScalarField>>::prove(&gx, transcript).unwrap(); // XXX unwrap

        // Note: The following two "sanity checks" are done for this prototype, in a final version
        // they should be removed.
        //
        // Sanity check 1: evaluate g(x) over x \in {0,1} (the boolean hypercube), and check that
        // its sum is equal to the extracted_sum from the SumCheck.
        // //////////////////////////////////////////////////////////////////////
        // let mut g_over_bhc = C::ScalarField::zero();
        // for x in BooleanHypercube::new(running_instances[0].ccs.s) {
        //     g_over_bhc += g.evaluate(&x).unwrap();
        // }

        // // note: this is the sum of g(x) over the whole boolean hypercube
        // let extracted_sum =
        //     <PolyIOP<C::ScalarField> as SumCheck<C::ScalarField>>::extract_sum(&sumcheck_proof);
        // assert_eq!(extracted_sum, g_over_bhc);
        // // Sanity check 2: expect \sum v_j * gamma^j to be equal to the sum of g(x) over the
        // // boolean hypercube (and also equal to the extracted_sum from the SumCheck).
        // let mut sum_v_j_gamma = C::ScalarField::zero();
        // for (i, running_instance) in running_instances.iter().enumerate() {
        //     for j in 0..running_instance.v.len() {
        //         let gamma_j = gamma.pow([(i * running_instances[0].ccs.t + j) as u64]);
        //         sum_v_j_gamma += running_instance.v[j] * gamma_j;
        //     }
        // }
        // assert_eq!(g_over_bhc, sum_v_j_gamma);
        // assert_eq!(extracted_sum, sum_v_j_gamma);
        // //////////////////////////////////////////////////////////////////////

        // Step 2: dig into the sumcheck and extract r_x_prime
        let r_x_prime = sumcheck_proof_x.point.clone();


        // Step 4: compute sigmas and thetas
        let (sigmas, taus) = Self::compute_sigmas_and_taus(
            &running_instances[0].ccs,
            &z_accs,
            &z_cccs,
            &running_instances[0].r_y,
            &r_x_prime,
        );

        // Compute g(y)
        let delta: C::ScalarField = transcript.get_and_append_challenge(b"delta").unwrap();

        let gy = Self::compute_gy(
            running_instances,
            new_instances,
            &z_accs,
            &z_cccs,
            delta,
            &r_x_prime,
        );

        // Step 3: Run the sumcheck prover
        let sumcheck_proof_y =
        <PolyIOP<C::ScalarField> as SumCheck<C::ScalarField>>::prove(&gy, transcript).unwrap(); // XXX unwrap

        // Step 2: dig into the sumcheck and extract r_x_prime
        let r_y_prime = sumcheck_proof_y.point.clone();
        
        // Step 6: Get the folding challenge
        let rho: C::ScalarField = transcript.get_and_append_challenge(b"rho").unwrap();

        // Step 7: Create the folded instance
        let folded_accs = Self::fold(
            running_instances,
            new_instances,
            &sigmas,
            &taus,
            r_x_prime,
            r_y_prime,
            rho,
        );

        // Step 8: Fold the witnesses
        let folded_witness = Self::fold_witness(w_accs, w_cccs, rho);

        (
            Proof::<C> {
                sc_proof: sumcheck_proof_x,
                sigmas,
                taus,
            },
            folded_accs,
            folded_witness,
        )
    }

    /// Perform the multifolding verifier:
    ///
    /// Given μ accs instances and ν CCS instances, fold them into a single accs instance.
    ///
    /// Return the folded accs instance.
    pub fn verify(
        transcript: &mut IOPTranscript<C::ScalarField>,
        running_instances: &[ACCS<C>],
        new_instances: &[CCCS<C>],
        proof: Proof<C>,
    ) -> ACCS<C> {
        // TODO appends to transcript

        assert!(!running_instances.is_empty());
        assert!(!new_instances.is_empty());

        // Step 1: Get some challenges
        let gamma: C::ScalarField = transcript.get_and_append_challenge(b"gamma").unwrap();
        let beta: Vec<C::ScalarField> = transcript
            .get_and_append_challenge_vectors(b"beta", running_instances[0].ccs.s)
            .unwrap();

        let vp_aux_info = VPAuxInfo::<C::ScalarField> {
            max_degree: running_instances[0].ccs.d + 1,
            num_variables: running_instances[0].ccs.s,
            phantom: PhantomData::<C::ScalarField>,
        };

        // Step 3: Start verifying the sumcheck
        // First, compute the expected sumcheck sum: \sum gamma^j v_j
        let mut sum_v_j_gamma = C::ScalarField::zero();
        for (i, running_instance) in running_instances.iter().enumerate() {
            for j in 0..running_instance.v.len() {
                let gamma_j = gamma.pow([(i * running_instances[0].ccs.t + j) as u64]);
                sum_v_j_gamma += running_instance.v[j] * gamma_j;
            }
        }

        // Verify the interactive part of the sumcheck
        let sumcheck_subclaim = <PolyIOP<C::ScalarField> as SumCheck<C::ScalarField>>::verify(
            sum_v_j_gamma,
            &proof.sc_proof,
            &vp_aux_info,
            transcript,
        )
        .unwrap();

        // Step 2: Dig into the sumcheck claim and extract the randomness used
        let r_x_prime = sumcheck_subclaim.point.clone();
        let r_y_prime = sumcheck_subclaim.point.clone();

        // Step 5: Finish verifying sumcheck (verify the claim c)
        let c = Self::compute_c_from_sigmas_and_taus(
            &new_instances[0].ccs,
            &proof.sigmas,
            &proof.taus,
            gamma,
            &beta,
            &running_instances
                .iter()
                .map(|accs| accs.r_x.clone())
                .collect(),
            &r_x_prime,
        );
        // check that the g(r_x') from the sumcheck proof is equal to the computed c from sigmas&thetas
        assert_eq!(c, sumcheck_subclaim.expected_evaluation);

        // Sanity check: we can also compute g(r_x') from the proof last evaluation value, and
        // should be equal to the previously obtained values.
        let g_on_rxprime_from_sumcheck_last_eval = interpolate_uni_poly::<C::ScalarField>(
            &proof.sc_proof.proofs.last().unwrap().evaluations,
            *r_x_prime.last().unwrap(),
        )
        .unwrap();
        assert_eq!(g_on_rxprime_from_sumcheck_last_eval, c);
        assert_eq!(
            g_on_rxprime_from_sumcheck_last_eval,
            sumcheck_subclaim.expected_evaluation
        );

        // Step 6: Get the folding challenge
        let rho: C::ScalarField = transcript.get_and_append_challenge(b"rho").unwrap();

        // Step 7: Compute the folded instance
        Self::fold(
            running_instances,
            new_instances,
            &proof.sigmas,
            &proof.taus,
            r_x_prime,
            r_y_prime,
            rho,
        )
    }
}

#[cfg(test)]
pub mod test {
    use super::*;
    use crate::ccs::ccs::test::{get_test_ccs, get_test_z};
    use ark_std::test_rng;
    use ark_std::UniformRand;

    use crate::ccs::pedersen::Pedersen;
    use ark_bls12_381::{Fr, G1Projective};

    const rnd : u32 = 1;
    // NIMFS: Non Interactive Multifolding Scheme
    type NIMFS = Genericfolding<G1Projective>;

    #[test]
    fn test_compute_sigmas_and_taus() -> () {
        let before = Instant::now();
        let mut ctr = 0;
        while ctr < rnd {
            let ccs = get_test_ccs();
            let z1 = get_test_z(3);
            let z2 = get_test_z(4);
            ccs.check_relation(&z1).unwrap();
            ccs.check_relation(&z2).unwrap();

            // run steps 1 and 2
            let mut rng = test_rng();
            let gamma: Fr = Fr::rand(&mut rng);
            let alpha: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
            let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

            // Initialize a multifolding object
            let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
            let (accs_instance, _) = ccs.to_accs(&mut rng, &pedersen_params, &z1);
            let (cccs_instance, _) = ccs.to_cccs(&mut rng, &pedersen_params, &z2);


            let (sigmas, taus) = NIMFS::compute_sigmas_and_taus(
                &accs_instance.ccs,
                &vec![z1.clone()],
                &vec![z2.clone()],
                &accs_instance.r_y,
                &r_x_prime,
            );

            let f = NIMFS::compute_fx(
                &vec![accs_instance.clone()],
                &vec![cccs_instance.clone()],
                &vec![z2.clone()],
                gamma,
                &alpha,
            );

            // we expect f(r_x_prime) to be equal to:
            // c = (sum gamma^j * e1 * sigma_j) + gamma^{t+1} * e2 * sum c_i * prod tau_j
            // from compute_c_from_sigmas_and_taus
            let expected_c = f.evaluate(&r_x_prime).unwrap();
            let c = NIMFS::compute_c_from_sigmas_and_taus(
                &ccs,
                &sigmas,
                &taus,
                gamma,
                &alpha,
                &vec![accs_instance.r_x],
                &r_x_prime,
            );
            assert_eq!(c, expected_c);
            ctr += 1;
        }
        println!("Elapsed time: {:.2?}", before.elapsed()/rnd);
    }

    #[test]
    fn test_compute_fx() -> () {
        let ccs = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        println!("z1: {:?}", z1);
        println!("z2: {:?}", z2);

        ccs.check_relation(&z1).unwrap();
        ccs.check_relation(&z2).unwrap();

        let mut rng = test_rng(); // TMP
        let gamma: Fr = Fr::rand(&mut rng);
        let alpha: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (accs_instance, _) = ccs.to_accs(&mut rng, &pedersen_params, &z1);
        let (cccs_instance, _) = ccs.to_cccs(&mut rng, &pedersen_params, &z2);

        // compute a vector v' = \sum_{y} eq(r_y, y) M(r_x, y) for testing f(x), specifically
        // v' = \sum_y eq(r_y, y) M(r_x, y) = \sum_x L_j(x)
        // 0 = \sum_x Q(x)
        let (test_vec_v, _) =  Genericfolding::<G1Projective>::compute_sigmas_and_taus(
            &ccs,
            &vec![z1.clone()],
            &vec![z2.clone()],
            &accs_instance.r_y,
            &accs_instance.r_x,
        );

        let mut sum_v_j_gamma = Fr::zero();
        for j in 0..test_vec_v[0].len() {
            let gamma_j = gamma.pow([j as u64]);
            sum_v_j_gamma += test_vec_v[0][j] * gamma_j; // test_vec_v only has one row for one accs instance
        }

        // Compute f(x) with that r_x
        let f = NIMFS::compute_fx(
            &vec![accs_instance.clone()],
            &vec![cccs_instance.clone()],
            &vec![z2.clone()],
            gamma,
            &alpha,
        );

        // evaluate f(x) over x \in {0,1}^s
        let mut f_on_bhc = Fr::zero();
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            f_on_bhc += f.evaluate(&x).unwrap();
        }

        // evaluate sum_{j \in [t]} (gamma^j * Lj(x)) over x \in {0,1}^s
        let mut sum_Lj_on_bhc = Fr::zero();
        let vec_L = accs_instance.compute_Ls();
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            for j in 0..vec_L.len() {
                let gamma_j = gamma.pow([j as u64]);
                sum_Lj_on_bhc += vec_L[j].evaluate(&x).unwrap() * gamma_j;
            }
        }

        // Q(x) over bhc is assumed to be zero, as checked in the test 'test_compute_Q'
        assert_ne!(f_on_bhc, Fr::zero());

        // evaluating g(x) over the boolean hypercube should give the same result as evaluating the
        // sum of gamma^j * Lj(x) over the boolean hypercube
        assert_eq!(f_on_bhc, sum_Lj_on_bhc);

        // evaluating g(x) over the boolean hypercube should give the same result as evaluating the
        // sum of gamma^j * v_j over j \in [t]
        assert_eq!(f_on_bhc, sum_v_j_gamma);
    }
    // TODO: run this test function

    #[test]
    fn test_fold() -> () {
        let ccs = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        ccs.check_relation(&z1).unwrap();
        ccs.check_relation(&z2).unwrap();

        let mut rng = test_rng();
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let r_y_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (running_instance, _) = ccs.to_accs(&mut rng, &pedersen_params, &z1);

        let (sigmas, taus) = Genericfolding::<G1Projective>::compute_sigmas_and_taus(
            &running_instance.ccs,
            &vec![z1.clone()],
            &vec![z2.clone()],
            &running_instance.r_y,
            &r_x_prime,
        );

        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, ccs.n - ccs.l - 1);

        let (accs, w1) = ccs.to_accs(&mut rng, &pedersen_params, &z1);
        let (cccs, w2) = ccs.to_cccs(&mut rng, &pedersen_params, &z2);

        accs.check_relation(&pedersen_params, &w1).unwrap();
        cccs.check_relation(&pedersen_params, &w2).unwrap();

        let mut rng = test_rng();
        let rho = Fr::rand(&mut rng);

        let folded = Genericfolding::<G1Projective>::fold(
            &vec![accs],
            &vec![cccs],
            &sigmas,
            &taus,
            r_x_prime,
            r_y_prime,
            rho,
        );

        let w_folded = Genericfolding::<G1Projective>::fold_witness(&vec![w1], &vec![w2], rho);

        // check accs relation
        folded.check_relation(&pedersen_params, &w_folded).unwrap();
    }

    /// Perform multifolding of an accs instance with a CCCS instance (as described in the paper)
    #[test]
    pub fn test_basic_multifolding() {
        let mut rng = test_rng();

        // Create a basic CCS circuit
        let ccs = get_test_ccs::<G1Projective>();
        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);

        // Generate a satisfying witness
        let z_1 = get_test_z(3);
        // Generate another satisfying witness
        let z_2 = get_test_z(4);

        // Create the accs instance out of z_1
        let (running_instance, w1) = ccs.to_accs(&mut rng, &pedersen_params, &z_1);
        // Create the CCCS instance out of z_2
        let (new_instance, w2) = ccs.to_cccs(&mut rng, &pedersen_params, &z_2);

        // Prover's transcript
        let mut transcript_p = IOPTranscript::<Fr>::new(b"multifolding");
        transcript_p.append_message(b"init", b"init").unwrap();

        // Run the prover side of the multifolding
        let (proof, folded_accs, folded_witness) = NIMFS::prove(
            &mut transcript_p,
            &vec![running_instance.clone()],
            &vec![new_instance.clone()],
            &vec![w1],
            &vec![w2],
        );

        // Verifier's transcript
        let mut transcript_v = IOPTranscript::<Fr>::new(b"multifolding");
        transcript_v.append_message(b"init", b"init").unwrap();

        // Run the verifier side of the multifolding
        let folded_accs_v = NIMFS::verify(
            &mut transcript_v,
            &vec![running_instance.clone()],
            &vec![new_instance.clone()],
            proof,
        );
        assert_eq!(folded_accs, folded_accs_v);

        // Check that the folded accs instance is a valid instance with respect to the folded witness
        folded_accs
            .check_relation(&pedersen_params, &folded_witness)
            .unwrap();
    }

    /// Perform multiple steps of multifolding of an accs instance with a CCCS instance
    #[test]
    pub fn test_multifolding_two_instances_multiple_steps() {
        let mut rng = test_rng();

        let ccs = get_test_ccs::<G1Projective>();

        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);

        // accs witness
        let z_1 = get_test_z(2);
        let (mut running_instance, mut w1) = ccs.to_accs(&mut rng, &pedersen_params, &z_1);

        let mut transcript_p = IOPTranscript::<Fr>::new(b"multifolding");
        let mut transcript_v = IOPTranscript::<Fr>::new(b"multifolding");
        transcript_p.append_message(b"init", b"init").unwrap();
        transcript_v.append_message(b"init", b"init").unwrap();

        let n: usize = 10;
        for i in 3..n {
            println!("\niteration: i {}", i); // DBG

            // CCS witness
            let z_2 = get_test_z(i);
            println!("z_2 {:?}", z_2); // DBG

            let (new_instance, w2) = ccs.to_cccs(&mut rng, &pedersen_params, &z_2);

            // run the prover side of the multifolding
            let (proof, folded_accs, folded_witness) = NIMFS::prove(
                &mut transcript_p,
                &vec![running_instance.clone()],
                &vec![new_instance.clone()],
                &vec![w1],
                &vec![w2],
            );

            // run the verifier side of the multifolding
            let folded_accs_v = NIMFS::verify(
                &mut transcript_v,
                &vec![running_instance.clone()],
                &vec![new_instance.clone()],
                proof,
            );

            assert_eq!(folded_accs, folded_accs_v);

            // check that the folded instance with the folded witness holds the accs relation
            println!("check_relation {}", i);
            folded_accs
                .check_relation(&pedersen_params, &folded_witness)
                .unwrap();

            running_instance = folded_accs;
            w1 = folded_witness;
        }
    }

    /// Test that generates mu>1 and nu>1 instances, and folds them in a single multifolding step.
    #[test]
    pub fn test_multifolding_mu_nu_instances() {
        let mut rng = test_rng();

        // Create a basic CCS circuit
        let ccs = get_test_ccs::<G1Projective>();
        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);

        let mu = 10;
        let nu = 15;

        // Generate a mu accs & nu CCCS satisfying witness
        let mut z_accs = Vec::new();
        for i in 0..mu {
            let z = get_test_z(i + 3);
            z_accs.push(z);
        }
        let mut z_cccs = Vec::new();
        for i in 0..nu {
            let z = get_test_z(nu + i + 3);
            z_cccs.push(z);
        }

        // Create the accs instances out of z_accs
        let mut accs_instances = Vec::new();
        let mut w_accs = Vec::new();
        for i in 0..mu {
            let (running_instance, w) = ccs.to_accs(&mut rng, &pedersen_params, &z_accs[i]);
            accs_instances.push(running_instance);
            w_accs.push(w);
        }
        // Create the CCCS instance out of z_cccs
        let mut cccs_instances = Vec::new();
        let mut w_cccs = Vec::new();
        for i in 0..nu {
            let (new_instance, w) = ccs.to_cccs(&mut rng, &pedersen_params, &z_cccs[i]);
            cccs_instances.push(new_instance);
            w_cccs.push(w);
        }

        // Prover's transcript
        let mut transcript_p = IOPTranscript::<Fr>::new(b"multifolding");
        transcript_p.append_message(b"init", b"init").unwrap();

        // Run the prover side of the multifolding
        let (proof, folded_accs, folded_witness) = NIMFS::prove(
            &mut transcript_p,
            &accs_instances,
            &cccs_instances,
            &w_accs,
            &w_cccs,
        );

        // Verifier's transcript
        let mut transcript_v = IOPTranscript::<Fr>::new(b"multifolding");
        transcript_v.append_message(b"init", b"init").unwrap();

        // Run the verifier side of the multifolding
        let folded_accs_v =
            NIMFS::verify(&mut transcript_v, &accs_instances, &cccs_instances, proof);
        assert_eq!(folded_accs, folded_accs_v);

        // Check that the folded accs instance is a valid instance with respect to the folded witness
        folded_accs
            .check_relation(&pedersen_params, &folded_witness)
            .unwrap();
    }

    /// Test that generates mu>1 and nu>1 instances, and folds them in a single multifolding step
    /// and repeats the process doing multiple steps.
    #[test]
    pub fn test_multifolding_mu_nu_instances_multiple_steps() {
        let before = Instant::now();
        let mut ctr = 0;
        let mut rng = test_rng();

        while ctr < rnd {
            // Create a basic CCS circuit
            let ccs = get_test_ccs::<G1Projective>();
            let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);

            // Prover's transcript
            let mut transcript_p = IOPTranscript::<Fr>::new(b"multifolding");
            transcript_p.append_message(b"init", b"init").unwrap();

            // Verifier's transcript
            let mut transcript_v = IOPTranscript::<Fr>::new(b"multifolding");
            transcript_v.append_message(b"init", b"init").unwrap();

            let n_steps = 3;

            // number of accs & CCCS instances in each multifolding step
            let mu = 10;
            let nu = 15;

            // Generate a mu accs & nu CCCS satisfying witness, for each step
            for step in 0..n_steps {
                let mut z_accs = Vec::new();
                for i in 0..mu {
                    let z = get_test_z(step + i + 3);
                    z_accs.push(z);
                }
                let mut z_cccs = Vec::new();
                for i in 0..nu {
                    let z = get_test_z(nu + i + 3);
                    z_cccs.push(z);
                }

                // Create the accs instances out of z_accs
                let mut accs_instances = Vec::new();
                let mut w_accs = Vec::new();
                for i in 0..mu {
                    let (running_instance, w) = ccs.to_accs(&mut rng, &pedersen_params, &z_accs[i]);
                    accs_instances.push(running_instance);
                    w_accs.push(w);
                }
                // Create the CCCS instance out of z_cccs
                let mut cccs_instances = Vec::new();
                let mut w_cccs = Vec::new();
                for i in 0..nu {
                    let (new_instance, w) = ccs.to_cccs(&mut rng, &pedersen_params, &z_cccs[i]);
                    cccs_instances.push(new_instance);
                    w_cccs.push(w);
                }

                // Run the prover side of the multifolding
                let (proof, folded_accs, folded_witness) = NIMFS::prove(
                    &mut transcript_p,
                    &accs_instances,
                    &cccs_instances,
                    &w_accs,
                    &w_cccs,
                );

                // Run the verifier side of the multifolding
                let folded_accs_v =
                    NIMFS::verify(&mut transcript_v, &accs_instances, &cccs_instances, proof);
                assert_eq!(folded_accs, folded_accs_v);

                // Check that the folded accs instance is a valid instance with respect to the folded witness
                folded_accs
                    .check_relation(&pedersen_params, &folded_witness)
                    .unwrap();
            }
            ctr += 1;
        }
        println!("Elapsed time: {:.2?}", before.elapsed()/rnd);
    }
}
