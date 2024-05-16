use ark_ec::CurveGroup;
use ark_poly::DenseMultilinearExtension;
use ark_std::One;
use std::sync::Arc;
use crate::espresso::multilinear_polynomial::{fix_variables, fix_last_variables};

use ark_std::{rand::Rng, UniformRand};

use crate::ccs::cccs::Witness;
use crate::ccs::ccs::{CCSError, CCS};
use crate::ccs::util::{compute_all_sum_M_and_z_evals, compute_sum_eqM};

use crate::ccs::pedersen::{Commitment, Params as PedersenParams, Pedersen};
use crate::espresso::virtual_polynomial::VirtualPolynomial;
use crate::util::mle::matrix_to_mle;
use crate::util::mle::vec_to_mle;

/// Atomic CCS instance
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ACCS<C: CurveGroup> {
    // Underlying CCS structure
    pub ccs: CCS<C>,

    // TODO: Further improve the abstractions here. We should not need so many public fields

    // Commitment to witness
    pub C: Commitment<C>,
    // Relaxation factor of z for folded accs
    pub u: C::ScalarField,
    // Public input/output
    pub x: Vec<C::ScalarField>,
    // Random evaluation point for the v_i
    pub r_x: Vec<C::ScalarField>,
    // Random evaluation point for the v_i
    pub r_y: Vec<C::ScalarField>,
    // Vector of v_i
    pub v: Vec<C::ScalarField>,
}

impl<C: CurveGroup> CCS<C> {
    /// Compute v_j values of the linearized committed CCS form
    /// Given `r`, compute:  \sum_{y \in {0,1}^s'} M_j(r, y) * z(y)
    pub fn compute_v_j_accs(&self, z: &[C::ScalarField], r_x: &[C::ScalarField], r_y: &[C::ScalarField]) -> Vec<C::ScalarField> {
        // compute_all_sum_Mz_evals(&self.M, &z.to_vec(), r_x, self.s_prime)
        compute_all_sum_M_and_z_evals(&self.M, &z.to_vec(), r_x, r_y, self.s_prime)
    }

    pub fn to_accs<R: Rng>(
        &self,
        rng: &mut R,
        pedersen_params: &PedersenParams<C>,
        z: &[C::ScalarField],
    ) -> (ACCS<C>, Witness<C::ScalarField>) {
        let w: Vec<C::ScalarField> = z[(1 + self.l)..].to_vec();
        let r_w = C::ScalarField::rand(rng);
        let C = Pedersen::commit(pedersen_params, &w, &r_w);

        let r_x: Vec<C::ScalarField> = (0..self.s).map(|_| C::ScalarField::rand(rng)).collect();
        let r_y: Vec<C::ScalarField> = (0..self.s_prime).map(|_| C::ScalarField::rand(rng)).collect();
        let v = self.compute_v_j_accs(z, &r_x, &r_y);

        (
            ACCS::<C> {
                ccs: self.clone(),
                C,
                u: C::ScalarField::one(),
                x: z[1..(1 + self.l)].to_vec(),
                r_x,
                r_y,
                v,
            },
            Witness::<C::ScalarField> { w, r_w },
        )
    }
}

impl<C: CurveGroup> ACCS<C> {
    /// Compute all L_j(x) polynomials
    pub fn compute_Ls(&self) -> Vec<VirtualPolynomial<C::ScalarField>> {
        // Convert all matrices to MLE
        let M_x_y_mle: Vec<DenseMultilinearExtension<C::ScalarField>> =
            self.ccs.M.clone().into_iter().map(matrix_to_mle).collect();

        let mut vec_L_j_x = Vec::with_capacity(self.ccs.t);
        
        for M_j in M_x_y_mle {
            // compute \sum_{y} eq(r_y, y) M(x,y)
            let sum_M_y: DenseMultilinearExtension<_> = compute_sum_eqM(M_j, &self.r_y, self.ccs.s_prime);

            let sum_M_y_virtual =
                VirtualPolynomial::new_from_mle(&Arc::new(sum_M_y.clone()), C::ScalarField::one());
            let L_j_x = sum_M_y_virtual.build_f_hat(&self.r_x).unwrap();

            vec_L_j_x.push(L_j_x);
        }
        vec_L_j_x
    }

    /// Compute all R_j(y) and S(y)
    pub fn compute_R_S(&self, r_x_prime: &[C::ScalarField], z: &Vec<C::ScalarField>) -> Vec<VirtualPolynomial<C::ScalarField>> {
        // Convert all matrices to MLE
        let M_x_y_mle: Vec<DenseMultilinearExtension<C::ScalarField>> =
        self.ccs.M.clone().into_iter().map(matrix_to_mle).collect();

        let mut vec_RS_j_y = Vec::with_capacity(self.ccs.t+1);

        for M_j in M_x_y_mle {
            let M_j_x: DenseMultilinearExtension<C::ScalarField> = fix_last_variables(&M_j, &r_x_prime);
            let M_j_x_virtual: VirtualPolynomial<_> =
                VirtualPolynomial::new_from_mle(&Arc::new(M_j_x.clone()), C::ScalarField::one());
            let R_j_y = M_j_x_virtual.build_f_hat(&self.r_y).unwrap();
            vec_RS_j_y.push(R_j_y);
        }
        let z_y = vec_to_mle(self.ccs.s_prime, z);
        let z_y_virtual = VirtualPolynomial::new_from_mle(&Arc::new(z_y.clone()), C::ScalarField::one());
        let S_y = z_y_virtual.build_f_hat(&self.r_y).unwrap();
        vec_RS_j_y.push(S_y);
        vec_RS_j_y
    }

    /// Perform the check of the ACCS instance described at section 4.2
    pub fn check_relation(
        &self,
        pedersen_params: &PedersenParams<C>,
        w: &Witness<C::ScalarField>,
    ) -> Result<(), CCSError> {
        // check that C is the commitment of w. Notice that this is not verifying a Pedersen
        // opening, but checking that the Commmitment comes from committing to the witness.
        assert_eq!(self.C.0, Pedersen::commit(pedersen_params, &w.w, &w.r_w).0);

        // check ACCS relation
        let z: Vec<C::ScalarField> = [vec![self.u], self.x.clone(), w.w.to_vec()].concat();
        let computed_v = self.ccs.compute_v_j_accs( &z, &self.r_x, &self.r_y);
        assert_eq!(computed_v, self.v);
        Ok(())
    }
}

#[cfg(test)]
pub mod test {

    use super::*;
    use ark_std::Zero;

    use crate::ccs::ccs::test::{get_test_ccs, get_test_z};
    use crate::util::hypercube::BooleanHypercube;
    use ark_std::test_rng;

    use ark_bls12_381::{Fr, G1Projective};

    #[test]
    /// Test atomic CCS v_j against the L_j(x)
    fn test_accs_v_j() -> () {
        let mut rng = test_rng();

        let ccs: CCS<ark_ec::short_weierstrass::Projective<ark_bls12_381::g1::Config>> = get_test_ccs::<G1Projective>();
        let z = get_test_z(3);
        ccs.check_relation(&z.clone()).unwrap();

        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, ccs.n - ccs.l - 1); // |io| - |w| - 1
        let (accs, _) = ccs.to_accs(&mut rng, &pedersen_params, &z);
        // with our test vector comming from R1CS, v should have length 4
        assert_eq!(accs.v.len(), 4); // matrices A,B,C and z

        // check that \sum_x L_j_x = M_j(r_x,r_y)
        let vec_L_j_x = accs.compute_Ls();
        // let M_x_y_mle: Vec<DenseMultilinearExtension<Fr>> = ccs.M.iter().cloned().map(matrix_to_mle).collect();
        // for j in 0..ccs.t {
        //     // sanity check: sum_x L_j_x should equal M_j(r_x, r_y)
        //     let M_j_y: DenseMultilinearExtension<Fr> = fix_variables(&M_x_y_mle[j], &accs.r_y);
        //     let M_j_xy = fix_variables(&M_j_y, &accs.r_x);
            
        //     let mut sum_L_j_x = Fr::zero(); 
        //     let bhc = BooleanHypercube::new(ccs.s);
        //     for y in bhc.into_iter() {
        //         let L_j_x_eval = vec_L_j_x[j].evaluate(&y).unwrap();
        //         sum_L_j_x = sum_L_j_x + L_j_x_eval;
        //     }
        //     println!("M_j_xy: {:?}", M_j_xy.evaluations[0]);
        //     println!("sum_L_j_x: {:?}", sum_L_j_x);
        // }

        for (v_i, L_j_x) in accs.v.into_iter().skip(1).zip(vec_L_j_x) {
            let sum_L_j_x = BooleanHypercube::new(ccs.s)
                .into_iter()
                .map(|x| L_j_x.evaluate(&x).unwrap())
                .fold(Fr::zero(), |acc, result| acc + result);
            assert_eq!(v_i, sum_L_j_x);
        }
    }

    /// Given a bad z, check that the v_j should not match with the L_j(x)
    #[test]
    fn test_bad_v_j() -> () {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z.clone()).unwrap();

        // Mutate z so that the relation does not hold
        let mut bad_z = z.clone();
        bad_z[3] = Fr::zero();
        assert!(ccs.check_relation(&bad_z.clone()).is_err());

        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, ccs.n - ccs.l - 1);
        // Compute v_j with the right z
        let (accs, _) = ccs.to_accs(&mut rng, &pedersen_params, &z);
        // with our test vector comming from R1CS, v should have length 3
        assert_eq!(accs.v.len(), 3);

        // Bad compute L_j(x) with the bad z
        let vec_L_j_x = accs.compute_Ls();
        assert_eq!(vec_L_j_x.len(), accs.v.len());

        // // Make sure that the accs is not satisfied given these L_j(x)
        // // i.e. summing L_j(x) over the hypercube should not give v_j for all j
        // let mut satisfied = true;
        // for (v_i, L_j_x) in accs.v.into_iter().zip(vec_L_j_x) {
        //     let sum_L_j_x = BooleanHypercube::new(ccs.s)
        //         .into_iter()
        //         .map(|y| L_j_x.evaluate(&y).unwrap())
        //         .fold(Fr::zero(), |acc, result| acc + result);
        //     if v_i != sum_L_j_x {
        //         satisfied = false;
        //     }
        // }

        // assert_eq!(satisfied, false);
    }
}
