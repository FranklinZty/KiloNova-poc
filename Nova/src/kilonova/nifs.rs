//! Indexed Holographic Folding NIFS for the experimental `kilonova` path.
#![allow(non_snake_case)]
use crate::{
  constants::NUM_CHALLENGE_BITS,
  errors::NovaError,
  gadgets::utils::{base_as_scalar, scalar_as_base},
  r1cs::{R1CSInstance, R1CSWitness},
  traits::{AbsorbInROTrait, Engine, ROConstants, ROTrait},
  CommitmentKey,
};
use ff::Field;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

use super::{
  relation::{FoldedInstance, FoldedWitness, GlobalStructure},
  transcript::{absorb_tag, HFS_TAG_INPUT, HFS_TAG_X_CLAIMS, HFS_TAG_Y_CLAIMS},
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SumcheckProof<E: Engine> {
  pub(crate) point: Vec<E::Base>,
  pub(crate) polys: Vec<Vec<E::Base>>,
}

#[allow(clippy::upper_case_acronyms)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct NIFS<E: Engine> {
  pub(crate) sc_proof_x: SumcheckProof<E>,
  pub(crate) sc_proof_y: SumcheckProof<E>,
  pub(crate) sigmas: Vec<E::Base>,
  pub(crate) taus: Vec<E::Base>,
  pub(crate) epsilons: Vec<E::Base>,
  pub(crate) thetas: Vec<E::Base>,
}

impl<E: Engine> NIFS<E> {
  /// HFS transcript v1, input phase (docs/protocol-spec.md §3):
  /// `TAG_INPUT, pp_digest, predicate_id, U1 (running ACCS incl. iota' = comm_M), U2, iota`.
  /// Mirrored by `AllocatedFoldedInstance::fold_with_r1cs_holographic`.
  pub(crate) fn absorb_inputs(
    ro: &mut E::RO,
    pp_digest: &E::Scalar,
    predicate_id: usize,
    structure: &GlobalStructure<E>,
    U1: &FoldedInstance<E>,
    U2: &R1CSInstance<E>,
  ) {
    absorb_tag::<E>(ro, HFS_TAG_INPUT);
    ro.absorb(scalar_as_base::<E>(*pp_digest));
    ro.absorb(E::Base::from(predicate_id as u64));
    U1.absorb_in_ro(ro);
    U2.absorb_in_ro(ro);
    for comm in &structure.predicate_commitments(predicate_id) {
      comm.absorb_in_ro(ro);
    }
  }

  /// Binds the X-phase helper claims before `delta` is derived.
  pub(crate) fn absorb_x_claims(ro: &mut E::RO, sigmas: &[E::Base], taus: &[E::Base]) {
    absorb_tag::<E>(ro, HFS_TAG_X_CLAIMS);
    for v in sigmas.iter().chain(taus.iter()) {
      ro.absorb(*v);
    }
  }

  /// Binds the Y-phase helper claims before `rho` is derived.
  pub(crate) fn absorb_y_claims(ro: &mut E::RO, epsilons: &[E::Base], thetas: &[E::Base]) {
    absorb_tag::<E>(ro, HFS_TAG_Y_CLAIMS);
    for v in epsilons.iter().chain(thetas.iter()) {
      ro.absorb(*v);
    }
  }

  fn bind_table<F: Field>(table: &mut Vec<F>, r: F) {
    let half = table.len() / 2;
    for i in 0..half {
      table[i] = table[i] + r * (table[half + i] - table[i]);
    }
    table.truncate(half);
  }

  fn interpolate(points: &[E::Base], evals: &[E::Base], at: E::Base) -> Result<E::Base, NovaError> {
    if points.len() != evals.len() || points.is_empty() {
      return Err(NovaError::InvalidSumcheckProof);
    }

    let mut out = E::Base::ZERO;
    for (i, point_i) in points.iter().enumerate() {
      let mut num = E::Base::ONE;
      let mut den = E::Base::ONE;
      for (j, point_j) in points.iter().enumerate() {
        if i != j {
          num *= at - *point_j;
          den *= *point_i - *point_j;
        }
      }
      let den_inv = Option::<E::Base>::from(den.invert()).ok_or(NovaError::InvalidSumcheckProof)?;
      out += evals[i] * num * den_inv;
    }
    Ok(out)
  }

  fn powers(base: E::Base, count: usize) -> Vec<E::Base> {
    let mut cur = E::Base::ONE;
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
      out.push(cur);
      cur *= base;
    }
    out
  }

  fn canonical_point(point: &[E::Base]) -> Vec<E::Base> {
    point.iter().rev().copied().collect()
  }

  pub fn dummy(
    ro_consts: &ROConstants<E>,
    pp_digest: &E::Scalar,
    structure: &GlobalStructure<E>,
    predicate_id: usize,
    U2: &R1CSInstance<E>,
  ) -> Self {
    let zero_x_poly = vec![E::Base::ZERO; 4];
    let zero_y_poly = vec![E::Base::ZERO; 3];
    let mut ro = E::RO::new(ro_consts.clone());
    let U1 = FoldedInstance::default(structure);
    Self::absorb_inputs(&mut ro, pp_digest, predicate_id, structure, &U1, U2);

    let _gamma = ro.squeeze(NUM_CHALLENGE_BITS);
    let _alpha = (0..structure.s_max)
      .map(|_| ro.squeeze(NUM_CHALLENGE_BITS))
      .collect::<Vec<_>>();

    let mut point_x = Vec::with_capacity(structure.s_max);
    let polys_x = (0..structure.s_max)
      .map(|_| {
        for eval in &zero_x_poly {
          ro.absorb(*eval);
        }
        let r = ro.squeeze(NUM_CHALLENGE_BITS);
        point_x.push(r);
        zero_x_poly.clone()
      })
      .collect::<Vec<_>>();

    Self::absorb_x_claims(&mut ro, &[E::Base::ZERO; 3], &[E::Base::ZERO; 3]);
    let _delta = ro.squeeze(NUM_CHALLENGE_BITS);
    let mut point_y = Vec::with_capacity(structure.s_prime_max);
    let polys_y = (0..structure.s_prime_max)
      .map(|_| {
        for eval in &zero_y_poly {
          ro.absorb(*eval);
        }
        let r = ro.squeeze(NUM_CHALLENGE_BITS);
        point_y.push(r);
        zero_y_poly.clone()
      })
      .collect::<Vec<_>>();

    Self::absorb_y_claims(&mut ro, &[E::Base::ZERO; 4], &[E::Base::ZERO; 4]);
    let _rho = ro.squeeze(NUM_CHALLENGE_BITS);

    Self {
      sc_proof_x: SumcheckProof {
        point: point_x,
        polys: polys_x,
      },
      sc_proof_y: SumcheckProof {
        point: point_y,
        polys: polys_y,
      },
      sigmas: vec![E::Base::ZERO; 3],
      taus: vec![E::Base::ZERO; 3],
      epsilons: vec![E::Base::ZERO; 4],
      thetas: vec![E::Base::ZERO; 4],
    }
  }

  fn sumcheck_prove_x(
    ro: &mut E::RO,
    gamma: E::Base,
    alpha: &[E::Base],
    mut eq_rx: Vec<E::Base>,
    mut L0: Vec<E::Base>,
    mut L1: Vec<E::Base>,
    mut L2: Vec<E::Base>,
    mut eq_alpha: Vec<E::Base>,
    mut Az: Vec<E::Base>,
    mut Bz: Vec<E::Base>,
    mut Cz: Vec<E::Base>,
  ) -> SumcheckProof<E> {
    let gamma_pows = Self::powers(gamma, 4);
    let mut point = Vec::with_capacity(alpha.len());
    let mut polys = Vec::with_capacity(alpha.len());
    let eval_points = [
      E::Base::ZERO,
      E::Base::ONE,
      E::Base::from(2u64),
      E::Base::from(3u64),
    ];

    for _ in 0..alpha.len() {
      let half = L0.len() / 2;
      let evals = eval_points
        .iter()
        .map(|t| {
          (0..half)
            .into_par_iter()
            .map(|i| {
              let interp = |table: &Vec<E::Base>| table[i] + *t * (table[half + i] - table[i]);
              let l0 = interp(&L0);
              let l1 = interp(&L1);
              let l2 = interp(&L2);
              let eqx = interp(&eq_rx);
              let eq = interp(&eq_alpha);
              let az = interp(&Az);
              let bz = interp(&Bz);
              let cz = interp(&Cz);
              gamma_pows[0] * eqx * l0
                + gamma_pows[1] * eqx * l1
                + gamma_pows[2] * eqx * l2
                + gamma_pows[3] * eq * (az * bz - cz)
            })
            .reduce(|| E::Base::ZERO, |acc, x| acc + x)
        })
        .collect::<Vec<_>>();

      for eval in &evals {
        ro.absorb(*eval);
      }
      let r_i = ro.squeeze(NUM_CHALLENGE_BITS);
      point.push(r_i);
      polys.push(evals);

      Self::bind_table(&mut eq_rx, r_i);
      Self::bind_table(&mut L0, r_i);
      Self::bind_table(&mut L1, r_i);
      Self::bind_table(&mut L2, r_i);
      Self::bind_table(&mut eq_alpha, r_i);
      Self::bind_table(&mut Az, r_i);
      Self::bind_table(&mut Bz, r_i);
      Self::bind_table(&mut Cz, r_i);
    }

    SumcheckProof::<E> { point, polys }
  }

  fn sumcheck_prove_y(
    ro: &mut E::RO,
    delta: E::Base,
    mut eq_ry: Vec<E::Base>,
    mut R0: Vec<E::Base>,
    mut R1: Vec<E::Base>,
    mut R2: Vec<E::Base>,
    mut z_running: Vec<E::Base>,
    mut T0: Vec<E::Base>,
    mut T1: Vec<E::Base>,
    mut T2: Vec<E::Base>,
    mut z_new: Vec<E::Base>,
  ) -> SumcheckProof<E> {
    let delta_pows = Self::powers(delta, 7);
    let mut point = Vec::with_capacity(eq_ry.len().ilog2() as usize);
    let mut polys = Vec::with_capacity(eq_ry.len().ilog2() as usize);
    let eval_points = [E::Base::ZERO, E::Base::ONE, E::Base::from(2u64)];
    let rounds = eq_ry.len().ilog2() as usize;

    for _ in 0..rounds {
      let half = eq_ry.len() / 2;
      let evals = eval_points
        .iter()
        .map(|t| {
          (0..half)
            .into_par_iter()
            .map(|i| {
              let interp = |table: &Vec<E::Base>| table[i] + *t * (table[half + i] - table[i]);
              let eq = interp(&eq_ry);
              let r0 = interp(&R0);
              let r1 = interp(&R1);
              let r2 = interp(&R2);
              let zr = interp(&z_running);
              let t0 = interp(&T0);
              let t1 = interp(&T1);
              let t2 = interp(&T2);
              let zn = interp(&z_new);

              delta_pows[0] * eq * r0
                + delta_pows[1] * eq * r1
                + delta_pows[2] * eq * r2
                + delta_pows[3] * eq * zr
                + delta_pows[4] * t0 * zn
                + delta_pows[5] * t1 * zn
                + delta_pows[6] * t2 * zn
            })
            .reduce(|| E::Base::ZERO, |acc, x| acc + x)
        })
        .collect::<Vec<_>>();

      for eval in &evals {
        ro.absorb(*eval);
      }
      let r_i = ro.squeeze(NUM_CHALLENGE_BITS);
      point.push(r_i);
      polys.push(evals);

      Self::bind_table(&mut eq_ry, r_i);
      Self::bind_table(&mut R0, r_i);
      Self::bind_table(&mut R1, r_i);
      Self::bind_table(&mut R2, r_i);
      Self::bind_table(&mut z_running, r_i);
      Self::bind_table(&mut T0, r_i);
      Self::bind_table(&mut T1, r_i);
      Self::bind_table(&mut T2, r_i);
      Self::bind_table(&mut z_new, r_i);
    }

    SumcheckProof::<E> { point, polys }
  }

  fn sumcheck_verify(
    ro: &mut E::RO,
    mut claim: E::Base,
    proof: &SumcheckProof<E>,
    eval_points: &[E::Base],
  ) -> Result<(Vec<E::Base>, E::Base), NovaError> {
    if proof.point.len() != proof.polys.len() {
      return Err(NovaError::InvalidSumcheckProof);
    }

    let mut point = Vec::with_capacity(proof.point.len());
    for evals in &proof.polys {
      if evals.len() != eval_points.len() {
        return Err(NovaError::InvalidSumcheckProof);
      }
      if evals[0] + evals[1] != claim {
        return Err(NovaError::InvalidSumcheckProof);
      }

      for eval in evals {
        ro.absorb(*eval);
      }
      let r_i = ro.squeeze(NUM_CHALLENGE_BITS);
      claim = Self::interpolate(eval_points, evals, r_i)?;
      point.push(r_i);
    }

    if point != proof.point {
      return Err(NovaError::InvalidSumcheckProof);
    }

    Ok((point, claim))
  }

  fn eq_table(point: &[E::Base]) -> Vec<E::Base> {
    let size = 1usize << point.len();
    (0..size)
      .map(|idx| {
        GlobalStructure::<E>::eq_eval(&GlobalStructure::<E>::bits_le(idx, point.len()), point)
      })
      .collect()
  }

  fn row_table_eval_folded(
    structure: &GlobalStructure<E>,
    coeffs: &[E::Base],
    which: usize,
    r_y: &[E::Base],
  ) -> Vec<E::Base> {
    (0..(1usize << structure.s_max))
      .map(|row| {
        coeffs
          .iter()
          .enumerate()
          .map(|(predicate_id, coeff)| {
            *coeff
              * structure.predicates[predicate_id].row_buckets[which][row]
                .iter()
                .fold(E::Base::ZERO, |acc, (col, val)| {
                  acc
                    + *val
                      * GlobalStructure::<E>::eq_eval(
                        &GlobalStructure::<E>::bits_le(*col, structure.s_prime_max),
                        r_y,
                      )
                })
          })
          .sum()
      })
      .collect()
  }

  fn row_table_compressed_predicate(
    structure: &GlobalStructure<E>,
    predicate_id: usize,
    which: usize,
    z: &[E::Base],
  ) -> Vec<E::Base> {
    (0..(1usize << structure.s_max))
      .map(|row| {
        structure.predicates[predicate_id].row_buckets[which][row]
          .iter()
          .fold(E::Base::ZERO, |acc, (col, val)| {
            acc + *val * z.get(*col).copied().unwrap_or(E::Base::ZERO)
          })
      })
      .collect()
  }

  fn col_table_eval_folded(
    structure: &GlobalStructure<E>,
    coeffs: &[E::Base],
    which: usize,
    r_x: &[E::Base],
  ) -> Vec<E::Base> {
    (0..(1usize << structure.s_prime_max))
      .map(|col| {
        coeffs
          .iter()
          .enumerate()
          .map(|(predicate_id, coeff)| {
            *coeff
              * structure.predicates[predicate_id].col_buckets[which][col]
                .iter()
                .fold(E::Base::ZERO, |acc, (row, val)| {
                  acc
                    + *val
                      * GlobalStructure::<E>::eq_eval(
                        &GlobalStructure::<E>::bits_le(*row, structure.s_max),
                        r_x,
                      )
                })
          })
          .sum()
      })
      .collect()
  }

  fn col_table_eval_predicate(
    structure: &GlobalStructure<E>,
    predicate_id: usize,
    which: usize,
    r_x: &[E::Base],
  ) -> Vec<E::Base> {
    (0..(1usize << structure.s_prime_max))
      .map(|col| {
        structure.predicates[predicate_id].col_buckets[which][col]
          .iter()
          .fold(E::Base::ZERO, |acc, (row, val)| {
            acc
              + *val
                * GlobalStructure::<E>::eq_eval(
                  &GlobalStructure::<E>::bits_le(*row, structure.s_max),
                  r_x,
                )
          })
      })
      .collect()
  }

  fn z_table(structure: &GlobalStructure<E>, z: &[E::Base]) -> Vec<E::Base> {
    (0..(1usize << structure.s_prime_max))
      .map(|idx| z.get(idx).copied().unwrap_or(E::Base::ZERO))
      .collect()
  }

  pub fn prove(
    ck_witness: &CommitmentKey<E>,
    ro_consts: &ROConstants<E>,
    pp_digest: &E::Scalar,
    structure: &GlobalStructure<E>,
    predicate_id: usize,
    U1: &FoldedInstance<E>,
    W1: &FoldedWitness<E>,
    U2: &R1CSInstance<E>,
    W2: &R1CSWitness<E>,
  ) -> Result<(Self, (FoldedInstance<E>, FoldedWitness<E>)), NovaError> {
    if predicate_id >= structure.predicates.len() {
      return Err(NovaError::InvalidInputLength);
    }

    let z_running = structure.z_from_folded(U1, W1);
    let z_new = structure.z_from_r1cs(U2, W2);

    let mut ro = E::RO::new(ro_consts.clone());
    Self::absorb_inputs(&mut ro, pp_digest, predicate_id, structure, U1, U2);

    let gamma = ro.squeeze(NUM_CHALLENGE_BITS);
    let alpha = (0..structure.s_max)
      .map(|_| ro.squeeze(NUM_CHALLENGE_BITS))
      .collect::<Vec<_>>();

    let eq_alpha = Self::eq_table(&alpha);
    let eq_rx = Self::eq_table(&U1.r_x);
    let L0 = Self::row_table_eval_folded(structure, &W1.lambda_proj, 0, &U1.r_y);
    let L1 = Self::row_table_eval_folded(structure, &W1.lambda_proj, 1, &U1.r_y);
    let L2 = Self::row_table_eval_folded(structure, &W1.lambda_proj, 2, &U1.r_y);
    let Az = Self::row_table_compressed_predicate(structure, predicate_id, 0, &z_new);
    let Bz = Self::row_table_compressed_predicate(structure, predicate_id, 1, &z_new);
    let Cz = Self::row_table_compressed_predicate(structure, predicate_id, 2, &z_new);

    let sc_proof_x = Self::sumcheck_prove_x(
      &mut ro, gamma, &alpha, eq_rx, L0, L1, L2, eq_alpha, Az, Bz, Cz,
    );
    // Prover-side completeness check: the X sum-check must start from the running claim.
    // It fails exactly when the incoming R1CS instance does not satisfy the zero-check over
    // E::Base, which is the case for any instance using non-trivial E::Scalar arithmetic
    // (known issue B15: the HFS runs over E::Base while the R1CS is defined over E::Scalar).
    if let Some(first) = sc_proof_x.polys.first() {
      if first[0] + first[1] != structure.compute_sum_x(U1, gamma) {
        return Err(NovaError::UnSat {
          reason: "HFS zero-check failed: incoming instance is not satisfied over E::Base (B15)"
            .to_string(),
        });
      }
    }
    let r_x_prime = Self::canonical_point(&sc_proof_x.point);
    let sigmas = structure.compute_sigmas(W1, U1, &r_x_prime);
    let taus = structure.compute_taus(predicate_id, &r_x_prime, &z_new);

    Self::absorb_x_claims(&mut ro, &sigmas, &taus);
    let delta = ro.squeeze(NUM_CHALLENGE_BITS);
    let eq_ry = Self::eq_table(&U1.r_y);
    let R0 = Self::col_table_eval_folded(structure, &W1.lambda_proj, 0, &r_x_prime);
    let R1 = Self::col_table_eval_folded(structure, &W1.lambda_proj, 1, &r_x_prime);
    let R2 = Self::col_table_eval_folded(structure, &W1.lambda_proj, 2, &r_x_prime);
    let z_running_table = Self::z_table(structure, &z_running);
    let T0 = Self::col_table_eval_predicate(structure, predicate_id, 0, &r_x_prime);
    let T1 = Self::col_table_eval_predicate(structure, predicate_id, 1, &r_x_prime);
    let T2 = Self::col_table_eval_predicate(structure, predicate_id, 2, &r_x_prime);
    let z_new_table = Self::z_table(structure, &z_new);

    let sc_proof_y = Self::sumcheck_prove_y(
      &mut ro,
      delta,
      eq_ry,
      R0,
      R1,
      R2,
      z_running_table,
      T0,
      T1,
      T2,
      z_new_table,
    );
    let r_y_prime = Self::canonical_point(&sc_proof_y.point);
    let epsilons = structure.compute_epsilons(W1, U1, &z_running, &r_x_prime, &r_y_prime);
    let thetas = structure.compute_thetas(predicate_id, &z_new, &r_x_prime, &r_y_prime);

    Self::absorb_y_claims(&mut ro, &epsilons, &thetas);
    let rho_base = ro.squeeze(NUM_CHALLENGE_BITS);
    let rho_scalar = base_as_scalar::<E>(rho_base);
    let v = epsilons
      .iter()
      .zip(thetas.iter())
      .map(|(a, b)| *a + rho_base * *b)
      .collect::<Vec<_>>();
    let U = U1.fold(
      structure,
      predicate_id,
      U2,
      &rho_base,
      &rho_scalar,
      r_x_prime,
      r_y_prime,
      v,
    );
    let W = W1.fold(structure, predicate_id, W2, &rho_base, &rho_scalar)?;
    structure.is_sat(ck_witness, &U, &W)?;

    Ok((
      Self {
        sc_proof_x,
        sc_proof_y,
        sigmas,
        taus,
        epsilons,
        thetas,
      },
      (U, W),
    ))
  }

  pub fn verify(
    &self,
    ro_consts: &ROConstants<E>,
    pp_digest: &E::Scalar,
    structure: &GlobalStructure<E>,
    predicate_id: usize,
    U1: &FoldedInstance<E>,
    U2: &R1CSInstance<E>,
  ) -> Result<FoldedInstance<E>, NovaError> {
    if predicate_id >= structure.predicates.len() {
      return Err(NovaError::InvalidInputLength);
    }
    if self.sigmas.len() != 3
      || self.taus.len() != 3
      || self.epsilons.len() != 4
      || self.thetas.len() != 4
      || self.sc_proof_x.polys.len() != structure.s_max
      || self.sc_proof_y.polys.len() != structure.s_prime_max
    {
      return Err(NovaError::InvalidSumcheckProof);
    }

    if U1.X.len() != structure.num_io
      || U1.r_x.len() != structure.s_max
      || U1.r_y.len() != structure.s_prime_max
      || U1.v.len() != 4
    {
      return Err(NovaError::InvalidInputLength);
    }

    let mut ro = E::RO::new(ro_consts.clone());
    Self::absorb_inputs(&mut ro, pp_digest, predicate_id, structure, U1, U2);

    let gamma = ro.squeeze(NUM_CHALLENGE_BITS);
    let alpha = (0..structure.s_max)
      .map(|_| ro.squeeze(NUM_CHALLENGE_BITS))
      .collect::<Vec<_>>();

    let sum_x = structure.compute_sum_x(U1, gamma);
    let (r_x_prime_sumcheck, claim_x) = Self::sumcheck_verify(
      &mut ro,
      sum_x,
      &self.sc_proof_x,
      &[
        E::Base::ZERO,
        E::Base::ONE,
        E::Base::from(2u64),
        E::Base::from(3u64),
      ],
    )?;

    let r_x_prime = Self::canonical_point(&r_x_prime_sumcheck);
    let cx = structure.compute_cx(U1, &self.sigmas, &self.taus, gamma, &alpha, &r_x_prime);
    if claim_x != cx {
      return Err(NovaError::InvalidSumcheckProof);
    }

    Self::absorb_x_claims(&mut ro, &self.sigmas, &self.taus);
    let delta = ro.squeeze(NUM_CHALLENGE_BITS);
    let sum_y = structure.compute_sum_y(U1, &self.sigmas, &self.taus, delta);
    let (r_y_prime_sumcheck, claim_y) = Self::sumcheck_verify(
      &mut ro,
      sum_y,
      &self.sc_proof_y,
      &[E::Base::ZERO, E::Base::ONE, E::Base::from(2u64)],
    )?;

    let r_y_prime = Self::canonical_point(&r_y_prime_sumcheck);
    let cy = structure.compute_cy(U1, &self.epsilons, &self.thetas, delta, &r_y_prime);
    if claim_y != cy {
      return Err(NovaError::InvalidSumcheckProof);
    }

    Self::absorb_y_claims(&mut ro, &self.epsilons, &self.thetas);
    let rho_base = ro.squeeze(NUM_CHALLENGE_BITS);
    let rho_scalar = base_as_scalar::<E>(rho_base);
    let v = self
      .epsilons
      .iter()
      .zip(self.thetas.iter())
      .map(|(a, b)| *a + rho_base * *b)
      .collect::<Vec<_>>();
    Ok(U1.fold(
      structure,
      predicate_id,
      U2,
      &rho_base,
      &rho_scalar,
      r_x_prime,
      r_y_prime,
      v,
    ))
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    provider::PallasEngine,
    r1cs::SparseMatrix,
    traits::{commitment::CommitmentEngineTrait, snark::default_ck_hint, Engine},
  };

  fn tiny_r1cs<E: Engine>(
    scale: E::Scalar,
  ) -> (
    GlobalStructure<E>,
    CommitmentKey<E>,
    R1CSInstance<E>,
    R1CSWitness<E>,
    R1CSInstance<E>,
    R1CSWitness<E>,
  ) {
    let one = <E::Scalar as Field>::ONE;
    assert!(scale == one);
    let shape0 = crate::r1cs::R1CSShape::<E>::new(
      4,
      4,
      2,
      SparseMatrix::new(
        &[(0, 0, scale), (1, 1, one), (2, 2, one), (3, 3, one)],
        4,
        7,
      ),
      SparseMatrix::new(
        &[(0, 0, one), (1, 1, scale), (2, 2, one), (3, 3, one)],
        4,
        7,
      ),
      SparseMatrix::new(&[(0, 4, one), (1, 5, scale)], 4, 7),
    )
    .unwrap();
    let shape1 = crate::r1cs::R1CSShape::<E>::new(
      8,
      8,
      2,
      SparseMatrix::new(&[(0, 0, one), (1, 1, scale), (4, 4, one)], 8, 11),
      SparseMatrix::new(&[(0, 0, scale), (1, 1, one), (4, 4, one)], 8, 11),
      SparseMatrix::new(&[(0, 8, one), (1, 9, one)], 8, 11),
    )
    .unwrap();
    let ck = shape1.commitment_key(&*default_ck_hint());
    let structure = GlobalStructure::new(&[shape0.clone(), shape1.clone()]);
    let W0 = R1CSWitness::<E> {
      W: vec![one, one, E::Scalar::ZERO, E::Scalar::ZERO],
      r_W: E::Scalar::ZERO,
    };
    let U0 = R1CSInstance::<E> {
      comm_W: crate::CE::<E>::commit(&ck, &W0.W, &W0.r_W),
      X: vec![one, E::Scalar::ZERO],
    };
    let W1 = R1CSWitness::<E> {
      W: vec![
        one,
        one,
        E::Scalar::ZERO,
        E::Scalar::ZERO,
        E::Scalar::ZERO,
        E::Scalar::ZERO,
        E::Scalar::ZERO,
        E::Scalar::ZERO,
      ],
      r_W: E::Scalar::ZERO,
    };
    let U1 = R1CSInstance::<E> {
      comm_W: crate::CE::<E>::commit(&ck, &W1.W, &W1.r_W),
      X: vec![one, E::Scalar::ZERO],
    };
    (structure, ck, U0, W0, U1, W1)
  }

  #[test]
  fn test_nifs_roundtrip() {
    let (S, ck, U0, W0, U2, W2) = tiny_r1cs::<PallasEngine>(<PallasEngine as Engine>::Scalar::ONE);
    let U1 = super::super::relation::FoldedInstance::from_r1cs_instance_witness(&S, 0, &U0, &W0);
    let W1 = super::super::relation::FoldedWitness::from_r1cs_witness(&S, 0, &W0);
    let ro_consts = ROConstants::<PallasEngine>::default();
    let pp_digest = <PallasEngine as Engine>::Scalar::ZERO;
    let (nifs, (folded_u, folded_w)) =
      NIFS::prove(&ck, &ro_consts, &pp_digest, &S, 1, &U1, &W1, &U2, &W2).unwrap();
    let folded_u_v = nifs
      .verify(&ro_consts, &pp_digest, &S, 1, &U1, &U2)
      .unwrap();
    assert_eq!(folded_u, folded_u_v);
    assert!(S.is_sat(&ck, &folded_u, &folded_w).is_ok());
  }

  #[test]
  fn test_nifs_rejects_tampered_proof() {
    let (S, ck, U0, W0, U2, W2) = tiny_r1cs::<PallasEngine>(<PallasEngine as Engine>::Scalar::ONE);
    let U1 = super::super::relation::FoldedInstance::from_r1cs_instance_witness(&S, 0, &U0, &W0);
    let W1 = super::super::relation::FoldedWitness::from_r1cs_witness(&S, 0, &W0);
    let ro_consts = ROConstants::<PallasEngine>::default();
    let pp_digest = <PallasEngine as Engine>::Scalar::ZERO;
    let (mut nifs, _) =
      NIFS::prove(&ck, &ro_consts, &pp_digest, &S, 1, &U1, &W1, &U2, &W2).unwrap();
    nifs.sc_proof_x.polys[0][0] += <PallasEngine as Engine>::Base::ONE;
    assert!(nifs
      .verify(&ro_consts, &pp_digest, &S, 1, &U1, &U2)
      .is_err());
  }

  #[test]
  fn test_nifs_rejects_tampered_helper_claims() {
    let (S, ck, U0, W0, U2, W2) = tiny_r1cs::<PallasEngine>(<PallasEngine as Engine>::Scalar::ONE);
    let U1 = super::super::relation::FoldedInstance::from_r1cs_instance_witness(&S, 0, &U0, &W0);
    let W1 = super::super::relation::FoldedWitness::from_r1cs_witness(&S, 0, &W0);
    let ro_consts = ROConstants::<PallasEngine>::default();
    let pp_digest = <PallasEngine as Engine>::Scalar::ZERO;
    let (nifs, _) = NIFS::prove(&ck, &ro_consts, &pp_digest, &S, 1, &U1, &W1, &U2, &W2).unwrap();

    let mut tampered_sigma = nifs.clone();
    tampered_sigma.sigmas[0] += <PallasEngine as Engine>::Base::ONE;
    assert!(tampered_sigma
      .verify(&ro_consts, &pp_digest, &S, 1, &U1, &U2)
      .is_err());

    let mut tampered_tau = nifs.clone();
    tampered_tau.taus[0] += <PallasEngine as Engine>::Base::ONE;
    assert!(tampered_tau
      .verify(&ro_consts, &pp_digest, &S, 1, &U1, &U2)
      .is_err());

    let mut tampered_epsilon = nifs.clone();
    tampered_epsilon.epsilons[0] += <PallasEngine as Engine>::Base::ONE;
    assert!(tampered_epsilon
      .verify(&ro_consts, &pp_digest, &S, 1, &U1, &U2)
      .is_err());

    let mut tampered_theta = nifs;
    tampered_theta.thetas[0] += <PallasEngine as Engine>::Base::ONE;
    assert!(tampered_theta
      .verify(&ro_consts, &pp_digest, &S, 1, &U1, &U2)
      .is_err());
  }

  /// B4: the running instance U1 (including its index commitment iota' = comm_M) is bound
  /// by the transcript, so a proof made for one running instance is rejected for another.
  #[test]
  fn test_nifs_rejects_substituted_running_instance() {
    let (S, ck, U0, W0, U2, W2) = tiny_r1cs::<PallasEngine>(<PallasEngine as Engine>::Scalar::ONE);
    let U1 = super::super::relation::FoldedInstance::from_r1cs_instance_witness(&S, 0, &U0, &W0);
    let W1 = super::super::relation::FoldedWitness::from_r1cs_witness(&S, 0, &W0);
    let ro_consts = ROConstants::<PallasEngine>::default();
    let pp_digest = <PallasEngine as Engine>::Scalar::ZERO;
    let (nifs, _) = NIFS::prove(&ck, &ro_consts, &pp_digest, &S, 1, &U1, &W1, &U2, &W2).unwrap();

    let mut other_x = U1.clone();
    other_x.X[0] += <PallasEngine as Engine>::Base::ONE;
    assert!(nifs
      .verify(&ro_consts, &pp_digest, &S, 1, &other_x, &U2)
      .is_err());

    let mut other_index = U1.clone();
    other_index.comm_M = S.predicate_commitments(1);
    assert!(nifs
      .verify(&ro_consts, &pp_digest, &S, 1, &other_index, &U2)
      .is_err());

    let mut other_comm_w = U1.clone();
    other_comm_w.comm_W = U1.comm_W + U1.comm_W;
    assert!(nifs
      .verify(&ro_consts, &pp_digest, &S, 1, &other_comm_w, &U2)
      .is_err());
  }

  /// B16: epsilon/theta are absorbed before rho. Changing (epsilon_0, theta_0) jointly so
  /// that the final Y check c_y still holds must change rho (or be rejected); otherwise a
  /// prover could choose the claims after seeing rho.
  #[test]
  fn test_nifs_rho_binds_y_claims() {
    let (S, ck, U0, W0, U2, W2) = tiny_r1cs::<PallasEngine>(<PallasEngine as Engine>::Scalar::ONE);
    let U1 = super::super::relation::FoldedInstance::from_r1cs_instance_witness(&S, 0, &U0, &W0);
    let W1 = super::super::relation::FoldedWitness::from_r1cs_witness(&S, 0, &W0);
    let ro_consts = ROConstants::<PallasEngine>::default();
    let pp_digest = <PallasEngine as Engine>::Scalar::ZERO;
    let (nifs, (folded_u, _)) =
      NIFS::prove(&ck, &ro_consts, &pp_digest, &S, 1, &U1, &W1, &U2, &W2).unwrap();

    // Recover delta and r_y' exactly as the verifier does.
    let mut ro = <PallasEngine as Engine>::RO::new(ro_consts.clone());
    NIFS::<PallasEngine>::absorb_inputs(&mut ro, &pp_digest, 1, &S, &U1, &U2);
    let _gamma = ro.squeeze(NUM_CHALLENGE_BITS);
    for _ in 0..S.s_max {
      let _ = ro.squeeze(NUM_CHALLENGE_BITS);
    }
    for poly in &nifs.sc_proof_x.polys {
      for e in poly {
        ro.absorb(*e);
      }
      let _ = ro.squeeze(NUM_CHALLENGE_BITS);
    }
    NIFS::<PallasEngine>::absorb_x_claims(&mut ro, &nifs.sigmas, &nifs.taus);
    let delta = ro.squeeze(NUM_CHALLENGE_BITS);
    let r_y_prime = NIFS::<PallasEngine>::canonical_point(&nifs.sc_proof_y.point);
    let eq_ry = U1.r_y.iter().zip(r_y_prime.iter()).fold(
      <PallasEngine as Engine>::Base::ONE,
      |acc, (a, b)| {
        acc
          * (*a * *b
            + (<PallasEngine as Engine>::Base::ONE - *a)
              * (<PallasEngine as Engine>::Base::ONE - *b))
      },
    );

    // c_y contains eq_ry * epsilon_0 + delta^4 * theta_0 * theta_3; keep it invariant.
    let d_theta = <PallasEngine as Engine>::Base::from(5u64);
    let d_eps = -(delta.pow_vartime([4]) * nifs.thetas[3] * d_theta)
      * Option::<<PallasEngine as Engine>::Base>::from(eq_ry.invert()).unwrap();
    let mut forged = nifs.clone();
    forged.epsilons[0] += d_eps;
    forged.thetas[0] += d_theta;

    // Before the B16 fix rho did not depend on (epsilon, theta), so the forged proof was
    // accepted with the *same* rho. Now rho (hence u = u1 + rho) must change.
    match forged.verify(&ro_consts, &pp_digest, &S, 1, &U1, &U2) {
      Err(_) => {}
      Ok(u) => assert_ne!(u.u, folded_u.u, "rho does not bind epsilon/theta"),
    }
  }

  /// Known issue B15 (regression evidence for **v1**): this v1 HFS runs over `E::Base` on
  /// projected witnesses, while the R1CS is defined over `E::Scalar`. An R1CS instance that is
  /// satisfied over `E::Scalar` but uses a negative coefficient (here `(w0 - w1) * 1 = 0`) and
  /// a wrapping product (`w0 * w0 = x0`) cannot be folded.
  ///
  /// Status: **fixed** for native folding in P3 (`hfs::tests::test_b15_instance_class_folds_in_v2`
  /// folds this exact shape over `E::Scalar`) and for recursion in P5 (`kilonova::ivc`, HFS v2
  /// with CycleFold; `ivc::tests::test_ivc_v2_nonuniform_*` run the v1 traces that are ignored
  /// here). This test is deliberately **not** flipped: it pins the behaviour of the frozen v1
  /// code (`nifs.rs`, `RecursiveSNARK` v1), which is kept unmodified as historical evidence.
  /// Delete it together with the v1 path.
  #[test]
  fn test_known_issue_b15_scalar_r1cs_not_foldable_over_base() {
    type E = PallasEngine;
    type F = <E as Engine>::Scalar;
    let one = F::ONE;
    let shape = crate::r1cs::R1CSShape::<E>::new(
      2,
      2,
      2,
      SparseMatrix::new(&[(0, 0, one), (0, 1, -one), (1, 0, one)], 2, 5),
      SparseMatrix::new(&[(0, 2, one), (1, 0, one)], 2, 5),
      SparseMatrix::new(&[(1, 3, one)], 2, 5),
    )
    .unwrap();
    let ck = shape.commitment_key(&*default_ck_hint());
    let x = F::from(1u64 << 63).pow_vartime([4]) + F::from(7u64);
    let W = R1CSWitness::<E> {
      W: vec![x, x],
      r_W: F::ZERO,
    };
    let U = R1CSInstance::<E> {
      comm_W: crate::CE::<E>::commit(&ck, &W.W, &W.r_W),
      X: vec![x * x, F::ZERO],
    };
    // Satisfied over E::Scalar ...
    assert!(shape.is_sat(&ck, &U, &W).is_ok());

    // ... but the holographic fold over E::Base rejects it.
    let S = GlobalStructure::new(&[shape]);
    let U1 = super::super::relation::FoldedInstance::from_r1cs_instance_witness(&S, 0, &U, &W);
    let W1 = super::super::relation::FoldedWitness::from_r1cs_witness(&S, 0, &W);
    let ro_consts = ROConstants::<E>::default();
    let res = NIFS::prove(&ck, &ro_consts, &F::ZERO, &S, 0, &U1, &W1, &U, &W);
    assert!(
      res.is_err(),
      "B15 appears fixed in the v1 path: update this test and docs/baseline-status.md"
    );
  }
}
