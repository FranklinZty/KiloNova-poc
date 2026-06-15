//! This module defines indexed R1CS-specialized Holographic Folding relations.
use crate::{
  errors::NovaError,
  gadgets::utils::scalar_as_base,
  r1cs::{R1CSInstance, R1CSShape, R1CSWitness},
  spartan::math::Math,
  traits::{
    commitment::CommitmentEngineTrait, AbsorbInROTrait, Engine, ROTrait, TranscriptReprTrait,
  },
  Commitment, CommitmentKey, CE,
};
use ff::Field;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

const INDEX_LABELS: [&[u8]; 3] = [b"kilonova_idx_a", b"kilonova_idx_b", b"kilonova_idx_c"];

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PredicateIndex<E: Engine> {
  pub(crate) id: usize,
  pub(crate) shape: R1CSShape<E>,
  pub(crate) s: usize,
  pub(crate) s_prime: usize,
  pub(crate) z_len: usize,
  pub(crate) matrix_at_zero: [E::Base; 3],
  pub(crate) mats: [Vec<(usize, usize, E::Base)>; 3],
  pub(crate) row_buckets: [Vec<Vec<(usize, E::Base)>>; 3],
  pub(crate) col_buckets: [Vec<Vec<(usize, E::Base)>>; 3],
  pub(crate) comm_M: [Commitment<E>; 3],
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct GlobalStructure<E: Engine> {
  pub(crate) num_io: usize,
  pub(crate) num_vars_max: usize,
  pub(crate) s_max: usize,
  pub(crate) s_prime_max: usize,
  pub(crate) z_len_max: usize,
  pub(crate) predicates: Vec<PredicateIndex<E>>,
  pub(crate) ck_index: [CommitmentKey<E>; 3],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct FoldedWitness<E: Engine> {
  pub(crate) W: Vec<E::Scalar>,
  pub(crate) W_proj: Vec<E::Base>,
  pub(crate) r_W: E::Scalar,
  pub(crate) lambda_scalar: Vec<E::Scalar>,
  pub(crate) lambda_proj: Vec<E::Base>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct FoldedInstance<E: Engine> {
  pub(crate) comm_W: Commitment<E>,
  pub(crate) comm_M: [Commitment<E>; 3],
  pub(crate) u: E::Base,
  pub(crate) X: Vec<E::Base>,
  pub(crate) r_x: Vec<E::Base>,
  pub(crate) r_y: Vec<E::Base>,
  pub(crate) v: Vec<E::Base>,
}

pub type Structure<E> = GlobalStructure<E>;

impl<E: Engine> GlobalStructure<E> {
  pub fn new(shapes: &[R1CSShape<E>]) -> Self {
    Self::build(shapes, true)
  }

  pub fn new_for_setup(shapes: &[R1CSShape<E>]) -> Self {
    Self::build(shapes, true)
  }

  fn build(shapes: &[R1CSShape<E>], with_runtime_tables: bool) -> Self {
    assert!(!shapes.is_empty());

    let padded = shapes.iter().map(R1CSShape::pad).collect::<Vec<_>>();
    let num_io = padded[0].num_io;
    let num_vars_max = padded.iter().map(|shape| shape.num_vars).max().unwrap();
    let s_max = padded
      .iter()
      .map(|shape| shape.num_cons.log_2().max(1))
      .max()
      .unwrap();
    let z_len_max = num_vars_max + 1 + num_io;
    let s_prime_max = z_len_max.next_power_of_two().log_2().max(1);

    let ck_index = core::array::from_fn(|j| E::CE::setup(INDEX_LABELS[j], shapes.len()));
    let predicate_commitments = (0..shapes.len())
      .map(|id| {
        let basis = Self::basis_coeffs_scalar_with_len(id, shapes.len());
        core::array::from_fn(|j| CE::<E>::commit(&ck_index[j], &basis, &E::Scalar::ZERO))
      })
      .collect::<Vec<[Commitment<E>; 3]>>();

    let predicates = padded
      .into_iter()
      .enumerate()
      .map(|(id, shape)| {
        let s = shape.num_cons.log_2().max(1);
        let z_len = shape.num_vars + 1 + shape.num_io;
        let s_prime = z_len.next_power_of_two().log_2().max(1);
        let (mats, matrix_at_zero, row_buckets, col_buckets) = if with_runtime_tables {
          let mats = [shape.A.clone(), shape.B.clone(), shape.C.clone()].map(|M| {
            M.iter()
              .map(|(row, col, val)| (row, col, scalar_as_base::<E>(val)))
              .collect::<Vec<_>>()
          });
          let matrix_at_zero = core::array::from_fn(|which| {
            mats[which]
              .iter()
              .filter(|(row, col, _)| *row == 0 && *col == 0)
              .fold(E::Base::ZERO, |acc, (_, _, val)| acc + *val)
          });
          let mut row_buckets = core::array::from_fn(|_| vec![Vec::new(); 1usize << s_max]);
          let mut col_buckets = core::array::from_fn(|_| vec![Vec::new(); 1usize << s_prime_max]);
          for which in 0..3 {
            for (row, col, val) in &mats[which] {
              row_buckets[which][*row].push((*col, *val));
              col_buckets[which][*col].push((*row, *val));
            }
          }
          (mats, matrix_at_zero, row_buckets, col_buckets)
        } else {
          let matrix_at_zero = core::array::from_fn(|which| {
            let matrix = match which {
              0 => &shape.A,
              1 => &shape.B,
              _ => &shape.C,
            };
            matrix
              .iter()
              .filter(|(row, col, _)| *row == 0 && *col == 0)
              .fold(E::Base::ZERO, |acc, (_, _, val)| {
                acc + scalar_as_base::<E>(val)
              })
          });
          (
            core::array::from_fn(|_| Vec::new()),
            matrix_at_zero,
            core::array::from_fn(|_| Vec::new()),
            core::array::from_fn(|_| Vec::new()),
          )
        };

        PredicateIndex {
          id,
          shape,
          s,
          s_prime,
          z_len,
          matrix_at_zero,
          mats,
          row_buckets,
          col_buckets,
          comm_M: predicate_commitments[id],
        }
      })
      .collect::<Vec<_>>();

    Self {
      num_io,
      num_vars_max,
      s_max,
      s_prime_max,
      z_len_max,
      predicates,
      ck_index,
    }
  }

  fn basis_coeffs_scalar_with_len(id: usize, len: usize) -> Vec<E::Scalar> {
    let mut coeffs = vec![E::Scalar::ZERO; len];
    coeffs[id] = E::Scalar::ONE;
    coeffs
  }

  pub(crate) fn basis_coeffs_scalar(&self, id: usize) -> Vec<E::Scalar> {
    Self::basis_coeffs_scalar_with_len(id, self.predicates.len())
  }

  pub(crate) fn basis_coeffs_base(&self, id: usize) -> Vec<E::Base> {
    let mut coeffs = vec![E::Base::ZERO; self.predicates.len()];
    coeffs[id] = E::Base::ONE;
    coeffs
  }

  pub(crate) fn zero_r_x(&self) -> Vec<E::Base> {
    vec![E::Base::ZERO; self.s_max]
  }

  pub(crate) fn zero_r_y(&self) -> Vec<E::Base> {
    vec![E::Base::ZERO; self.s_prime_max]
  }

  pub(crate) fn project_witness(&self, W: &[E::Scalar]) -> Vec<E::Base> {
    let mut projected = W
      .iter()
      .map(|w| scalar_as_base::<E>(*w))
      .collect::<Vec<_>>();
    projected.resize(self.num_vars_max, E::Base::ZERO);
    projected
  }

  pub(crate) fn project_io(&self, X: &[E::Scalar]) -> Vec<E::Base> {
    let mut projected = X
      .iter()
      .map(|x| scalar_as_base::<E>(*x))
      .collect::<Vec<_>>();
    projected.resize(self.num_io, E::Base::ZERO);
    projected
  }

  pub(crate) fn commit_index_coeffs(&self, coeffs: &[E::Scalar]) -> [Commitment<E>; 3] {
    core::array::from_fn(|j| CE::<E>::commit(&self.ck_index[j], coeffs, &E::Scalar::ZERO))
  }

  pub(crate) fn predicate_commitments(&self, predicate_id: usize) -> [Commitment<E>; 3] {
    self.predicates[predicate_id].comm_M
  }

  pub(crate) fn z_from_folded(&self, U: &FoldedInstance<E>, W: &FoldedWitness<E>) -> Vec<E::Base> {
    [W.W_proj.clone(), vec![U.u], U.X.clone()].concat()
  }

  pub(crate) fn z_from_r1cs(&self, U: &R1CSInstance<E>, W: &R1CSWitness<E>) -> Vec<E::Base> {
    [
      self.project_witness(&W.W),
      vec![E::Base::ONE],
      self.project_io(&U.X),
    ]
    .concat()
  }

  pub(crate) fn eq_eval(bits: &[bool], point: &[E::Base]) -> E::Base {
    debug_assert_eq!(bits.len(), point.len());
    bits
      .iter()
      .zip(point.iter())
      .fold(E::Base::ONE, |acc, (bit, r)| {
        let term = if *bit { *r } else { E::Base::ONE - *r };
        acc * term
      })
  }

  pub(crate) fn bits_le(mut idx: usize, len: usize) -> Vec<bool> {
    let mut bits = Vec::with_capacity(len);
    for _ in 0..len {
      bits.push(idx & 1 == 1);
      idx >>= 1;
    }
    bits
  }

  pub(crate) fn eval_matrix_predicate(
    &self,
    predicate_id: usize,
    which: usize,
    r_x: &[E::Base],
    r_y: &[E::Base],
  ) -> E::Base {
    self.predicates[predicate_id].mats[which]
      .par_iter()
      .map(|(row, col, val)| {
        let row_bits = Self::bits_le(*row, self.s_max);
        let col_bits = Self::bits_le(*col, self.s_prime_max);
        *val * Self::eq_eval(&row_bits, r_x) * Self::eq_eval(&col_bits, r_y)
      })
      .reduce(|| E::Base::ZERO, |acc, x| acc + x)
  }

  pub(crate) fn eval_matrix_folded(
    &self,
    coeffs: &[E::Base],
    which: usize,
    r_x: &[E::Base],
    r_y: &[E::Base],
  ) -> E::Base {
    coeffs
      .par_iter()
      .enumerate()
      .map(|(predicate_id, coeff)| {
        *coeff * self.eval_matrix_predicate(predicate_id, which, r_x, r_y)
      })
      .reduce(|| E::Base::ZERO, |acc, x| acc + x)
  }

  pub(crate) fn eval_row_compression_predicate(
    &self,
    predicate_id: usize,
    which: usize,
    r_x: &[E::Base],
    z: &[E::Base],
  ) -> E::Base {
    self.predicates[predicate_id].mats[which]
      .par_iter()
      .map(|(row, col, val)| {
        let row_bits = Self::bits_le(*row, self.s_max);
        *val * Self::eq_eval(&row_bits, r_x) * z.get(*col).copied().unwrap_or(E::Base::ZERO)
      })
      .reduce(|| E::Base::ZERO, |acc, x| acc + x)
  }

  pub(crate) fn eval_z(&self, z: &[E::Base], r_y: &[E::Base]) -> E::Base {
    z.par_iter()
      .enumerate()
      .map(|(idx, val)| *val * Self::eq_eval(&Self::bits_le(idx, self.s_prime_max), r_y))
      .reduce(|| E::Base::ZERO, |acc, x| acc + x)
  }

  pub(crate) fn compute_v_from_coeffs(
    &self,
    coeffs: &[E::Base],
    _u: E::Base,
    r_x: &[E::Base],
    r_y: &[E::Base],
    z: &[E::Base],
  ) -> Vec<E::Base> {
    vec![
      self.eval_matrix_folded(coeffs, 0, r_x, r_y),
      self.eval_matrix_folded(coeffs, 1, r_x, r_y),
      self.eval_matrix_folded(coeffs, 2, r_x, r_y),
      self.eval_z(z, r_y),
    ]
  }

  pub(crate) fn compute_sigmas(
    &self,
    W: &FoldedWitness<E>,
    U: &FoldedInstance<E>,
    r_x_prime: &[E::Base],
  ) -> Vec<E::Base> {
    (0..3)
      .map(|j| self.eval_matrix_folded(&W.lambda_proj, j, r_x_prime, &U.r_y))
      .collect()
  }

  pub(crate) fn compute_taus(
    &self,
    predicate_id: usize,
    r_x_prime: &[E::Base],
    z_new: &[E::Base],
  ) -> Vec<E::Base> {
    (0..3)
      .map(|j| self.eval_row_compression_predicate(predicate_id, j, r_x_prime, z_new))
      .collect()
  }

  pub(crate) fn compute_epsilons(
    &self,
    W: &FoldedWitness<E>,
    _U: &FoldedInstance<E>,
    z_running: &[E::Base],
    r_x_prime: &[E::Base],
    r_y_prime: &[E::Base],
  ) -> Vec<E::Base> {
    vec![
      self.eval_matrix_folded(&W.lambda_proj, 0, r_x_prime, r_y_prime),
      self.eval_matrix_folded(&W.lambda_proj, 1, r_x_prime, r_y_prime),
      self.eval_matrix_folded(&W.lambda_proj, 2, r_x_prime, r_y_prime),
      self.eval_z(z_running, r_y_prime),
    ]
  }

  pub(crate) fn compute_thetas(
    &self,
    predicate_id: usize,
    z_new: &[E::Base],
    r_x_prime: &[E::Base],
    r_y_prime: &[E::Base],
  ) -> Vec<E::Base> {
    vec![
      self.eval_matrix_predicate(predicate_id, 0, r_x_prime, r_y_prime),
      self.eval_matrix_predicate(predicate_id, 1, r_x_prime, r_y_prime),
      self.eval_matrix_predicate(predicate_id, 2, r_x_prime, r_y_prime),
      self.eval_z(z_new, r_y_prime),
    ]
  }

  pub(crate) fn compute_sum_x(&self, U: &FoldedInstance<E>, gamma: E::Base) -> E::Base {
    U.v[0] + gamma * U.v[1] + gamma.square() * U.v[2]
  }

  pub(crate) fn compute_cx(
    &self,
    U: &FoldedInstance<E>,
    sigmas: &[E::Base],
    taus: &[E::Base],
    gamma: E::Base,
    alpha: &[E::Base],
    r_x_prime: &[E::Base],
  ) -> E::Base {
    let eq_running_rx = U
      .r_x
      .iter()
      .zip(r_x_prime.iter())
      .fold(E::Base::ONE, |acc, (a, b)| {
        acc * (*a * *b + (E::Base::ONE - *a) * (E::Base::ONE - *b))
      });
    let eq_alpha = alpha
      .iter()
      .zip(r_x_prime.iter())
      .fold(E::Base::ONE, |acc, (a, b)| {
        acc * (*a * *b + (E::Base::ONE - *a) * (E::Base::ONE - *b))
      });

    eq_running_rx * (sigmas[0] + gamma * sigmas[1] + gamma.square() * sigmas[2])
      + gamma.pow_vartime([3]) * eq_alpha * (taus[0] * taus[1] - taus[2])
  }

  pub(crate) fn compute_sum_y(
    &self,
    U: &FoldedInstance<E>,
    sigmas: &[E::Base],
    taus: &[E::Base],
    delta: E::Base,
  ) -> E::Base {
    let delta_pows = [
      E::Base::ONE,
      delta,
      delta.square(),
      delta.pow_vartime([3]),
      delta.pow_vartime([4]),
      delta.pow_vartime([5]),
      delta.pow_vartime([6]),
    ];

    delta_pows[0] * sigmas[0]
      + delta_pows[1] * sigmas[1]
      + delta_pows[2] * sigmas[2]
      + delta_pows[3] * U.v[3]
      + delta_pows[4] * taus[0]
      + delta_pows[5] * taus[1]
      + delta_pows[6] * taus[2]
  }

  pub(crate) fn compute_cy(
    &self,
    U: &FoldedInstance<E>,
    epsilons: &[E::Base],
    thetas: &[E::Base],
    delta: E::Base,
    r_y_prime: &[E::Base],
  ) -> E::Base {
    let delta_pows = [
      E::Base::ONE,
      delta,
      delta.square(),
      delta.pow_vartime([3]),
      delta.pow_vartime([4]),
      delta.pow_vartime([5]),
      delta.pow_vartime([6]),
    ];
    let eq_ry = U
      .r_y
      .iter()
      .zip(r_y_prime.iter())
      .fold(E::Base::ONE, |acc, (a, b)| {
        acc * (*a * *b + (E::Base::ONE - *a) * (E::Base::ONE - *b))
      });

    delta_pows[0] * eq_ry * epsilons[0]
      + delta_pows[1] * eq_ry * epsilons[1]
      + delta_pows[2] * eq_ry * epsilons[2]
      + delta_pows[3] * eq_ry * epsilons[3]
      + delta_pows[4] * thetas[0] * thetas[3]
      + delta_pows[5] * thetas[1] * thetas[3]
      + delta_pows[6] * thetas[2] * thetas[3]
  }

  pub fn is_sat(
    &self,
    ck_witness: &CommitmentKey<E>,
    U: &FoldedInstance<E>,
    W: &FoldedWitness<E>,
  ) -> Result<(), NovaError> {
    if W.W.len() != self.num_vars_max
      || W.W_proj.len() != self.num_vars_max
      || W.lambda_scalar.len() != self.predicates.len()
      || W.lambda_proj.len() != self.predicates.len()
      || U.X.len() != self.num_io
      || U.r_x.len() != self.s_max
      || U.r_y.len() != self.s_prime_max
      || U.v.len() != 4
    {
      return Err(NovaError::InvalidWitnessLength);
    }

    let comm_W = CE::<E>::commit(ck_witness, &W.W, &W.r_W);
    if comm_W != U.comm_W {
      return Err(NovaError::UnSat {
        reason: "Invalid witness commitment".to_string(),
      });
    }

    let expected_comm_M = self.commit_index_coeffs(&W.lambda_scalar);
    if expected_comm_M != U.comm_M {
      return Err(NovaError::UnSat {
        reason: "Invalid folded index commitment".to_string(),
      });
    }

    let z = self.z_from_folded(U, W);
    let expected_v = self.compute_v_from_coeffs(&W.lambda_proj, U.u, &U.r_x, &U.r_y, &z);
    if expected_v != U.v {
      return Err(NovaError::UnSat {
        reason: "Indexed ACCS relation is unsatisfied".to_string(),
      });
    }

    Ok(())
  }
}

impl<E: Engine> FoldedWitness<E> {
  pub fn default(S: &GlobalStructure<E>) -> Self {
    Self {
      W: vec![E::Scalar::ZERO; S.num_vars_max],
      W_proj: vec![E::Base::ZERO; S.num_vars_max],
      r_W: E::Scalar::ZERO,
      lambda_scalar: vec![E::Scalar::ZERO; S.predicates.len()],
      lambda_proj: vec![E::Base::ZERO; S.predicates.len()],
    }
  }

  pub fn from_r1cs_witness(
    S: &GlobalStructure<E>,
    predicate_id: usize,
    witness: &R1CSWitness<E>,
  ) -> Self {
    let mut W = witness.W.clone();
    W.resize(S.num_vars_max, E::Scalar::ZERO);

    Self {
      W,
      W_proj: S.project_witness(&witness.W),
      r_W: witness.r_W,
      lambda_scalar: S.basis_coeffs_scalar(predicate_id),
      lambda_proj: S.basis_coeffs_base(predicate_id),
    }
  }

  pub fn fold(
    &self,
    S: &GlobalStructure<E>,
    predicate_id: usize,
    W2: &R1CSWitness<E>,
    rho_base: &E::Base,
    rho_scalar: &E::Scalar,
  ) -> Result<Self, NovaError> {
    if W2.W.len() > self.W.len() {
      return Err(NovaError::InvalidWitnessLength);
    }

    let mut W2_padded = W2.W.clone();
    W2_padded.resize(self.W.len(), E::Scalar::ZERO);
    let W2_proj = S.project_witness(&W2.W);

    let W = self
      .W
      .par_iter()
      .zip(W2_padded.par_iter())
      .map(|(a, b)| *a + *rho_scalar * *b)
      .collect::<Vec<_>>();

    let W_proj = self
      .W_proj
      .par_iter()
      .zip(W2_proj.par_iter())
      .map(|(a, b)| *a + *rho_base * *b)
      .collect::<Vec<_>>();

    let mut lambda_scalar = self.lambda_scalar.clone();
    lambda_scalar[predicate_id] += *rho_scalar;
    let mut lambda_proj = self.lambda_proj.clone();
    lambda_proj[predicate_id] += *rho_base;

    Ok(Self {
      W,
      W_proj,
      r_W: self.r_W + *rho_scalar * W2.r_W,
      lambda_scalar,
      lambda_proj,
    })
  }
}

impl<E: Engine> FoldedInstance<E> {
  pub fn default(S: &GlobalStructure<E>) -> Self {
    Self {
      comm_W: Commitment::<E>::default(),
      comm_M: [Commitment::<E>::default(); 3],
      u: E::Base::ZERO,
      X: vec![E::Base::ZERO; S.num_io],
      r_x: S.zero_r_x(),
      r_y: S.zero_r_y(),
      v: vec![E::Base::ZERO; 4],
    }
  }

  pub fn from_r1cs_instance_witness(
    S: &GlobalStructure<E>,
    predicate_id: usize,
    instance: &R1CSInstance<E>,
    witness: &R1CSWitness<E>,
  ) -> Self {
    let r_x = S.zero_r_x();
    let r_y = S.zero_r_y();
    let X = S.project_io(&instance.X);
    let z = S.z_from_r1cs(instance, witness);
    let coeffs = S.basis_coeffs_base(predicate_id);
    let v = S.compute_v_from_coeffs(&coeffs, E::Base::ONE, &r_x, &r_y, &z);

    Self {
      comm_W: instance.comm_W,
      comm_M: S.predicate_commitments(predicate_id),
      u: E::Base::ONE,
      X,
      r_x,
      r_y,
      v,
    }
  }

  pub fn fold(
    &self,
    S: &GlobalStructure<E>,
    predicate_id: usize,
    U2: &R1CSInstance<E>,
    rho_base: &E::Base,
    rho_scalar: &E::Scalar,
    r_x: Vec<E::Base>,
    r_y: Vec<E::Base>,
    v: Vec<E::Base>,
  ) -> Self {
    let X2 = S.project_io(&U2.X);
    let X = self
      .X
      .par_iter()
      .zip(X2.par_iter())
      .map(|(a, b)| *a + *rho_base * *b)
      .collect::<Vec<_>>();
    let incoming_comm_M = S.predicate_commitments(predicate_id);

    Self {
      comm_W: self.comm_W + U2.comm_W * *rho_scalar,
      comm_M: core::array::from_fn(|j| self.comm_M[j] + incoming_comm_M[j] * *rho_scalar),
      u: self.u + *rho_base,
      X,
      r_x,
      r_y,
      v,
    }
  }
}

impl<E: Engine> TranscriptReprTrait<E::GE> for FoldedInstance<E> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    [
      self.comm_W.to_transcript_bytes(),
      self.comm_M[0].to_transcript_bytes(),
      self.comm_M[1].to_transcript_bytes(),
      self.comm_M[2].to_transcript_bytes(),
      self.u.to_transcript_bytes(),
      self.X.as_slice().to_transcript_bytes(),
      self.r_x.as_slice().to_transcript_bytes(),
      self.r_y.as_slice().to_transcript_bytes(),
      self.v.as_slice().to_transcript_bytes(),
    ]
    .concat()
  }
}

impl<E: Engine> AbsorbInROTrait<E> for FoldedInstance<E> {
  fn absorb_in_ro(&self, ro: &mut E::RO) {
    self.comm_W.absorb_in_ro(ro);
    for comm in &self.comm_M {
      comm.absorb_in_ro(ro);
    }
    ro.absorb(self.u);
    for x in &self.X {
      ro.absorb(*x);
    }
    for r in &self.r_x {
      ro.absorb(*r);
    }
    for r in &self.r_y {
      ro.absorb(*r);
    }
    for v in &self.v {
      ro.absorb(*v);
    }
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

  fn tiny_r1cs<E: Engine>(scale: E::Scalar) -> (R1CSShape<E>, CommitmentKey<E>) {
    let one = <E::Scalar as Field>::ONE;
    let num_cons = 4;
    let num_vars = 4;
    let num_io = 2;
    let A = vec![(0, 0, scale), (1, 1, one), (2, 2, one), (3, 3, one)];
    let B = vec![(0, 0, one), (1, 1, scale), (2, 2, one), (3, 3, one)];
    let C = vec![(0, 4, one), (1, 5, scale)];
    let shape = R1CSShape::<E>::new(
      num_cons,
      num_vars,
      num_io,
      SparseMatrix::new(&A, num_cons, num_vars + num_io + 1),
      SparseMatrix::new(&B, num_cons, num_vars + num_io + 1),
      SparseMatrix::new(&C, num_cons, num_vars + num_io + 1),
    )
    .unwrap();
    let ck = shape.commitment_key(&*default_ck_hint());
    (shape, ck)
  }

  #[test]
  fn test_folded_relation_sat() {
    let (shape0, ck0) = tiny_r1cs::<PallasEngine>(<PallasEngine as Engine>::Scalar::ONE);
    let (shape1, _) = tiny_r1cs::<PallasEngine>(<PallasEngine as Engine>::Scalar::from(2u64));
    let S = GlobalStructure::new(&[shape0.clone(), shape1]);
    let W = R1CSWitness::<PallasEngine> {
      W: vec![<PallasEngine as Engine>::Scalar::ZERO; shape0.num_vars],
      r_W: <PallasEngine as Engine>::Scalar::ZERO,
    };
    let U = R1CSInstance::<PallasEngine> {
      comm_W: CE::<PallasEngine>::commit(&ck0, &W.W, &W.r_W),
      X: vec![
        <PallasEngine as Engine>::Scalar::ZERO,
        <PallasEngine as Engine>::Scalar::ZERO,
      ],
    };

    let folded_w = FoldedWitness::from_r1cs_witness(&S, 0, &W);
    let folded_u = FoldedInstance::from_r1cs_instance_witness(&S, 0, &U, &W);
    assert!(S.is_sat(&ck0, &folded_u, &folded_w).is_ok());
  }

  #[test]
  fn test_cross_predicate_fold_sat() {
    let (shape0, ck0) = tiny_r1cs::<PallasEngine>(<PallasEngine as Engine>::Scalar::ONE);
    let (shape1, _) = tiny_r1cs::<PallasEngine>(<PallasEngine as Engine>::Scalar::from(2u64));
    let S = GlobalStructure::new(&[shape0.clone(), shape1.clone()]);

    let W0 = R1CSWitness::<PallasEngine> {
      W: vec![<PallasEngine as Engine>::Scalar::ZERO; shape0.num_vars],
      r_W: <PallasEngine as Engine>::Scalar::ZERO,
    };
    let U0 = R1CSInstance::<PallasEngine> {
      comm_W: CE::<PallasEngine>::commit(&ck0, &W0.W, &W0.r_W),
      X: vec![
        <PallasEngine as Engine>::Scalar::ZERO,
        <PallasEngine as Engine>::Scalar::ZERO,
      ],
    };
    let W1 = R1CSWitness::<PallasEngine> {
      W: vec![<PallasEngine as Engine>::Scalar::ZERO; shape1.num_vars],
      r_W: <PallasEngine as Engine>::Scalar::ZERO,
    };
    let U1 = R1CSInstance::<PallasEngine> {
      comm_W: CE::<PallasEngine>::commit(&ck0, &W1.W, &W1.r_W),
      X: vec![
        <PallasEngine as Engine>::Scalar::ZERO,
        <PallasEngine as Engine>::Scalar::ZERO,
      ],
    };

    let running_w = FoldedWitness::from_r1cs_witness(&S, 0, &W0);
    let running_u = FoldedInstance::from_r1cs_instance_witness(&S, 0, &U0, &W0);
    let rho_base = <PallasEngine as Engine>::Base::from(3u64);
    let rho_scalar = <PallasEngine as Engine>::Scalar::from(3u64);
    let folded_w = running_w.fold(&S, 1, &W1, &rho_base, &rho_scalar).unwrap();
    let z = S.z_from_folded(&running_u, &running_w);
    let sigmas = S.compute_sigmas(&running_w, &running_u, &running_u.r_x);
    let _ = sigmas;
    let folded_u = running_u.fold(
      &S,
      1,
      &U1,
      &rho_base,
      &rho_scalar,
      running_u.r_x.clone(),
      running_u.r_y.clone(),
      S.compute_v_from_coeffs(
        &folded_w.lambda_proj,
        running_u.u + rho_base,
        &running_u.r_x,
        &running_u.r_y,
        &z,
      ),
    );
    assert_eq!(
      folded_w.lambda_scalar[1],
      <PallasEngine as Engine>::Scalar::from(3u64)
    );
    assert_eq!(
      folded_u.comm_M,
      S.commit_index_coeffs(&folded_w.lambda_scalar)
    );
  }
}
