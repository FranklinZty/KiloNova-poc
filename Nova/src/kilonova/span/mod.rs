//! This module implements an experimental non-uniform IVC path based on
//! R1CS-specialized Holographic Folding.
use crate::{
  constants::NUM_HASH_BITS,
  digest::{DigestComputer, SimpleDigestible},
  errors::NovaError,
  frontend::{
    num::AllocatedNum, r1cs::NovaWitness, shape_cs::ShapeCS, solver::SatisfyingAssignment,
    ConstraintSystem, Index, LinearCombination, SynthesisError,
  },
  gadgets::utils::scalar_as_base,
  r1cs::{sparse::SparseMatrix, CommitmentKeyHint, R1CSInstance, R1CSShape, R1CSWitness},
  traits::{
    commitment::CommitmentEngineTrait, AbsorbInROTrait, Engine, ROConstants, ROConstantsCircuit,
    ROTrait,
  },
  Commitment, CommitmentKey,
};
use core::marker::PhantomData;
use ff::{Field, PrimeField};
use once_cell::sync::OnceCell;
use rand_core::OsRng;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

mod circuit;
pub mod nifs;
pub mod relation;

pub(crate) use circuit::{KiloNovaAugmentedCircuit, KiloNovaAugmentedCircuitInputs};
use nifs::NIFS;
use relation::{FoldedInstance, FoldedWitness, GlobalStructure};

pub trait PredicateSet<F: PrimeField>: Send + Sync + Clone {
  fn arity(&self) -> usize;
  fn num_predicates(&self) -> usize;
  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    predicate_id: usize,
    cs: &mut CS,
    z: &[AllocatedNum<F>],
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>;
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TrivialPredicateSet<F: PrimeField> {
  _p: PhantomData<F>,
}

impl<F: PrimeField> PredicateSet<F> for TrivialPredicateSet<F> {
  fn arity(&self) -> usize {
    1
  }

  fn num_predicates(&self) -> usize {
    1
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    _predicate_id: usize,
    _cs: &mut CS,
    z: &[AllocatedNum<F>],
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
    Ok(z.to_vec())
  }
}

#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PublicParams<E1, E2, PS>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  PS: PredicateSet<E1::Scalar>,
{
  F_arity: usize,
  ro_consts_primary: ROConstants<E1>,
  ro_consts_circuit_primary: ROConstantsCircuit<E2>,
  ro_consts_secondary: ROConstants<E2>,
  ro_consts_circuit_secondary: ROConstantsCircuit<E1>,
  ck_primary: CommitmentKey<E1>,
  structure_primary: GlobalStructure<E1>,
  ck_secondary: CommitmentKey<E2>,
  structure_secondary: GlobalStructure<E2>,
  #[serde(skip, default = "OnceCell::new")]
  digest: OnceCell<E1::Scalar>,
  _p: PhantomData<PS>,
}

impl<E1, E2, PS> SimpleDigestible for PublicParams<E1, E2, PS>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  PS: PredicateSet<E1::Scalar>,
{
}

fn dummy_shape<E: Engine>() -> R1CSShape<E> {
  let num_cons = 1 << 2;
  let num_vars = 1 << 2;
  let num_io = 2;
  R1CSShape::new(
    num_cons,
    num_vars,
    num_io,
    SparseMatrix::new(&[], num_cons, num_vars + num_io + 1),
    SparseMatrix::new(&[], num_cons, num_vars + num_io + 1),
    SparseMatrix::new(&[], num_cons, num_vars + num_io + 1),
  )
  .unwrap()
}

fn dummy_r1cs_instance<E: Engine>(num_io: usize) -> R1CSInstance<E> {
  R1CSInstance {
    comm_W: Commitment::<E>::default(),
    X: vec![E::Scalar::ZERO; num_io],
  }
}

fn structure_signature<E: Engine>(
  structure: &GlobalStructure<E>,
) -> (usize, usize, usize, usize, Vec<(usize, usize, usize)>) {
  (
    structure.num_vars_max,
    structure.s_max,
    structure.s_prime_max,
    structure.predicates.len(),
    structure
      .predicates
      .iter()
      .map(|predicate| {
        (
          predicate.shape.num_cons,
          predicate.shape.num_vars,
          predicate.shape.num_io,
        )
      })
      .collect::<Vec<_>>(),
  )
}

fn max_commitment_key_size<E: Engine>(
  shapes: &[R1CSShape<E>],
  ck_hint: &CommitmentKeyHint<E>,
) -> usize {
  shapes
    .iter()
    .map(|shape| {
      let hint = ck_hint(shape);
      core::cmp::max(shape.num_vars, hint)
    })
    .max()
    .unwrap()
}

fn add_shape_constraint<S: PrimeField>(
  X: &mut (
    &mut SparseMatrix<S>,
    &mut SparseMatrix<S>,
    &mut SparseMatrix<S>,
    &mut usize,
  ),
  num_vars: usize,
  a_lc: &LinearCombination<S>,
  b_lc: &LinearCombination<S>,
  c_lc: &LinearCombination<S>,
) {
  let (A, B, C, nn) = X;
  let n = **nn;
  assert_eq!(n + 1, A.indptr.len(), "A: invalid shape");
  assert_eq!(n + 1, B.indptr.len(), "B: invalid shape");
  assert_eq!(n + 1, C.indptr.len(), "C: invalid shape");

  let add_constraint_component = |index: Index, coeff: &S, M: &mut SparseMatrix<S>| {
    if *coeff != S::ZERO {
      match index {
        Index::Input(idx) => {
          let idx = idx + num_vars;
          M.data.push(*coeff);
          M.indices.push(idx);
        }
        Index::Aux(idx) => {
          M.data.push(*coeff);
          M.indices.push(idx);
        }
      }
    }
  };

  for (index, coeff) in a_lc.iter() {
    add_constraint_component(index.0, coeff, A);
  }
  A.indptr.push(A.indices.len());

  for (index, coeff) in b_lc.iter() {
    add_constraint_component(index.0, coeff, B)
  }
  B.indptr.push(B.indices.len());

  for (index, coeff) in c_lc.iter() {
    add_constraint_component(index.0, coeff, C)
  }
  C.indptr.push(C.indices.len());

  **nn += 1;
}

fn shape_cs_to_shape<E: Engine>(cs: &ShapeCS<E>) -> R1CSShape<E> {
  let mut A = SparseMatrix::<E::Scalar>::empty();
  let mut B = SparseMatrix::<E::Scalar>::empty();
  let mut C = SparseMatrix::<E::Scalar>::empty();

  let mut num_cons_added = 0;
  let mut X = (&mut A, &mut B, &mut C, &mut num_cons_added);
  let num_inputs = cs.num_inputs();
  let num_constraints = cs.num_constraints();
  let num_vars = cs.num_aux();

  for constraint in cs.constraints.iter() {
    add_shape_constraint(
      &mut X,
      num_vars,
      &constraint.0,
      &constraint.1,
      &constraint.2,
    );
  }
  assert_eq!(num_cons_added, num_constraints);

  A.cols = num_vars + num_inputs;
  B.cols = num_vars + num_inputs;
  C.cols = num_vars + num_inputs;

  R1CSShape::new(num_constraints, num_vars, num_inputs - 1, A, B, C).unwrap()
}

fn update_trace_digest<F: PrimeField>(trace_digest: F, predicate_id: usize) -> F {
  let delta = F::from((predicate_id as u64) + 1);
  (trace_digest + delta).square() + delta
}

impl<E1, E2, PS> PublicParams<E1, E2, PS>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  PS: PredicateSet<E1::Scalar>,
{
  pub fn setup(
    predicates: &PS,
    ck_hint1: &CommitmentKeyHint<E1>,
    ck_hint2: &CommitmentKeyHint<E2>,
  ) -> Result<Self, NovaError> {
    let ro_consts_primary = ROConstants::<E1>::default();
    let ro_consts_secondary = ROConstants::<E2>::default();
    let ro_consts_circuit_primary = ROConstantsCircuit::<E2>::default();
    let ro_consts_circuit_secondary = ROConstantsCircuit::<E1>::default();
    let F_arity = predicates.arity();

    let tc = TrivialPredicateSet::<E2::Scalar>::default();
    let dummy_secondary = dummy_shape::<E2>();
    let mut guess_secondary = GlobalStructure::new_for_setup(&[dummy_secondary.clone()]);

    let (primary_shapes_final, secondary_shape_final) = loop {
      let primary_shapes = (0..predicates.num_predicates())
        .into_par_iter()
        .map(|predicate_id| {
          let circuit_primary: KiloNovaAugmentedCircuit<'_, E2, PS> = KiloNovaAugmentedCircuit::new(
            true,
            None,
            predicates,
            predicate_id,
            0,
            ro_consts_circuit_primary.clone(),
            guess_secondary.clone(),
          );
          let mut cs_primary: ShapeCS<E1> = ShapeCS::new();
          let _ = circuit_primary.synthesize(&mut cs_primary);
          shape_cs_to_shape(&cs_primary)
        })
        .collect::<Vec<_>>();
      let structure_primary = GlobalStructure::new_for_setup(&primary_shapes);

      let circuit_secondary: KiloNovaAugmentedCircuit<'_, E1, _> = KiloNovaAugmentedCircuit::new(
        false,
        None,
        &tc,
        0,
        0,
        ro_consts_circuit_secondary.clone(),
        structure_primary.clone(),
      );
      let mut cs_secondary: ShapeCS<E2> = ShapeCS::new();
      let _ = circuit_secondary.synthesize(&mut cs_secondary);
      let shape_secondary = shape_cs_to_shape(&cs_secondary);
      let structure_secondary = GlobalStructure::new_for_setup(&[shape_secondary.clone()]);

      if structure_signature(&guess_secondary) == structure_signature(&structure_secondary) {
        break (primary_shapes, shape_secondary);
      }

      guess_secondary = structure_secondary;
    };

    let ck_primary = E1::CE::setup(
      b"ck",
      max_commitment_key_size(&primary_shapes_final, ck_hint1),
    );
    let ck_secondary = E2::CE::setup(
      b"ck",
      max_commitment_key_size(&[secondary_shape_final.clone()], ck_hint2),
    );

    let structure_primary = GlobalStructure::new(&primary_shapes_final);
    let structure_secondary = GlobalStructure::new(&[secondary_shape_final]);

    if structure_primary.num_io != 2 || structure_secondary.num_io != 2 {
      return Err(NovaError::InvalidStepCircuitIO);
    }

    let pp = Self {
      F_arity,
      ro_consts_primary,
      ro_consts_circuit_primary,
      ro_consts_secondary,
      ro_consts_circuit_secondary,
      ck_primary,
      structure_primary,
      ck_secondary,
      structure_secondary,
      digest: OnceCell::new(),
      _p: Default::default(),
    };
    let _ = pp.digest();
    Ok(pp)
  }

  pub fn digest(&self) -> E1::Scalar {
    self
      .digest
      .get_or_try_init(|| DigestComputer::new(self).digest())
      .cloned()
      .expect("Failure in retrieving digest")
  }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RecursiveSNARK<E1, E2, PS>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  PS: PredicateSet<E1::Scalar>,
{
  z0: Vec<E1::Scalar>,
  r_W_primary: FoldedWitness<E1>,
  r_U_primary: FoldedInstance<E1>,
  ri_primary: E1::Scalar,
  r_W_secondary: FoldedWitness<E2>,
  r_U_secondary: FoldedInstance<E2>,
  ri_secondary: E2::Scalar,
  l_w_secondary: R1CSWitness<E2>,
  l_u_secondary: R1CSInstance<E2>,
  i: usize,
  zi: Vec<E1::Scalar>,
  trace_primary: E1::Scalar,
  trace_secondary: E2::Scalar,
  _p: PhantomData<PS>,
}

impl<E1, E2, PS> RecursiveSNARK<E1, E2, PS>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  PS: PredicateSet<E1::Scalar>,
{
  pub fn new(
    pp: &PublicParams<E1, E2, PS>,
    predicates: &PS,
    z0: &[E1::Scalar],
    first_predicate_id: usize,
  ) -> Result<Self, NovaError> {
    if z0.len() != pp.F_arity || first_predicate_id >= predicates.num_predicates() {
      return Err(NovaError::InvalidInitialInputLength);
    }

    let ri_primary = E1::Scalar::random(&mut OsRng);
    let ri_secondary = E2::Scalar::random(&mut OsRng);

    let mut cs_primary = SatisfyingAssignment::<E1>::new();
    let inputs_primary = KiloNovaAugmentedCircuitInputs::new(
      scalar_as_base::<E1>(pp.digest()),
      E1::Scalar::ZERO,
      z0.to_vec(),
      None,
      E1::Scalar::ZERO,
      E1::Scalar::from(first_predicate_id as u64),
      E1::Scalar::ZERO,
      Some(FoldedInstance::default(&pp.structure_secondary)),
      Some(vec![E1::Scalar::ZERO; pp.structure_secondary.num_vars_max]),
      None,
      ri_primary,
      Some(dummy_r1cs_instance::<E2>(pp.structure_secondary.num_io)),
      Some(vec![E1::Scalar::ZERO; pp.structure_secondary.num_vars_max]),
      Some(NIFS::dummy(
        &pp.ro_consts_secondary,
        &scalar_as_base::<E1>(pp.digest()),
        &pp.structure_secondary,
        0,
        &dummy_r1cs_instance::<E2>(pp.structure_secondary.num_io),
      )),
    );
    let circuit_primary: KiloNovaAugmentedCircuit<'_, E2, PS> = KiloNovaAugmentedCircuit::new(
      true,
      Some(inputs_primary),
      predicates,
      first_predicate_id,
      0,
      pp.ro_consts_circuit_primary.clone(),
      pp.structure_secondary.clone(),
    );
    let zi_primary = circuit_primary.synthesize(&mut cs_primary)?;
    let primary_predicate = &pp.structure_primary.predicates[first_predicate_id];
    let (u_primary, w_primary) =
      cs_primary.r1cs_instance_and_witness(&primary_predicate.shape, &pp.ck_primary)?;

    let r_W_primary = FoldedWitness::from_r1cs_witness(&pp.structure_primary, &w_primary);
    let r_U_primary = FoldedInstance::from_r1cs_instance_witness(
      &pp.structure_primary,
      first_predicate_id,
      &u_primary,
      &w_primary,
    );
    let bootstrap_running_W_primary = FoldedWitness::default(&pp.structure_primary);
    let bootstrap_running_U_primary = FoldedInstance::default(&pp.structure_primary);
    let bootstrap_nifs_primary = NIFS::dummy(
      &pp.ro_consts_primary,
      &pp.digest(),
      &pp.structure_primary,
      first_predicate_id,
      &u_primary,
    );

    let mut cs_secondary = SatisfyingAssignment::<E2>::new();
    let inputs_secondary = KiloNovaAugmentedCircuitInputs::new(
      pp.digest(),
      E2::Scalar::ZERO,
      vec![E2::Scalar::ZERO],
      None,
      E2::Scalar::ZERO,
      E2::Scalar::ZERO,
      E2::Scalar::from(first_predicate_id as u64),
      Some(bootstrap_running_U_primary),
      Some(bootstrap_running_W_primary.W_proj.clone()),
      None,
      ri_secondary,
      Some(u_primary.clone()),
      Some(pp.structure_primary.project_witness(&w_primary.W)),
      Some(bootstrap_nifs_primary),
    );
    let tc = TrivialPredicateSet::<E2::Scalar>::default();
    let circuit_secondary: KiloNovaAugmentedCircuit<'_, E1, _> = KiloNovaAugmentedCircuit::new(
      false,
      Some(inputs_secondary),
      &tc,
      0,
      first_predicate_id,
      pp.ro_consts_circuit_secondary.clone(),
      pp.structure_primary.clone(),
    );
    let _ = circuit_secondary.synthesize(&mut cs_secondary)?;
    let secondary_predicate = &pp.structure_secondary.predicates[0];
    let (u_secondary, w_secondary) =
      cs_secondary.r1cs_instance_and_witness(&secondary_predicate.shape, &pp.ck_secondary)?;

    let zi_primary = zi_primary
      .iter()
      .map(|v| v.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<_>, _>>()?;

    Ok(Self {
      z0: z0.to_vec(),
      r_W_primary,
      r_U_primary,
      ri_primary,
      r_W_secondary: FoldedWitness::default(&pp.structure_secondary),
      r_U_secondary: FoldedInstance::default(&pp.structure_secondary),
      ri_secondary,
      l_w_secondary: w_secondary,
      l_u_secondary: u_secondary,
      i: 1,
      zi: zi_primary,
      trace_primary: update_trace_digest(E1::Scalar::ZERO, first_predicate_id),
      trace_secondary: update_trace_digest(E2::Scalar::ZERO, first_predicate_id),
      _p: Default::default(),
    })
  }

  pub fn prove_step(
    &mut self,
    pp: &PublicParams<E1, E2, PS>,
    predicates: &PS,
    predicate_id: usize,
  ) -> Result<(), NovaError> {
    if predicate_id >= predicates.num_predicates() {
      return Err(NovaError::InvalidInputLength);
    }

    let (nifs_secondary, (r_U_secondary, r_W_secondary)) = NIFS::prove(
      &pp.ck_secondary,
      &pp.ro_consts_secondary,
      &scalar_as_base::<E1>(pp.digest()),
      &pp.structure_secondary,
      0,
      &self.r_U_secondary,
      &self.r_W_secondary,
      &self.l_u_secondary,
      &self.l_w_secondary,
    )?;

    let r_next_primary = E1::Scalar::random(&mut OsRng);
    let mut cs_primary = SatisfyingAssignment::<E1>::new();
    let inputs_primary = KiloNovaAugmentedCircuitInputs::new(
      scalar_as_base::<E1>(pp.digest()),
      E1::Scalar::from(self.i as u64),
      self.z0.to_vec(),
      Some(self.zi.clone()),
      self.trace_primary,
      E1::Scalar::from(predicate_id as u64),
      E1::Scalar::ZERO,
      Some(self.r_U_secondary.clone()),
      Some(self.r_W_secondary.W_proj.clone()),
      Some(self.ri_primary),
      r_next_primary,
      Some(self.l_u_secondary.clone()),
      Some(
        pp.structure_secondary
          .project_witness(&self.l_w_secondary.W),
      ),
      Some(nifs_secondary),
    );
    let circuit_primary: KiloNovaAugmentedCircuit<'_, E2, PS> = KiloNovaAugmentedCircuit::new(
      true,
      Some(inputs_primary),
      predicates,
      predicate_id,
      0,
      pp.ro_consts_circuit_primary.clone(),
      pp.structure_secondary.clone(),
    );
    let zi_primary = circuit_primary.synthesize(&mut cs_primary)?;
    let primary_predicate = &pp.structure_primary.predicates[predicate_id];
    let (l_u_primary, l_w_primary) =
      cs_primary.r1cs_instance_and_witness(&primary_predicate.shape, &pp.ck_primary)?;

    let (nifs_primary, (r_U_primary, r_W_primary)) = NIFS::prove(
      &pp.ck_primary,
      &pp.ro_consts_primary,
      &pp.digest(),
      &pp.structure_primary,
      predicate_id,
      &self.r_U_primary,
      &self.r_W_primary,
      &l_u_primary,
      &l_w_primary,
    )?;

    let r_next_secondary = E2::Scalar::random(&mut OsRng);
    let mut cs_secondary = SatisfyingAssignment::<E2>::new();
    let inputs_secondary = KiloNovaAugmentedCircuitInputs::new(
      pp.digest(),
      E2::Scalar::from(self.i as u64),
      vec![E2::Scalar::ZERO],
      Some(vec![E2::Scalar::ZERO]),
      self.trace_secondary,
      E2::Scalar::ZERO,
      E2::Scalar::from(predicate_id as u64),
      Some(self.r_U_primary.clone()),
      Some(self.r_W_primary.W_proj.clone()),
      Some(self.ri_secondary),
      r_next_secondary,
      Some(l_u_primary),
      Some(pp.structure_primary.project_witness(&l_w_primary.W)),
      Some(nifs_primary),
    );
    let tc = TrivialPredicateSet::<E2::Scalar>::default();
    let circuit_secondary: KiloNovaAugmentedCircuit<'_, E1, _> = KiloNovaAugmentedCircuit::new(
      false,
      Some(inputs_secondary),
      &tc,
      0,
      predicate_id,
      pp.ro_consts_circuit_secondary.clone(),
      pp.structure_primary.clone(),
    );
    let _ = circuit_secondary.synthesize(&mut cs_secondary)?;
    let secondary_predicate = &pp.structure_secondary.predicates[0];
    let (l_u_secondary, l_w_secondary) = cs_secondary
      .r1cs_instance_and_witness(&secondary_predicate.shape, &pp.ck_secondary)
      .map_err(|_| NovaError::UnSat {
        reason: "Unable to generate secondary witness".to_string(),
      })?;

    self.zi = zi_primary
      .iter()
      .map(|v| v.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<_>, _>>()?;
    self.l_u_secondary = l_u_secondary;
    self.l_w_secondary = l_w_secondary;
    self.r_U_primary = r_U_primary;
    self.r_W_primary = r_W_primary;
    self.r_U_secondary = r_U_secondary;
    self.r_W_secondary = r_W_secondary;
    self.ri_primary = r_next_primary;
    self.ri_secondary = r_next_secondary;
    self.i += 1;
    self.trace_primary = update_trace_digest(self.trace_primary, predicate_id);
    self.trace_secondary = update_trace_digest(self.trace_secondary, predicate_id);
    Ok(())
  }

  pub fn verify(
    &self,
    pp: &PublicParams<E1, E2, PS>,
    num_steps: usize,
    z0: &[E1::Scalar],
    predicate_trace: &[usize],
  ) -> Result<Vec<E1::Scalar>, NovaError> {
    let invalid = num_steps == 0
      || self.i != num_steps
      || self.z0 != z0
      || predicate_trace.len() != num_steps
      || predicate_trace
        .iter()
        .any(|predicate_id| *predicate_id >= pp.structure_primary.predicates.len())
      || self.l_u_secondary.X.len() != 2
      || self.r_U_primary.X.len() != 2
      || self.r_U_secondary.X.len() != 2;
    if invalid {
      return Err(NovaError::ProofVerifyError {
        reason: "Invalid number of steps or inputs".to_string(),
      });
    }

    let expected_trace_primary = predicate_trace
      .iter()
      .fold(E1::Scalar::ZERO, |acc, predicate_id| {
        update_trace_digest(acc, *predicate_id)
      });
    let expected_trace_secondary = predicate_trace
      .iter()
      .fold(E2::Scalar::ZERO, |acc, predicate_id| {
        update_trace_digest(acc, *predicate_id)
      });
    if expected_trace_primary != self.trace_primary
      || expected_trace_secondary != self.trace_secondary
    {
      return Err(NovaError::ProofVerifyError {
        reason: "Invalid predicate trace".to_string(),
      });
    }

    let (hash_primary, hash_secondary) = {
      let mut hasher = <E2 as Engine>::RO::new(pp.ro_consts_secondary.clone());
      hasher.absorb(pp.digest());
      hasher.absorb(E1::Scalar::from(num_steps as u64));
      for e in z0 {
        hasher.absorb(*e);
      }
      for e in &self.zi {
        hasher.absorb(*e);
      }
      self.r_U_secondary.absorb_in_ro(&mut hasher);
      hasher.absorb(self.ri_primary);
      hasher.absorb(self.trace_primary);

      let mut hasher2 = <E1 as Engine>::RO::new(pp.ro_consts_primary.clone());
      hasher2.absorb(scalar_as_base::<E1>(pp.digest()));
      hasher2.absorb(E2::Scalar::from(num_steps as u64));
      hasher2.absorb(E2::Scalar::ZERO);
      hasher2.absorb(E2::Scalar::ZERO);
      self.r_U_primary.absorb_in_ro(&mut hasher2);
      hasher2.absorb(self.ri_secondary);
      hasher2.absorb(self.trace_secondary);

      (
        hasher.squeeze(NUM_HASH_BITS),
        hasher2.squeeze(NUM_HASH_BITS),
      )
    };

    if hash_primary != scalar_as_base::<E2>(self.l_u_secondary.X[0])
      || hash_secondary != self.l_u_secondary.X[1]
    {
      return Err(NovaError::ProofVerifyError {
        reason: "Invalid output hash".to_string(),
      });
    }

    let (res_r_primary, (res_r_secondary, res_l_secondary)) = rayon::join(
      || {
        pp.structure_primary
          .is_sat(&pp.ck_primary, &self.r_U_primary, &self.r_W_primary)
      },
      || {
        rayon::join(
          || {
            pp.structure_secondary.is_sat(
              &pp.ck_secondary,
              &self.r_U_secondary,
              &self.r_W_secondary,
            )
          },
          || {
            pp.structure_secondary.predicates[0].shape.is_sat(
              &pp.ck_secondary,
              &self.l_u_secondary,
              &self.l_w_secondary,
            )
          },
        )
      },
    );

    res_r_primary?;
    res_r_secondary?;
    res_l_secondary?;
    Ok(self.zi.clone())
  }

  pub fn outputs(&self) -> &[E1::Scalar] {
    &self.zi
  }

  pub fn num_steps(&self) -> usize {
    self.i
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    frontend::{num::AllocatedNum, ConstraintSystem},
    provider::{PallasEngine, VestaEngine},
    traits::snark::default_ck_hint,
  };

  #[derive(Clone, Debug, Default)]
  struct ExamplePredicates<F: PrimeField> {
    _p: PhantomData<F>,
  }

  #[derive(Clone, Debug, Default)]
  struct BootstrapPredicates<F: PrimeField> {
    _p: PhantomData<F>,
  }

  impl<F: PrimeField> ExamplePredicates<F> {
    fn output(&self, predicate_id: usize, z: &[F]) -> Vec<F> {
      match predicate_id {
        0 => vec![z[0] + F::from(5u64)],
        _ => vec![z[0] * z[0] + z[0] + F::from(7u64)],
      }
    }

    fn synthesize_impl<CS: ConstraintSystem<F>>(
      &self,
      predicate_id: usize,
      cs: &mut CS,
      z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
      let x = &z[0];
      match predicate_id {
        0 => {
          let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
            Ok(x.get_value().unwrap() + F::from(5u64))
          })?;
          cs.enforce(
            || "y = x + 5",
            |lc| lc + x.get_variable() + (F::from(5u64), CS::one()),
            |lc| lc + CS::one(),
            |lc| lc + y.get_variable(),
          );
          Ok(vec![y])
        }
        _ => {
          let x_sq = x.square(cs.namespace(|| "x_sq"))?;
          let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
            Ok(x_sq.get_value().unwrap() + x.get_value().unwrap() + F::from(7u64))
          })?;
          cs.enforce(
            || "y = x^2 + x + 7",
            |lc| lc + x_sq.get_variable() + x.get_variable() + (F::from(7u64), CS::one()),
            |lc| lc + CS::one(),
            |lc| lc + y.get_variable(),
          );
          Ok(vec![y])
        }
      }
    }
  }

  impl<F: PrimeField> PredicateSet<F> for ExamplePredicates<F> {
    fn arity(&self) -> usize {
      1
    }

    fn num_predicates(&self) -> usize {
      2
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      predicate_id: usize,
      cs: &mut CS,
      z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
      self.synthesize_impl(predicate_id, cs, z)
    }
  }

  impl<F: PrimeField> super::super::PredicateSet<F> for ExamplePredicates<F> {
    fn arity(&self) -> usize {
      1
    }

    fn num_predicates(&self) -> usize {
      2
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      predicate_id: usize,
      cs: &mut CS,
      z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
      self.synthesize_impl(predicate_id, cs, z)
    }
  }

  impl<F: PrimeField> BootstrapPredicates<F> {
    fn output(&self, z: &[F]) -> Vec<F> {
      vec![z[0] + F::from(5u64)]
    }
  }

  impl<F: PrimeField> PredicateSet<F> for BootstrapPredicates<F> {
    fn arity(&self) -> usize {
      1
    }

    fn num_predicates(&self) -> usize {
      1
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      _predicate_id: usize,
      cs: &mut CS,
      z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
      let x = &z[0];
      let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
        Ok(x.get_value().unwrap() + F::from(5u64))
      })?;
      cs.enforce(
        || "y = x + 5",
        |lc| lc + x.get_variable() + (F::from(5u64), CS::one()),
        |lc| lc + CS::one(),
        |lc| lc + y.get_variable(),
      );
      Ok(vec![y])
    }
  }

  impl<F: PrimeField> super::super::PredicateSet<F> for BootstrapPredicates<F> {
    fn arity(&self) -> usize {
      1
    }

    fn num_predicates(&self) -> usize {
      1
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      predicate_id: usize,
      cs: &mut CS,
      z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
      <Self as PredicateSet<F>>::synthesize(self, predicate_id, cs, z)
    }
  }

  fn run_nonuniform_trace_test(predicate_trace: &[usize]) {
    use std::time::Instant;

    let predicates = ExamplePredicates::default();
    let setup_start = Instant::now();
    let pp = PublicParams::<
      PallasEngine,
      VestaEngine,
      ExamplePredicates<<PallasEngine as Engine>::Scalar>,
    >::setup(&predicates, &*default_ck_hint(), &*default_ck_hint())
    .unwrap();
    eprintln!("span trace setup {:?}", setup_start.elapsed());

    let new_start = Instant::now();
    let mut recursive_snark = RecursiveSNARK::<
      PallasEngine,
      VestaEngine,
      ExamplePredicates<<PallasEngine as Engine>::Scalar>,
    >::new(
      &pp,
      &predicates,
      &[<PallasEngine as Engine>::Scalar::ZERO],
      predicate_trace[0],
    )
    .unwrap();
    eprintln!("span trace new {:?}", new_start.elapsed());

    for (step, predicate_id) in predicate_trace.iter().enumerate().skip(1) {
      let prove_start = Instant::now();
      recursive_snark
        .prove_step(&pp, &predicates, *predicate_id)
        .unwrap();
      eprintln!("span trace prove_step[{step}] {:?}", prove_start.elapsed());
      let verify_step_start = Instant::now();
      assert!(recursive_snark
        .verify(
          &pp,
          step + 1,
          &[<PallasEngine as Engine>::Scalar::ZERO],
          &predicate_trace[..=step],
        )
        .is_ok());
      eprintln!(
        "span trace verify_step[{step}] {:?}",
        verify_step_start.elapsed()
      );
    }

    let verify_start = Instant::now();
    let zn = recursive_snark
      .verify(
        &pp,
        predicate_trace.len(),
        &[<PallasEngine as Engine>::Scalar::ZERO],
        &predicate_trace,
      )
      .unwrap();
    eprintln!("span trace final verify {:?}", verify_start.elapsed());
    let mut zn_direct = vec![<PallasEngine as Engine>::Scalar::ZERO];
    for predicate_id in predicate_trace {
      zn_direct = predicates.output(*predicate_id, &zn_direct);
    }
    assert_eq!(zn, zn_direct);
  }

  #[test]
  fn test_ivc_nontrivial_nonuniform_bootstrap() {
    use std::time::Instant;

    let predicates = BootstrapPredicates::default();
    let setup_start = Instant::now();
    let pp = PublicParams::<
      PallasEngine,
      VestaEngine,
      BootstrapPredicates<<PallasEngine as Engine>::Scalar>,
    >::setup(&predicates, &*default_ck_hint(), &*default_ck_hint())
    .unwrap();
    eprintln!("span bootstrap setup {:?}", setup_start.elapsed());

    let predicate_trace = [0usize];
    let new_start = Instant::now();
    let recursive_snark = RecursiveSNARK::<
      PallasEngine,
      VestaEngine,
      BootstrapPredicates<<PallasEngine as Engine>::Scalar>,
    >::new(
      &pp,
      &predicates,
      &[<PallasEngine as Engine>::Scalar::ZERO],
      0,
    )
    .unwrap();
    eprintln!("span bootstrap new {:?}", new_start.elapsed());

    let verify_start = Instant::now();
    let zn = recursive_snark
      .verify(
        &pp,
        predicate_trace.len(),
        &[<PallasEngine as Engine>::Scalar::ZERO],
        &predicate_trace,
      )
      .unwrap();
    eprintln!("span bootstrap verify {:?}", verify_start.elapsed());
    assert_eq!(
      zn,
      predicates.output(&[<PallasEngine as Engine>::Scalar::ZERO])
    );
  }

  #[test]
  fn test_ivc_nontrivial_nonuniform_smoke() {
    run_nonuniform_trace_test(&[0usize, 1usize]);
  }

  #[test]
  fn test_ivc_nontrivial_nonuniform() {
    run_nonuniform_trace_test(&[0usize, 1usize, 0usize]);
  }

  #[test]
  #[ignore = "performance comparison harness"]
  fn benchmark_direct_vs_span_nonuniform_trace() {
    use std::time::Instant;

    type FE = <PallasEngine as Engine>::Scalar;
    let predicates = ExamplePredicates::<FE>::default();
    let trace = [0usize, 1usize];
    let z0 = [FE::ZERO];

    let direct_setup_start = Instant::now();
    let direct_pp =
      super::super::PublicParams::<PallasEngine, VestaEngine, ExamplePredicates<FE>>::setup(
        &predicates,
        &*default_ck_hint(),
        &*default_ck_hint(),
      )
      .unwrap();
    let direct_setup = direct_setup_start.elapsed();

    let span_setup_start = Instant::now();
    let span_pp = PublicParams::<PallasEngine, VestaEngine, ExamplePredicates<FE>>::setup(
      &predicates,
      &*default_ck_hint(),
      &*default_ck_hint(),
    )
    .unwrap();
    let span_setup = span_setup_start.elapsed();

    let direct_new_start = Instant::now();
    let mut direct_snark = super::super::RecursiveSNARK::<
      PallasEngine,
      VestaEngine,
      ExamplePredicates<FE>,
    >::new(&direct_pp, &predicates, &z0, trace[0])
    .unwrap();
    let direct_new = direct_new_start.elapsed();

    let span_new_start = Instant::now();
    let mut span_snark = RecursiveSNARK::<PallasEngine, VestaEngine, ExamplePredicates<FE>>::new(
      &span_pp,
      &predicates,
      &z0,
      trace[0],
    )
    .unwrap();
    let span_new = span_new_start.elapsed();

    let direct_prove_start = Instant::now();
    for predicate_id in trace.iter().copied().skip(1) {
      direct_snark
        .prove_step(&direct_pp, &predicates, predicate_id)
        .unwrap();
    }
    let direct_prove = direct_prove_start.elapsed();

    let span_prove_start = Instant::now();
    for predicate_id in trace.iter().copied().skip(1) {
      span_snark
        .prove_step(&span_pp, &predicates, predicate_id)
        .unwrap();
    }
    let span_prove = span_prove_start.elapsed();

    let direct_verify_start = Instant::now();
    let direct_out = direct_snark
      .verify(&direct_pp, trace.len(), &z0, &trace)
      .unwrap();
    let direct_verify = direct_verify_start.elapsed();

    let span_verify_start = Instant::now();
    let span_out = span_snark
      .verify(&span_pp, trace.len(), &z0, &trace)
      .unwrap();
    let span_verify = span_verify_start.elapsed();

    assert_eq!(direct_out, span_out);

    eprintln!(
      "direct: setup={direct_setup:?} new={direct_new:?} prove={direct_prove:?} verify={direct_verify:?}"
    );
    eprintln!(
      "span:   setup={span_setup:?} new={span_new:?} prove={span_prove:?} verify={span_verify:?}"
    );
    eprintln!(
      "direct_primary_cons={} span_primary_cons={} direct_secondary_cons={} span_secondary_cons={}",
      direct_pp
        .structure_primary
        .predicates
        .iter()
        .map(|predicate| predicate.shape.num_cons)
        .max()
        .unwrap_or(0),
      span_pp
        .structure_primary
        .predicates
        .iter()
        .map(|predicate| predicate.shape.num_cons)
        .max()
        .unwrap_or(0),
      direct_pp.structure_secondary.predicates[0].shape.num_cons,
      span_pp.structure_secondary.predicates[0].shape.num_cons,
    );
  }
}
