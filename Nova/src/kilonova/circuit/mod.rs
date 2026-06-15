//! Augmented circuits for the Holographic Folding `kilonova` path.
use crate::{
  constants::NUM_HASH_BITS,
  frontend::{
    num::AllocatedNum, AllocatedBit, Assignment, Boolean, ConstraintSystem, SynthesisError,
  },
  gadgets::utils::{
    alloc_num_equals, alloc_scalar_as_base, alloc_zero, conditionally_select_vec, le_bits_to_num,
  },
  traits::{Engine, ROCircuitTrait, ROConstantsCircuit},
};
use ff::Field;
use serde::{Deserialize, Serialize};

use crate::kilonova::{
  nifs::NIFS,
  relation::{FoldedInstance, GlobalStructure},
  PredicateSet,
};
use crate::r1cs::R1CSInstance;

pub mod r1cs;
use r1cs::{
  AllocatedFoldedInstance, AllocatedIndexWitness, AllocatedNIFS, AllocatedProjectedWitness,
  AllocatedR1CSInstance,
};

#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct KiloNovaAugmentedCircuitInputs<E: Engine> {
  pp_digest: E::Scalar,
  i: E::Base,
  z0: Vec<E::Base>,
  zi: Option<Vec<E::Base>>,
  trace_digest_in: E::Base,
  local_predicate_id: E::Base,
  incoming_predicate_id: E::Base,
  U: Option<FoldedInstance<E>>,
  W: Option<Vec<E::Base>>,
  lambda: Option<Vec<E::Base>>,
  ri: Option<E::Base>,
  r_next: E::Base,
  u: Option<R1CSInstance<E>>,
  w: Option<Vec<E::Base>>,
  nifs: Option<NIFS<E>>,
}

impl<E: Engine> KiloNovaAugmentedCircuitInputs<E> {
  #[allow(clippy::too_many_arguments)]
  pub fn new(
    pp_digest: E::Scalar,
    i: E::Base,
    z0: Vec<E::Base>,
    zi: Option<Vec<E::Base>>,
    trace_digest_in: E::Base,
    local_predicate_id: E::Base,
    incoming_predicate_id: E::Base,
    U: Option<FoldedInstance<E>>,
    W: Option<Vec<E::Base>>,
    lambda: Option<Vec<E::Base>>,
    ri: Option<E::Base>,
    r_next: E::Base,
    u: Option<R1CSInstance<E>>,
    w: Option<Vec<E::Base>>,
    nifs: Option<NIFS<E>>,
  ) -> Self {
    Self {
      pp_digest,
      i,
      z0,
      zi,
      trace_digest_in,
      local_predicate_id,
      incoming_predicate_id,
      U,
      W,
      lambda,
      ri,
      r_next,
      u,
      w,
      nifs,
    }
  }
}

fn update_trace_digest_circuit<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  trace_digest_in: &AllocatedNum<E::Base>,
  predicate_id: &AllocatedNum<E::Base>,
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  let one = AllocatedNum::alloc(cs.namespace(|| "trace_one"), || Ok(E::Base::ONE))?;
  cs.enforce(
    || "enforce trace one",
    |lc| lc + CS::one(),
    |lc| lc + CS::one(),
    |lc| lc + one.get_variable(),
  );
  let delta = predicate_id.add(cs.namespace(|| "trace_delta"), &one)?;
  let shifted = trace_digest_in.add(cs.namespace(|| "trace_shifted"), &delta)?;
  let squared = shifted.square(cs.namespace(|| "trace_squared"))?;
  squared.add(cs.namespace(|| "trace_out"), &delta)
}

pub struct KiloNovaAugmentedCircuit<'a, E: Engine, PS: PredicateSet<E::Base>> {
  is_primary_circuit: bool,
  ro_consts: ROConstantsCircuit<E>,
  structure: GlobalStructure<E>,
  inputs: Option<KiloNovaAugmentedCircuitInputs<E>>,
  predicate_set: &'a PS,
  step_predicate_id: usize,
  incoming_predicate_id: usize,
}

impl<'a, E: Engine, PS: PredicateSet<E::Base>> KiloNovaAugmentedCircuit<'a, E, PS> {
  pub fn new(
    is_primary_circuit: bool,
    inputs: Option<KiloNovaAugmentedCircuitInputs<E>>,
    predicate_set: &'a PS,
    step_predicate_id: usize,
    incoming_predicate_id: usize,
    ro_consts: ROConstantsCircuit<E>,
    structure: GlobalStructure<E>,
  ) -> Self {
    Self {
      is_primary_circuit,
      ro_consts,
      structure,
      inputs,
      predicate_set,
      step_predicate_id,
      incoming_predicate_id,
    }
  }

  fn alloc_witness<CS: ConstraintSystem<E::Base>>(
    &self,
    mut cs: CS,
    arity: usize,
  ) -> Result<
    (
      AllocatedNum<E::Base>,
      AllocatedNum<E::Base>,
      Vec<AllocatedNum<E::Base>>,
      Vec<AllocatedNum<E::Base>>,
      AllocatedNum<E::Base>,
      AllocatedNum<E::Base>,
      AllocatedNum<E::Base>,
      AllocatedFoldedInstance<E>,
      AllocatedProjectedWitness<E>,
      AllocatedIndexWitness<E>,
      AllocatedNum<E::Base>,
      AllocatedNum<E::Base>,
      AllocatedR1CSInstance<E>,
      AllocatedProjectedWitness<E>,
      AllocatedNIFS<E>,
    ),
    SynthesisError,
  > {
    let pp_digest = alloc_scalar_as_base::<E, _>(
      cs.namespace(|| "pp_digest"),
      self.inputs.as_ref().map(|inputs| inputs.pp_digest),
    )?;
    let i = AllocatedNum::alloc(cs.namespace(|| "i"), || Ok(self.inputs.get()?.i))?;
    let z0 = (0..arity)
      .map(|idx| {
        AllocatedNum::alloc(cs.namespace(|| format!("z0_{idx}")), || {
          Ok(self.inputs.get()?.z0[idx])
        })
      })
      .collect::<Result<Vec<_>, _>>()?;
    let zero = vec![E::Base::ZERO; arity];
    let zi = (0..arity)
      .map(|idx| {
        AllocatedNum::alloc(cs.namespace(|| format!("zi_{idx}")), || {
          Ok(self.inputs.get()?.zi.as_ref().unwrap_or(&zero)[idx])
        })
      })
      .collect::<Result<Vec<_>, _>>()?;
    let trace_digest_in = AllocatedNum::alloc(cs.namespace(|| "trace_digest_in"), || {
      Ok(self.inputs.get()?.trace_digest_in)
    })?;
    let local_predicate_id = AllocatedNum::alloc(cs.namespace(|| "local_predicate_id"), || {
      Ok(self.inputs.get()?.local_predicate_id)
    })?;
    let incoming_predicate_id =
      AllocatedNum::alloc(cs.namespace(|| "incoming_predicate_id"), || {
        Ok(self.inputs.get()?.incoming_predicate_id)
      })?;
    let U = AllocatedFoldedInstance::alloc(
      cs.namespace(|| "allocate U"),
      self.inputs.as_ref().and_then(|inputs| inputs.U.as_ref()),
      &self.structure,
    )?;
    let W = AllocatedProjectedWitness::alloc(
      cs.namespace(|| "allocate W"),
      self.inputs.as_ref().and_then(|inputs| inputs.W.as_ref()),
      self.structure.num_vars_max,
    )?;
    let lambda = AllocatedIndexWitness::alloc(
      cs.namespace(|| "allocate lambda"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.lambda.as_ref()),
      self.structure.predicates.len(),
    )?;
    let ri = AllocatedNum::alloc(cs.namespace(|| "ri"), || {
      Ok(self.inputs.get()?.ri.unwrap_or(E::Base::ZERO))
    })?;
    let r_next = AllocatedNum::alloc(cs.namespace(|| "r_next"), || Ok(self.inputs.get()?.r_next))?;
    let u = AllocatedR1CSInstance::alloc(
      cs.namespace(|| "allocate u"),
      self.inputs.as_ref().and_then(|inputs| inputs.u.as_ref()),
    )?;
    let w = AllocatedProjectedWitness::alloc(
      cs.namespace(|| "allocate w"),
      self.inputs.as_ref().and_then(|inputs| inputs.w.as_ref()),
      self.structure.num_vars_max,
    )?;
    let nifs = AllocatedNIFS::alloc(
      cs.namespace(|| "allocate nifs"),
      self.inputs.as_ref().and_then(|inputs| inputs.nifs.as_ref()),
      &self.structure,
    )?;

    Ok((
      pp_digest,
      i,
      z0,
      zi,
      trace_digest_in,
      local_predicate_id,
      incoming_predicate_id,
      U,
      W,
      lambda,
      ri,
      r_next,
      u,
      w,
      nifs,
    ))
  }

  fn synthesize_hash_check<CS: ConstraintSystem<E::Base>>(
    &self,
    mut cs: CS,
    pp_digest: &AllocatedNum<E::Base>,
    i: &AllocatedNum<E::Base>,
    z0: &[AllocatedNum<E::Base>],
    zi: &[AllocatedNum<E::Base>],
    U: &AllocatedFoldedInstance<E>,
    ri: &AllocatedNum<E::Base>,
    trace_digest: &AllocatedNum<E::Base>,
  ) -> Result<AllocatedNum<E::Base>, SynthesisError> {
    let mut ro = E::ROCircuit::new(self.ro_consts.clone());
    ro.absorb(pp_digest);
    ro.absorb(i);
    for e in z0 {
      ro.absorb(e);
    }
    for e in zi {
      ro.absorb(e);
    }
    U.absorb_in_ro(cs.namespace(|| "absorb U"), &mut ro)?;
    ro.absorb(ri);
    ro.absorb(trace_digest);
    let hash_bits = ro.squeeze(cs.namespace(|| "input hash"), NUM_HASH_BITS)?;
    le_bits_to_num(cs.namespace(|| "hash"), &hash_bits)
  }

  fn synthesize_base_case<CS: ConstraintSystem<E::Base>>(
    &self,
    mut cs: CS,
    u: &AllocatedR1CSInstance<E>,
    w: &AllocatedProjectedWitness<E>,
  ) -> Result<AllocatedFoldedInstance<E>, SynthesisError> {
    if self.is_primary_circuit {
      AllocatedFoldedInstance::default(cs.namespace(|| "default U"), &self.structure)
    } else {
      AllocatedFoldedInstance::from_r1cs_instance_witness(
        cs.namespace(|| "from r1cs"),
        &self.structure,
        self.incoming_predicate_id,
        u,
        w,
      )
    }
  }

  #[allow(clippy::too_many_arguments)]
  fn synthesize_non_base_case<CS: ConstraintSystem<E::Base>>(
    &self,
    mut cs: CS,
    pp_digest: &AllocatedNum<E::Base>,
    incoming_predicate_id: &AllocatedNum<E::Base>,
    U: &AllocatedFoldedInstance<E>,
    W: &AllocatedProjectedWitness<E>,
    lambda: &AllocatedIndexWitness<E>,
    u: &AllocatedR1CSInstance<E>,
    w: &AllocatedProjectedWitness<E>,
    nifs: &AllocatedNIFS<E>,
  ) -> Result<AllocatedFoldedInstance<E>, SynthesisError> {
    U.fold_with_r1cs_holographic(
      cs.namespace(|| "holographic fold"),
      pp_digest,
      &self.structure,
      self.incoming_predicate_id,
      incoming_predicate_id,
      u,
      W,
      lambda,
      w,
      nifs,
      self.ro_consts.clone(),
    )
  }
}

impl<E: Engine, PS: PredicateSet<E::Base>> KiloNovaAugmentedCircuit<'_, E, PS> {
  pub fn synthesize<CS: ConstraintSystem<E::Base>>(
    self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<E::Base>>, SynthesisError> {
    let arity = self.predicate_set.arity();
    let (
      pp_digest,
      i,
      z0,
      zi,
      trace_digest_in,
      local_predicate_id,
      incoming_predicate_id,
      U,
      W,
      lambda,
      ri,
      r_next,
      u,
      w,
      nifs,
    ) = self.alloc_witness(cs.namespace(|| "allocate witness"), arity)?;

    let expected_local = AllocatedNum::alloc(cs.namespace(|| "expected_local_pred"), || {
      Ok(E::Base::from(self.step_predicate_id as u64))
    })?;
    let local_matches = alloc_num_equals(
      cs.namespace(|| "local_pred_match"),
      &local_predicate_id,
      &expected_local,
    )?;
    cs.enforce(
      || "enforce local predicate",
      |lc| lc + local_matches.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + CS::one(),
    );

    let zero = alloc_zero(cs.namespace(|| "zero"));
    let is_base_case = alloc_num_equals(cs.namespace(|| "is base"), &i, &zero)?;

    let hash = self.synthesize_hash_check(
      cs.namespace(|| "input hash"),
      &pp_digest,
      &i,
      &z0,
      &zi,
      &U,
      &ri,
      &trace_digest_in,
    )?;
    let check_hash = alloc_num_equals(cs.namespace(|| "u hash"), &u.X[0], &hash)?;

    let U_base = self.synthesize_base_case(cs.namespace(|| "base"), &u, &w)?;
    let U_non_base = self.synthesize_non_base_case(
      cs.namespace(|| "nonbase"),
      &pp_digest,
      &incoming_predicate_id,
      &U,
      &W,
      &lambda,
      &u,
      &w,
      &nifs,
    )?;

    let trace_selector = if self.is_primary_circuit {
      local_predicate_id.clone()
    } else {
      incoming_predicate_id.clone()
    };
    let trace_digest_out = update_trace_digest_circuit::<E, _>(
      cs.namespace(|| "trace_digest_out"),
      &trace_digest_in,
      &trace_selector,
    )?;

    let should_be_false =
      AllocatedBit::nor(cs.namespace(|| "hash_or_base"), &check_hash, &is_base_case)?;
    cs.enforce(
      || "hash or base",
      |lc| lc + should_be_false.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc,
    );

    let Unew = U_base.conditionally_select(
      cs.namespace(|| "select Unew"),
      &U_non_base,
      &Boolean::from(is_base_case.clone()),
    )?;

    let i_new = AllocatedNum::alloc(cs.namespace(|| "i_new"), || {
      Ok(*i.get_value().get()? + E::Base::ONE)
    })?;
    cs.enforce(
      || "i increment",
      |lc| lc + CS::one(),
      |lc| lc + i.get_variable() + CS::one(),
      |lc| lc + i_new.get_variable(),
    );

    let z_input = conditionally_select_vec(
      cs.namespace(|| "select z input"),
      &z0,
      &zi,
      &Boolean::from(is_base_case),
    )?;
    let z_next =
      self
        .predicate_set
        .synthesize(self.step_predicate_id, &mut cs.namespace(|| "F"), &z_input)?;

    let hash_out = self.synthesize_hash_check(
      cs.namespace(|| "output hash"),
      &pp_digest,
      &i_new,
      &z0,
      &z_next,
      &Unew,
      &r_next,
      &trace_digest_out,
    )?;

    u.X[1].inputize(cs.namespace(|| "other output"))?;
    hash_out.inputize(cs.namespace(|| "hash output"))?;
    Ok(z_next)
  }
}

#[cfg(test)]
mod tests {
  use crate::{
    frontend::{
      shape_cs::ShapeCS, solver::SatisfyingAssignment, test_cs::TestConstraintSystem,
      ConstraintSystem,
    },
    kilonova::test_utils::{
      build_direct_secondary_case, synthesize_secondary_direct, PrimaryBase, PrimaryEngine,
      SecondaryEngine,
    },
    traits::Engine,
  };
  use ff::Field;

  #[test]
  fn test_secondary_augmented_non_base_case_satisfiable() {
    let case = build_direct_secondary_case();

    let mut witness_cs = SatisfyingAssignment::<SecondaryEngine>::new();
    synthesize_secondary_direct(&case, &mut witness_cs).unwrap();

    let mut test_cs = TestConstraintSystem::<PrimaryBase>::new();
    synthesize_secondary_direct(&case, &mut test_cs).unwrap();
    assert!(
      test_cs.is_satisfied(),
      "direct circuit unsatisfied: {:?}",
      test_cs.which_is_unsatisfied()
    );

    let mut shape_cs = ShapeCS::<SecondaryEngine>::new();
    synthesize_secondary_direct(&case, &mut shape_cs).unwrap();
    assert!(shape_cs.num_constraints() > 0);
  }

  #[test]
  fn test_secondary_augmented_rejects_bad_hash() {
    let mut case = build_direct_secondary_case();
    case.u.X[0] += <PrimaryEngine as Engine>::Scalar::ONE;

    let mut test_cs = TestConstraintSystem::<PrimaryBase>::new();
    synthesize_secondary_direct(&case, &mut test_cs).unwrap();
    assert!(!test_cs.is_satisfied());
  }
}
