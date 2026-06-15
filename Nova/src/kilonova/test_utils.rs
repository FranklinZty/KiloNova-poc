use crate::{
  constants::NUM_HASH_BITS,
  frontend::{
    num::AllocatedNum,
    r1cs::{NovaShape, NovaWitness},
    shape_cs::ShapeCS,
    solver::SatisfyingAssignment,
    ConstraintSystem, SynthesisError,
  },
  gadgets::utils::{base_as_scalar, scalar_as_base},
  kilonova::{
    circuit::{
      KiloNovaAugmentedCircuit as DirectCircuit, KiloNovaAugmentedCircuitInputs as DirectInputs,
    },
    nifs as direct_nifs, relation as direct_relation,
    span::{
      nifs as span_nifs, relation as span_relation, KiloNovaAugmentedCircuit as SpanCircuit,
      KiloNovaAugmentedCircuitInputs as SpanInputs, TrivialPredicateSet as SpanTrivialPredicateSet,
    },
    TrivialPredicateSet,
  },
  provider::{PallasEngine, VestaEngine},
  r1cs::{
    R1CSInstance, R1CSShape, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness, SparseMatrix,
  },
  spartan::snark::RelaxedR1CSSNARK,
  traits::{
    commitment::CommitmentEngineTrait,
    snark::{default_ck_hint, RelaxedR1CSSNARKTrait},
    AbsorbInROTrait, Engine, ROConstants, ROConstantsCircuit, ROTrait,
  },
  CE,
};
use ff::Field;

pub type CommitmentOf<E> = <<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment;
pub type CommitmentKeyOf<E> = <<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey;

pub(crate) type PrimaryEngine = PallasEngine;
pub(crate) type SecondaryEngine = VestaEngine;
pub(crate) type PrimaryBase = <PrimaryEngine as Engine>::Base;
pub(crate) type PrimaryScalar = <PrimaryEngine as Engine>::Scalar;
type BenchSnark =
  RelaxedR1CSSNARK<SecondaryEngine, crate::provider::ipa_pc::EvaluationEngine<SecondaryEngine>>;

#[derive(Clone)]
pub(crate) struct DirectSecondaryCase {
  pub(crate) structure: direct_relation::GlobalStructure<PrimaryEngine>,
  pub(crate) pp_digest: PrimaryScalar,
  pub(crate) i: PrimaryBase,
  pub(crate) z0: Vec<PrimaryBase>,
  pub(crate) zi: Vec<PrimaryBase>,
  pub(crate) trace_digest_in: PrimaryBase,
  pub(crate) local_predicate_id: PrimaryBase,
  pub(crate) incoming_predicate_id: usize,
  pub(crate) incoming_predicate_id_runtime: PrimaryBase,
  pub(crate) U: direct_relation::FoldedInstance<PrimaryEngine>,
  pub(crate) W_proj: Vec<PrimaryBase>,
  pub(crate) lambda: Vec<PrimaryBase>,
  pub(crate) ri: PrimaryBase,
  pub(crate) r_next: PrimaryBase,
  pub(crate) u: R1CSInstance<PrimaryEngine>,
  pub(crate) w_proj: Vec<PrimaryBase>,
  pub(crate) nifs: direct_nifs::NIFS<PrimaryEngine>,
  pub(crate) folded_u: direct_relation::FoldedInstance<PrimaryEngine>,
}

#[derive(Clone)]
pub(crate) struct SpanSecondaryCase {
  pub(crate) structure: span_relation::GlobalStructure<PrimaryEngine>,
  pub(crate) pp_digest: PrimaryScalar,
  pub(crate) i: PrimaryBase,
  pub(crate) z0: Vec<PrimaryBase>,
  pub(crate) zi: Vec<PrimaryBase>,
  pub(crate) trace_digest_in: PrimaryBase,
  pub(crate) local_predicate_id: PrimaryBase,
  pub(crate) incoming_predicate_id: usize,
  pub(crate) incoming_predicate_id_runtime: PrimaryBase,
  pub(crate) U: span_relation::FoldedInstance<PrimaryEngine>,
  pub(crate) W_proj: Vec<PrimaryBase>,
  pub(crate) ri: PrimaryBase,
  pub(crate) r_next: PrimaryBase,
  pub(crate) u: R1CSInstance<PrimaryEngine>,
  pub(crate) w_proj: Vec<PrimaryBase>,
  pub(crate) nifs: span_nifs::NIFS<PrimaryEngine>,
  pub(crate) folded_u: span_relation::FoldedInstance<PrimaryEngine>,
}

pub struct DirectSecondarySingleStepSnark {
  case: DirectSecondaryCase,
  shape: R1CSShape<SecondaryEngine>,
  ck: CommitmentKeyOf<SecondaryEngine>,
  relaxed_u: RelaxedR1CSInstance<SecondaryEngine>,
  relaxed_w: RelaxedR1CSWitness<SecondaryEngine>,
  num_constraints: usize,
  num_aux: usize,
  num_inputs: usize,
}

pub struct SpanSecondarySingleStepSnark {
  case: SpanSecondaryCase,
  shape: R1CSShape<SecondaryEngine>,
  ck: CommitmentKeyOf<SecondaryEngine>,
  relaxed_u: RelaxedR1CSInstance<SecondaryEngine>,
  relaxed_w: RelaxedR1CSWitness<SecondaryEngine>,
  expected_folded_index_commitments: [CommitmentOf<PrimaryEngine>; 3],
  num_constraints: usize,
  num_aux: usize,
  num_inputs: usize,
}

#[derive(Clone)]
struct TinyBaseData<E: Engine> {
  shapes: Vec<R1CSShape<E>>,
  ck: CommitmentKeyOf<E>,
  running_instance: R1CSInstance<E>,
  running_witness: R1CSWitness<E>,
  incoming_instance: R1CSInstance<E>,
  incoming_witness: R1CSWitness<E>,
  pp_digest: E::Scalar,
  i: E::Base,
  z0: Vec<E::Base>,
  zi: Vec<E::Base>,
  trace_digest_in: E::Base,
  ri: E::Base,
  r_next: E::Base,
}

fn tiny_nonuniform_base_data<E: Engine>(num_predicates: usize) -> TinyBaseData<E> {
  assert!(num_predicates >= 2);
  let zero = <E::Scalar as Field>::ZERO;
  let shape0 = R1CSShape::<E>::new(
    2,
    2,
    2,
    SparseMatrix::new(&vec![], 2, 5),
    SparseMatrix::new(&vec![], 2, 5),
    SparseMatrix::new(&vec![], 2, 5),
  )
  .unwrap();
  let shape1 = R1CSShape::<E>::new(
    4,
    4,
    2,
    SparseMatrix::new(&vec![], 4, 7),
    SparseMatrix::new(&vec![], 4, 7),
    SparseMatrix::new(&vec![], 4, 7),
  )
  .unwrap();
  let shapes = (0..num_predicates)
    .map(|idx| {
      if idx % 2 == 0 {
        shape0.clone()
      } else {
        shape1.clone()
      }
    })
    .collect::<Vec<_>>();
  let ck = shape1.commitment_key(&*default_ck_hint());

  let running_witness = R1CSWitness::<E> {
    W: vec![zero, zero],
    r_W: zero,
  };
  let running_instance = R1CSInstance::<E> {
    comm_W: CE::<E>::commit(&ck, &running_witness.W, &running_witness.r_W),
    X: vec![zero, zero],
  };

  let incoming_witness = R1CSWitness::<E> {
    W: vec![zero, zero, zero, zero],
    r_W: zero,
  };
  let incoming_instance = R1CSInstance::<E> {
    comm_W: CE::<E>::commit(&ck, &incoming_witness.W, &incoming_witness.r_W),
    X: vec![zero, zero],
  };

  TinyBaseData {
    shapes,
    ck,
    running_instance,
    running_witness,
    incoming_instance,
    incoming_witness,
    pp_digest: E::Scalar::from(42u64),
    i: E::Base::ONE,
    z0: vec![E::Base::ZERO],
    zi: vec![E::Base::ZERO],
    trace_digest_in: E::Base::from(3u64),
    ri: E::Base::from(7u64),
    r_next: E::Base::from(11u64),
  }
}

pub(crate) fn compute_augmented_input_hash<E: Engine, U: AbsorbInROTrait<E>>(
  ro_consts: &ROConstants<E>,
  pp_digest: E::Scalar,
  i: E::Base,
  z0: &[E::Base],
  zi: &[E::Base],
  U: &U,
  ri: E::Base,
  trace_digest_in: E::Base,
) -> E::Base {
  let mut ro = E::RO::new(ro_consts.clone());
  ro.absorb(scalar_as_base::<E>(pp_digest));
  ro.absorb(i);
  for value in z0 {
    ro.absorb(*value);
  }
  for value in zi {
    ro.absorb(*value);
  }
  U.absorb_in_ro(&mut ro);
  ro.absorb(ri);
  ro.absorb(trace_digest_in);
  ro.squeeze(NUM_HASH_BITS)
}

fn build_direct_secondary_case_with_predicates_inner(num_predicates: usize) -> DirectSecondaryCase {
  let base = tiny_nonuniform_base_data::<PrimaryEngine>(num_predicates);
  let incoming_predicate_id = num_predicates - 1;
  let structure = direct_relation::GlobalStructure::new(&base.shapes);
  let running_w =
    direct_relation::FoldedWitness::from_r1cs_witness(&structure, 0, &base.running_witness);
  let running_u = direct_relation::FoldedInstance::from_r1cs_instance_witness(
    &structure,
    0,
    &base.running_instance,
    &base.running_witness,
  );

  let ro_consts = ROConstants::<PrimaryEngine>::default();
  let input_hash = compute_augmented_input_hash(
    &ro_consts,
    base.pp_digest,
    base.i,
    &base.z0,
    &base.zi,
    &running_u,
    base.ri,
    base.trace_digest_in,
  );

  let mut incoming_u = base.incoming_instance.clone();
  incoming_u.X[0] = base_as_scalar::<PrimaryEngine>(input_hash);
  let (nifs, (folded_u, folded_w)) = direct_nifs::NIFS::prove(
    &base.ck,
    &ro_consts,
    &base.pp_digest,
    &structure,
    incoming_predicate_id,
    &running_u,
    &running_w,
    &incoming_u,
    &base.incoming_witness,
  )
  .unwrap();
  let verified_u = nifs
    .verify(
      &ro_consts,
      &base.pp_digest,
      &structure,
      incoming_predicate_id,
      &running_u,
      &incoming_u,
    )
    .unwrap();
  assert_eq!(folded_u, verified_u);
  assert!(structure.is_sat(&base.ck, &folded_u, &folded_w).is_ok());

  DirectSecondaryCase {
    structure: structure.clone(),
    pp_digest: base.pp_digest,
    i: base.i,
    z0: base.z0,
    zi: base.zi,
    trace_digest_in: base.trace_digest_in,
    local_predicate_id: PrimaryBase::ZERO,
    incoming_predicate_id,
    incoming_predicate_id_runtime: PrimaryBase::from(incoming_predicate_id as u64),
    U: running_u,
    W_proj: running_w.W_proj.clone(),
    lambda: running_w.lambda_proj.clone(),
    ri: base.ri,
    r_next: base.r_next,
    u: incoming_u,
    w_proj: structure.project_witness(&base.incoming_witness.W),
    nifs,
    folded_u,
  }
}

#[cfg(test)]
pub(crate) fn build_direct_secondary_case() -> DirectSecondaryCase {
  build_direct_secondary_case_with_predicates_inner(2)
}

fn build_span_secondary_case_with_predicates_inner(num_predicates: usize) -> SpanSecondaryCase {
  let base = tiny_nonuniform_base_data::<PrimaryEngine>(num_predicates);
  let incoming_predicate_id = num_predicates - 1;
  let structure = span_relation::GlobalStructure::new(&base.shapes);
  let running_w =
    span_relation::FoldedWitness::from_r1cs_witness(&structure, &base.running_witness);
  let running_u = span_relation::FoldedInstance::from_r1cs_instance_witness(
    &structure,
    0,
    &base.running_instance,
    &base.running_witness,
  );

  let ro_consts = ROConstants::<PrimaryEngine>::default();
  let input_hash = compute_augmented_input_hash(
    &ro_consts,
    base.pp_digest,
    base.i,
    &base.z0,
    &base.zi,
    &running_u,
    base.ri,
    base.trace_digest_in,
  );

  let mut incoming_u = base.incoming_instance.clone();
  incoming_u.X[0] = base_as_scalar::<PrimaryEngine>(input_hash);
  let (nifs, (folded_u, folded_w)) = span_nifs::NIFS::prove(
    &base.ck,
    &ro_consts,
    &base.pp_digest,
    &structure,
    incoming_predicate_id,
    &running_u,
    &running_w,
    &incoming_u,
    &base.incoming_witness,
  )
  .unwrap();
  let verified_u = nifs
    .verify(
      &ro_consts,
      &base.pp_digest,
      &structure,
      incoming_predicate_id,
      &running_u,
      &incoming_u,
    )
    .unwrap();
  assert_eq!(folded_u, verified_u);
  assert!(structure.is_sat(&base.ck, &folded_u, &folded_w).is_ok());

  SpanSecondaryCase {
    structure: structure.clone(),
    pp_digest: base.pp_digest,
    i: base.i,
    z0: base.z0,
    zi: base.zi,
    trace_digest_in: base.trace_digest_in,
    local_predicate_id: PrimaryBase::ZERO,
    incoming_predicate_id,
    incoming_predicate_id_runtime: PrimaryBase::from(incoming_predicate_id as u64),
    U: running_u,
    W_proj: running_w.W_proj.clone(),
    ri: base.ri,
    r_next: base.r_next,
    u: incoming_u,
    w_proj: structure.project_witness(&base.incoming_witness.W),
    nifs,
    folded_u,
  }
}

#[cfg(test)]
pub(crate) fn build_span_secondary_case() -> SpanSecondaryCase {
  build_span_secondary_case_with_predicates_inner(2)
}

pub(crate) fn synthesize_secondary_direct<CS: ConstraintSystem<PrimaryBase>>(
  case: &DirectSecondaryCase,
  cs: &mut CS,
) -> Result<Vec<AllocatedNum<PrimaryBase>>, SynthesisError> {
  let predicate_set = TrivialPredicateSet::<PrimaryBase>::default();
  let inputs = DirectInputs::new(
    case.pp_digest,
    case.i,
    case.z0.clone(),
    Some(case.zi.clone()),
    case.trace_digest_in,
    case.local_predicate_id,
    case.incoming_predicate_id_runtime,
    Some(case.U.clone()),
    Some(case.W_proj.clone()),
    Some(case.lambda.clone()),
    Some(case.ri),
    case.r_next,
    Some(case.u.clone()),
    Some(case.w_proj.clone()),
    Some(case.nifs.clone()),
  );
  let circuit: DirectCircuit<'_, PrimaryEngine, _> = DirectCircuit::new(
    false,
    Some(inputs),
    &predicate_set,
    0,
    case.incoming_predicate_id,
    ROConstantsCircuit::<PrimaryEngine>::default(),
    case.structure.clone(),
  );
  circuit.synthesize(cs)
}

pub(crate) fn synthesize_secondary_span<CS: ConstraintSystem<PrimaryBase>>(
  case: &SpanSecondaryCase,
  cs: &mut CS,
) -> Result<Vec<AllocatedNum<PrimaryBase>>, SynthesisError> {
  let predicate_set = SpanTrivialPredicateSet::<PrimaryBase>::default();
  let inputs = SpanInputs::new(
    case.pp_digest,
    case.i,
    case.z0.clone(),
    Some(case.zi.clone()),
    case.trace_digest_in,
    case.local_predicate_id,
    case.incoming_predicate_id_runtime,
    Some(case.U.clone()),
    Some(case.W_proj.clone()),
    Some(case.ri),
    case.r_next,
    Some(case.u.clone()),
    Some(case.w_proj.clone()),
    Some(case.nifs.clone()),
  );
  let circuit: SpanCircuit<'_, PrimaryEngine, _> = SpanCircuit::new(
    false,
    Some(inputs),
    &predicate_set,
    0,
    case.incoming_predicate_id,
    ROConstantsCircuit::<PrimaryEngine>::default(),
    case.structure.clone(),
  );
  circuit.synthesize(cs)
}

fn build_direct_secondary_single_step_snark_inner(
  num_predicates: usize,
) -> DirectSecondarySingleStepSnark {
  let case = build_direct_secondary_case_with_predicates_inner(num_predicates);

  let mut shape_cs = ShapeCS::<SecondaryEngine>::new();
  synthesize_secondary_direct(&case, &mut shape_cs).unwrap();
  let num_constraints = shape_cs.num_constraints();
  let num_aux = shape_cs.num_aux();
  let num_inputs = shape_cs.num_inputs();
  let (shape, _) = shape_cs.r1cs_shape(&*default_ck_hint());
  let ck = shape.pad().commitment_key(&*BenchSnark::ck_floor());

  let mut witness_cs = SatisfyingAssignment::<SecondaryEngine>::new();
  synthesize_secondary_direct(&case, &mut witness_cs).unwrap();
  let (u, w) = witness_cs.r1cs_instance_and_witness(&shape, &ck).unwrap();
  let relaxed_u = RelaxedR1CSInstance::from_r1cs_instance(&ck, &shape, &u);
  let relaxed_w = RelaxedR1CSWitness::from_r1cs_witness(&shape, &w);
  let (relaxed_w, blind_w, blind_e) = relaxed_w.derandomize();
  let relaxed_u = relaxed_u.derandomize(
    &<SecondaryEngine as Engine>::CE::derand_key(&ck),
    &blind_w,
    &blind_e,
  );

  DirectSecondarySingleStepSnark {
    case,
    shape,
    ck,
    relaxed_u,
    relaxed_w,
    num_constraints,
    num_aux,
    num_inputs,
  }
}

fn build_span_secondary_single_step_snark_inner(
  num_predicates: usize,
) -> SpanSecondarySingleStepSnark {
  let case = build_span_secondary_case_with_predicates_inner(num_predicates);

  let mut shape_cs = ShapeCS::<SecondaryEngine>::new();
  synthesize_secondary_span(&case, &mut shape_cs).unwrap();
  let num_constraints = shape_cs.num_constraints();
  let num_aux = shape_cs.num_aux();
  let num_inputs = shape_cs.num_inputs();
  let (shape, _) = shape_cs.r1cs_shape(&*default_ck_hint());
  let ck = shape.pad().commitment_key(&*BenchSnark::ck_floor());

  let mut witness_cs = SatisfyingAssignment::<SecondaryEngine>::new();
  synthesize_secondary_span(&case, &mut witness_cs).unwrap();
  let (u, w) = witness_cs.r1cs_instance_and_witness(&shape, &ck).unwrap();
  let relaxed_u = RelaxedR1CSInstance::from_r1cs_instance(&ck, &shape, &u);
  let relaxed_w = RelaxedR1CSWitness::from_r1cs_witness(&shape, &w);
  let (relaxed_w, blind_w, blind_e) = relaxed_w.derandomize();
  let relaxed_u = relaxed_u.derandomize(
    &<SecondaryEngine as Engine>::CE::derand_key(&ck),
    &blind_w,
    &blind_e,
  );
  let direct_shapes = case
    .structure
    .predicates
    .iter()
    .map(|predicate| predicate.shape.clone())
    .collect::<Vec<_>>();
  let direct_structure = direct_relation::GlobalStructure::new(&direct_shapes);
  let lambda_scalar = case
    .folded_u
    .lambda
    .iter()
    .copied()
    .map(base_as_scalar::<PrimaryEngine>)
    .collect::<Vec<_>>();
  let expected_folded_index_commitments = direct_structure.commit_index_coeffs(&lambda_scalar);

  SpanSecondarySingleStepSnark {
    case,
    shape,
    ck,
    relaxed_u,
    relaxed_w,
    expected_folded_index_commitments,
    num_constraints,
    num_aux,
    num_inputs,
  }
}

#[doc(hidden)]
pub fn build_direct_secondary_single_step_snark() -> DirectSecondarySingleStepSnark {
  build_direct_secondary_single_step_snark_inner(2)
}

#[doc(hidden)]
pub fn build_span_secondary_single_step_snark() -> SpanSecondarySingleStepSnark {
  build_span_secondary_single_step_snark_inner(2)
}

#[doc(hidden)]
pub fn build_direct_secondary_single_step_snark_with_predicates(
  num_predicates: usize,
) -> DirectSecondarySingleStepSnark {
  build_direct_secondary_single_step_snark_inner(num_predicates)
}

#[doc(hidden)]
pub fn build_span_secondary_single_step_snark_with_predicates(
  num_predicates: usize,
) -> SpanSecondarySingleStepSnark {
  build_span_secondary_single_step_snark_inner(num_predicates)
}

impl DirectSecondarySingleStepSnark {
  pub fn shape(&self) -> &R1CSShape<SecondaryEngine> {
    &self.shape
  }

  pub fn ck(&self) -> &CommitmentKeyOf<SecondaryEngine> {
    &self.ck
  }

  pub fn relaxed_instance(&self) -> &RelaxedR1CSInstance<SecondaryEngine> {
    &self.relaxed_u
  }

  pub fn relaxed_witness(&self) -> &RelaxedR1CSWitness<SecondaryEngine> {
    &self.relaxed_w
  }

  pub fn num_constraints(&self) -> usize {
    self.num_constraints
  }

  pub fn num_aux(&self) -> usize {
    self.num_aux
  }

  pub fn num_inputs(&self) -> usize {
    self.num_inputs
  }

  pub fn folded_index_commitments(&self) -> [CommitmentOf<PrimaryEngine>; 3] {
    self.case.folded_u.comm_M
  }
}

impl SpanSecondarySingleStepSnark {
  pub fn shape(&self) -> &R1CSShape<SecondaryEngine> {
    &self.shape
  }

  pub fn ck(&self) -> &CommitmentKeyOf<SecondaryEngine> {
    &self.ck
  }

  pub fn relaxed_instance(&self) -> &RelaxedR1CSInstance<SecondaryEngine> {
    &self.relaxed_u
  }

  pub fn relaxed_witness(&self) -> &RelaxedR1CSWitness<SecondaryEngine> {
    &self.relaxed_w
  }

  pub fn num_constraints(&self) -> usize {
    self.num_constraints
  }

  pub fn num_aux(&self) -> usize {
    self.num_aux
  }

  pub fn num_inputs(&self) -> usize {
    self.num_inputs
  }

  pub fn reconstruct_folded_index_commitments(&self) -> [CommitmentOf<PrimaryEngine>; 3] {
    self
      .case
      .structure
      .reconstruct_folded_index_commitments(&self.case.folded_u.lambda)
  }

  pub fn expected_folded_index_commitments(&self) -> [CommitmentOf<PrimaryEngine>; 3] {
    self.expected_folded_index_commitments
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    provider::ipa_pc::EvaluationEngine, spartan::snark::RelaxedR1CSSNARK,
    traits::snark::RelaxedR1CSSNARKTrait,
  };

  type S = RelaxedR1CSSNARK<SecondaryEngine, EvaluationEngine<SecondaryEngine>>;

  #[test]
  fn test_direct_secondary_single_step_snark_roundtrip() {
    let direct = build_direct_secondary_single_step_snark();
    let (pk, vk) = S::setup(direct.ck(), direct.shape()).unwrap();
    let proof = S::prove(
      direct.ck(),
      &pk,
      direct.shape(),
      direct.relaxed_instance(),
      direct.relaxed_witness(),
    )
    .unwrap();
    proof.verify(&vk, direct.relaxed_instance()).unwrap();
  }

  #[test]
  fn test_span_secondary_single_step_snark_roundtrip() {
    let span = build_span_secondary_single_step_snark();
    let (pk, vk) = S::setup(span.ck(), span.shape()).unwrap();
    let proof = S::prove(
      span.ck(),
      &pk,
      span.shape(),
      span.relaxed_instance(),
      span.relaxed_witness(),
    )
    .unwrap();
    proof.verify(&vk, span.relaxed_instance()).unwrap();
  }

  #[test]
  fn test_span_reconstructed_folded_commitments_match_direct() {
    let span = build_span_secondary_single_step_snark();
    assert_eq!(
      span.reconstruct_folded_index_commitments(),
      span.expected_folded_index_commitments()
    );
  }
}
