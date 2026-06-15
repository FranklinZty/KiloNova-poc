//! Gadgets for the Holographic Folding `kilonova` augmented circuit.
use crate::{
  constants::NUM_CHALLENGE_BITS,
  frontend::{num::AllocatedNum, Assignment, Boolean, ConstraintSystem, SynthesisError},
  gadgets::{
    ecc::AllocatedPoint,
    utils::{alloc_one, alloc_zero, conditionally_select, le_bits_to_num},
  },
  r1cs::R1CSInstance,
  traits::{commitment::CommitmentTrait, Engine, ROCircuitTrait, ROConstantsCircuit},
};
use ff::Field;
use std::collections::BTreeMap;

use crate::kilonova::{
  nifs::{SumcheckProof, NIFS},
  relation::{FoldedInstance, GlobalStructure},
};

#[derive(Clone)]
pub struct AllocatedR1CSInstance<E: Engine> {
  pub(crate) comm_W: AllocatedPoint<E>,
  pub(crate) X: Vec<AllocatedNum<E::Base>>,
}

#[derive(Clone)]
pub struct AllocatedProjectedWitness<E: Engine> {
  pub(crate) W: Vec<AllocatedNum<E::Base>>,
}

#[derive(Clone)]
pub struct AllocatedIndexWitness<E: Engine> {
  pub(crate) lambda: Vec<AllocatedNum<E::Base>>,
}

#[derive(Clone)]
pub struct AllocatedFoldedInstance<E: Engine> {
  pub(crate) W: AllocatedPoint<E>,
  pub(crate) M: [AllocatedPoint<E>; 3],
  pub(crate) u: AllocatedNum<E::Base>,
  pub(crate) X: Vec<AllocatedNum<E::Base>>,
  pub(crate) r_x: Vec<AllocatedNum<E::Base>>,
  pub(crate) r_y: Vec<AllocatedNum<E::Base>>,
  pub(crate) v: Vec<AllocatedNum<E::Base>>,
}

pub struct AllocatedSumcheckProof<E: Engine> {
  pub(crate) point: Vec<AllocatedNum<E::Base>>,
  pub(crate) polys: Vec<Vec<AllocatedNum<E::Base>>>,
}

pub struct AllocatedNIFS<E: Engine> {
  pub(crate) sc_proof_x: AllocatedSumcheckProof<E>,
  pub(crate) sc_proof_y: AllocatedSumcheckProof<E>,
  pub(crate) sigmas: Vec<AllocatedNum<E::Base>>,
  pub(crate) taus: Vec<AllocatedNum<E::Base>>,
  pub(crate) epsilons: Vec<AllocatedNum<E::Base>>,
  pub(crate) thetas: Vec<AllocatedNum<E::Base>>,
}

fn alloc_num_vec<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  values: Option<&Vec<E::Base>>,
  len: usize,
  label: &str,
) -> Result<Vec<AllocatedNum<E::Base>>, SynthesisError> {
  (0..len)
    .map(|i| {
      AllocatedNum::alloc(cs.namespace(|| format!("{label}_{i}")), || {
        Ok(
          values
            .and_then(|v| v.get(i).copied())
            .unwrap_or(E::Base::ZERO),
        )
      })
    })
    .collect::<Result<Vec<_>, _>>()
}

fn assert_equal<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  a: &AllocatedNum<E::Base>,
  b: &AllocatedNum<E::Base>,
) {
  cs.enforce(
    || "assert equal",
    |lc| lc + CS::one(),
    |lc| lc + a.get_variable() - b.get_variable(),
    |lc| lc,
  );
}

fn add_const<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  a: &AllocatedNum<E::Base>,
  c: E::Base,
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  let out = AllocatedNum::alloc(cs.namespace(|| "add const"), || {
    Ok(*a.get_value().get()? + c)
  })?;
  cs.enforce(
    || "enforce add const",
    |lc| lc + CS::one(),
    |lc| lc + a.get_variable() + (c, CS::one()),
    |lc| lc + out.get_variable(),
  );
  Ok(out)
}

fn sub<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  a: &AllocatedNum<E::Base>,
  b: &AllocatedNum<E::Base>,
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  let out = AllocatedNum::alloc(cs.namespace(|| "sub"), || {
    Ok(*a.get_value().get()? - *b.get_value().get()?)
  })?;
  cs.enforce(
    || "enforce sub",
    |lc| lc + CS::one(),
    |lc| lc + a.get_variable() - b.get_variable(),
    |lc| lc + out.get_variable(),
  );
  Ok(out)
}

fn mul_const<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  a: &AllocatedNum<E::Base>,
  c: E::Base,
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  let out = AllocatedNum::alloc(cs.namespace(|| "mul const"), || {
    Ok(*a.get_value().get()? * c)
  })?;
  cs.enforce(
    || "enforce mul const",
    |lc| lc + a.get_variable(),
    |lc| lc + (c, CS::one()),
    |lc| lc + out.get_variable(),
  );
  Ok(out)
}

fn one_minus<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  a: &AllocatedNum<E::Base>,
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  let out = AllocatedNum::alloc(cs.namespace(|| "one_minus"), || {
    Ok(E::Base::ONE - *a.get_value().get()?)
  })?;
  cs.enforce(
    || "enforce one_minus",
    |lc| lc + CS::one(),
    |lc| lc + CS::one() - a.get_variable(),
    |lc| lc + out.get_variable(),
  );
  Ok(out)
}

fn eq_eval_bits<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  bits: &[bool],
  point: &[AllocatedNum<E::Base>],
  label: &str,
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  debug_assert_eq!(bits.len(), point.len());
  let mut acc = alloc_one(cs.namespace(|| format!("{label}_init")));
  for (i, (bit, r)) in bits.iter().zip(point.iter()).enumerate() {
    let term = if *bit {
      r.clone()
    } else {
      one_minus::<E, _>(cs.namespace(|| format!("{label}_one_minus_{i}")), r)?
    };
    acc = acc.mul(cs.namespace(|| format!("{label}_mul_{i}")), &term)?;
  }
  Ok(acc)
}

fn eq_points<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  left: &[AllocatedNum<E::Base>],
  right: &[AllocatedNum<E::Base>],
  label: &str,
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  debug_assert_eq!(left.len(), right.len());
  let mut acc = alloc_one(cs.namespace(|| format!("{label}_init")));
  for (i, (a, b)) in left.iter().zip(right.iter()).enumerate() {
    let ab = a.mul(cs.namespace(|| format!("{label}_ab_{i}")), b)?;
    let one_minus_a = one_minus::<E, _>(cs.namespace(|| format!("{label}_one_minus_a_{i}")), a)?;
    let one_minus_b = one_minus::<E, _>(cs.namespace(|| format!("{label}_one_minus_b_{i}")), b)?;
    let not_ab = one_minus_a.mul(cs.namespace(|| format!("{label}_not_ab_{i}")), &one_minus_b)?;
    let term = ab.add(cs.namespace(|| format!("{label}_term_{i}")), &not_ab)?;
    acc = acc.mul(cs.namespace(|| format!("{label}_acc_{i}")), &term)?;
  }
  Ok(acc)
}

fn powers<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  base: &AllocatedNum<E::Base>,
  count: usize,
  label: &str,
) -> Result<Vec<AllocatedNum<E::Base>>, SynthesisError> {
  let mut out = Vec::with_capacity(count);
  let mut cur = alloc_one(cs.namespace(|| format!("{label}_pow_0")));
  out.push(cur.clone());
  for i in 1..count {
    cur = cur.mul(cs.namespace(|| format!("{label}_pow_{i}")), base)?;
    out.push(cur.clone());
  }
  Ok(out)
}

fn eval_matrix_predicate<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  structure: &GlobalStructure<E>,
  predicate_id: usize,
  which: usize,
  r_x: &[AllocatedNum<E::Base>],
  r_y: &[AllocatedNum<E::Base>],
  label: &str,
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  let mut row_cache = BTreeMap::<usize, AllocatedNum<E::Base>>::new();
  let mut col_cache = BTreeMap::<usize, AllocatedNum<E::Base>>::new();
  let mut acc = alloc_zero(cs.namespace(|| format!("{label}_zero")));

  for (idx, (row, col, val)) in structure.predicates[predicate_id].mats[which]
    .iter()
    .enumerate()
  {
    let row_eval = if let Some(cached) = row_cache.get(row) {
      cached.clone()
    } else {
      let eval = eq_eval_bits::<E, _>(
        cs.namespace(|| format!("{label}_row_eval_{row}")),
        &GlobalStructure::<E>::bits_le(*row, structure.s_max),
        r_x,
        &format!("{label}_row_bits_{row}"),
      )?;
      row_cache.insert(*row, eval.clone());
      eval
    };
    let col_eval = if let Some(cached) = col_cache.get(col) {
      cached.clone()
    } else {
      let eval = eq_eval_bits::<E, _>(
        cs.namespace(|| format!("{label}_col_eval_{col}")),
        &GlobalStructure::<E>::bits_le(*col, structure.s_prime_max),
        r_y,
        &format!("{label}_col_bits_{col}"),
      )?;
      col_cache.insert(*col, eval.clone());
      eval
    };
    let eq = row_eval.mul(cs.namespace(|| format!("{label}_eq_{idx}")), &col_eval)?;
    let term = mul_const::<E, _>(cs.namespace(|| format!("{label}_scaled_{idx}")), &eq, *val)?;
    acc = acc.add(cs.namespace(|| format!("{label}_acc_{idx}")), &term)?;
  }

  Ok(acc)
}

fn eval_matrix_folded<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  structure: &GlobalStructure<E>,
  coeffs: &[AllocatedNum<E::Base>],
  which: usize,
  r_x: &[AllocatedNum<E::Base>],
  r_y: &[AllocatedNum<E::Base>],
  label: &str,
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  let mut acc = alloc_zero(cs.namespace(|| format!("{label}_zero")));
  for predicate_id in 0..structure.predicates.len() {
    let eval = eval_matrix_predicate::<E, _>(
      cs.namespace(|| format!("{label}_predicate_{predicate_id}")),
      structure,
      predicate_id,
      which,
      r_x,
      r_y,
      &format!("{label}_predicate_{predicate_id}"),
    )?;
    let term = coeffs[predicate_id].mul(
      cs.namespace(|| format!("{label}_coeff_mul_{predicate_id}")),
      &eval,
    )?;
    acc = acc.add(
      cs.namespace(|| format!("{label}_acc_{predicate_id}")),
      &term,
    )?;
  }
  Ok(acc)
}

fn eval_row_compression_predicate<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  structure: &GlobalStructure<E>,
  predicate_id: usize,
  which: usize,
  r_x: &[AllocatedNum<E::Base>],
  z: &[AllocatedNum<E::Base>],
  label: &str,
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  let mut row_cache = BTreeMap::<usize, AllocatedNum<E::Base>>::new();
  let mut acc = alloc_zero(cs.namespace(|| format!("{label}_zero")));

  for (idx, (row, col, val)) in structure.predicates[predicate_id].mats[which]
    .iter()
    .enumerate()
  {
    let row_eval = if let Some(cached) = row_cache.get(row) {
      cached.clone()
    } else {
      let eval = eq_eval_bits::<E, _>(
        cs.namespace(|| format!("{label}_row_eval_{row}")),
        &GlobalStructure::<E>::bits_le(*row, structure.s_max),
        r_x,
        &format!("{label}_row_bits_{row}"),
      )?;
      row_cache.insert(*row, eval.clone());
      eval
    };
    let scaled_row = mul_const::<E, _>(
      cs.namespace(|| format!("{label}_scaled_row_{idx}")),
      &row_eval,
      *val,
    )?;
    let z_col = if let Some(z_col) = z.get(*col) {
      z_col.clone()
    } else {
      alloc_zero(cs.namespace(|| format!("{label}_pad_z_{idx}")))
    };
    let term = scaled_row.mul(cs.namespace(|| format!("{label}_term_{idx}")), &z_col)?;
    acc = acc.add(cs.namespace(|| format!("{label}_acc_{idx}")), &term)?;
  }

  Ok(acc)
}

fn eval_z<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  z: &[AllocatedNum<E::Base>],
  r_y: &[AllocatedNum<E::Base>],
  s_prime_max: usize,
  label: &str,
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  let mut acc = alloc_zero(cs.namespace(|| format!("{label}_zero")));
  for (idx, value) in z.iter().enumerate() {
    let eq = eq_eval_bits::<E, _>(
      cs.namespace(|| format!("{label}_eq_{idx}")),
      &GlobalStructure::<E>::bits_le(idx, s_prime_max),
      r_y,
      &format!("{label}_bits_{idx}"),
    )?;
    let term = value.mul(cs.namespace(|| format!("{label}_term_{idx}")), &eq)?;
    acc = acc.add(cs.namespace(|| format!("{label}_acc_{idx}")), &term)?;
  }
  Ok(acc)
}

fn interpolate<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  evals: &[AllocatedNum<E::Base>],
  at: &AllocatedNum<E::Base>,
  points: &[E::Base],
) -> Result<AllocatedNum<E::Base>, SynthesisError> {
  let zero = alloc_zero(cs.namespace(|| "interp_zero"));
  let mut acc = zero;
  for i in 0..evals.len() {
    let mut num = alloc_one(cs.namespace(|| format!("interp_num_init_{i}")));
    let mut den = E::Base::ONE;
    for j in 0..evals.len() {
      if i != j {
        let shifted = add_const::<E, _>(
          cs.namespace(|| format!("interp_shift_{i}_{j}")),
          at,
          -points[j],
        )?;
        num = num.mul(cs.namespace(|| format!("interp_num_{i}_{j}")), &shifted)?;
        den *= points[i] - points[j];
      }
    }
    let den_inv = den.invert().unwrap();
    let basis = mul_const::<E, _>(cs.namespace(|| format!("interp_basis_{i}")), &num, den_inv)?;
    let term = basis.mul(cs.namespace(|| format!("interp_term_{i}")), &evals[i])?;
    acc = acc.add(cs.namespace(|| format!("interp_acc_{i}")), &term)?;
  }
  Ok(acc)
}

impl<E: Engine> AllocatedR1CSInstance<E> {
  pub fn alloc<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    u: Option<&R1CSInstance<E>>,
  ) -> Result<Self, SynthesisError> {
    let comm_W = AllocatedPoint::alloc(
      cs.namespace(|| "allocate comm_W"),
      u.map(|u| u.comm_W.to_coordinates()),
    )?;
    comm_W.check_on_curve(cs.namespace(|| "check comm_W on curve"))?;

    let X = (0..2)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("X_{i}")), || {
          Ok(crate::gadgets::utils::scalar_as_base::<E>(
            u.ok_or(SynthesisError::AssignmentMissing)?.X[i],
          ))
        })
      })
      .collect::<Result<Vec<_>, _>>()?;

    Ok(Self { comm_W, X })
  }

  pub fn absorb_in_ro(&self, ro: &mut E::ROCircuit) {
    ro.absorb(&self.comm_W.x);
    ro.absorb(&self.comm_W.y);
    ro.absorb(&self.comm_W.is_infinity);
    for x in &self.X {
      ro.absorb(x);
    }
  }
}

impl<E: Engine> AllocatedProjectedWitness<E> {
  pub fn alloc<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    witness: Option<&Vec<E::Base>>,
    num_vars: usize,
  ) -> Result<Self, SynthesisError> {
    let W = (0..num_vars)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("w_{i}")), || {
          Ok(
            witness
              .and_then(|w| w.get(i).copied())
              .unwrap_or(E::Base::ZERO),
          )
        })
      })
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self { W })
  }
}

impl<E: Engine> AllocatedIndexWitness<E> {
  pub fn alloc<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    lambda: Option<&Vec<E::Base>>,
    num_predicates: usize,
  ) -> Result<Self, SynthesisError> {
    let lambda = (0..num_predicates)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("lambda_{i}")), || {
          Ok(
            lambda
              .and_then(|v| v.get(i).copied())
              .unwrap_or(E::Base::ZERO),
          )
        })
      })
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self { lambda })
  }
}

impl<E: Engine> AllocatedFoldedInstance<E> {
  pub fn alloc<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    inst: Option<&FoldedInstance<E>>,
    structure: &GlobalStructure<E>,
  ) -> Result<Self, SynthesisError> {
    let W = AllocatedPoint::alloc(
      cs.namespace(|| "allocate W"),
      inst.map(|inst| inst.comm_W.to_coordinates()),
    )?;
    let M = core::array::from_fn(|j| {
      let point = AllocatedPoint::alloc(
        cs.namespace(|| format!("allocate M_{j}")),
        inst.map(|inst| inst.comm_M[j].to_coordinates()),
      )
      .unwrap();
      point
        .check_on_curve(cs.namespace(|| format!("check M_{j}")))
        .unwrap();
      point
    });
    let u = AllocatedNum::alloc(cs.namespace(|| "allocate u"), || {
      Ok(inst.map(|inst| inst.u).unwrap_or(E::Base::ZERO))
    })?;
    let X = (0..structure.num_io)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("X_{i}")), || {
          Ok(
            inst
              .and_then(|inst| inst.X.get(i).copied())
              .unwrap_or(E::Base::ZERO),
          )
        })
      })
      .collect::<Result<Vec<_>, _>>()?;
    let r_x = (0..structure.s_max)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("r_x_{i}")), || {
          Ok(
            inst
              .and_then(|inst| inst.r_x.get(i).copied())
              .unwrap_or(E::Base::ZERO),
          )
        })
      })
      .collect::<Result<Vec<_>, _>>()?;
    let r_y = (0..structure.s_prime_max)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("r_y_{i}")), || {
          Ok(
            inst
              .and_then(|inst| inst.r_y.get(i).copied())
              .unwrap_or(E::Base::ZERO),
          )
        })
      })
      .collect::<Result<Vec<_>, _>>()?;
    let v = (0..4)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("v_{i}")), || {
          Ok(
            inst
              .and_then(|inst| inst.v.get(i).copied())
              .unwrap_or(E::Base::ZERO),
          )
        })
      })
      .collect::<Result<Vec<_>, _>>()?;

    Ok(Self {
      W,
      M,
      u,
      X,
      r_x,
      r_y,
      v,
    })
  }

  pub fn default<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    structure: &GlobalStructure<E>,
  ) -> Result<Self, SynthesisError> {
    Self::alloc(
      cs.namespace(|| "default folded"),
      Some(&FoldedInstance::default(structure)),
      structure,
    )
  }

  pub fn from_r1cs_instance_witness<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    structure: &GlobalStructure<E>,
    predicate_id: usize,
    inst: &AllocatedR1CSInstance<E>,
    witness: &AllocatedProjectedWitness<E>,
  ) -> Result<Self, SynthesisError> {
    let u = alloc_one(cs.namespace(|| "one"));
    let r_x = (0..structure.s_max)
      .map(|i| alloc_zero(cs.namespace(|| format!("zero_rx_{i}"))))
      .collect::<Vec<_>>();
    let r_y = (0..structure.s_prime_max)
      .map(|i| alloc_zero(cs.namespace(|| format!("zero_ry_{i}"))))
      .collect::<Vec<_>>();
    let predicate = &structure.predicates[predicate_id];
    let m0 = mul_const::<E, _>(cs.namespace(|| "m0"), &u, predicate.matrix_at_zero[0])?;
    let m1 = mul_const::<E, _>(cs.namespace(|| "m1"), &u, predicate.matrix_at_zero[1])?;
    let m2 = mul_const::<E, _>(cs.namespace(|| "m2"), &u, predicate.matrix_at_zero[2])?;
    let z_eval = witness.W[0].clone();
    let M = core::array::from_fn(|j| {
      AllocatedPoint::alloc(
        cs.namespace(|| format!("base_M_{j}")),
        Some(structure.predicate_commitments(predicate_id)[j].to_coordinates()),
      )
      .unwrap()
    });

    Ok(Self {
      W: inst.comm_W.clone(),
      M,
      u,
      X: inst.X.clone(),
      r_x,
      r_y,
      v: vec![m0, m1, m2, z_eval],
    })
  }

  pub fn absorb_in_ro<CS: ConstraintSystem<E::Base>>(
    &self,
    mut cs: CS,
    ro: &mut E::ROCircuit,
  ) -> Result<(), SynthesisError> {
    self.W.check_on_curve(cs.namespace(|| "check W"))?;
    ro.absorb(&self.W.x);
    ro.absorb(&self.W.y);
    ro.absorb(&self.W.is_infinity);
    for (j, comm) in self.M.iter().enumerate() {
      comm.check_on_curve(cs.namespace(|| format!("check M_{j}")))?;
      ro.absorb(&comm.x);
      ro.absorb(&comm.y);
      ro.absorb(&comm.is_infinity);
    }
    ro.absorb(&self.u);
    for x in &self.X {
      ro.absorb(x);
    }
    for r in &self.r_x {
      ro.absorb(r);
    }
    for r in &self.r_y {
      ro.absorb(r);
    }
    for v in &self.v {
      ro.absorb(v);
    }
    Ok(())
  }

  #[allow(clippy::too_many_arguments)]
  pub fn fold_with_r1cs_holographic<CS: ConstraintSystem<E::Base>>(
    &self,
    mut cs: CS,
    params: &AllocatedNum<E::Base>,
    structure: &GlobalStructure<E>,
    predicate_id: usize,
    predicate_id_num: &AllocatedNum<E::Base>,
    u: &AllocatedR1CSInstance<E>,
    running_w: &AllocatedProjectedWitness<E>,
    running_lambda: &AllocatedIndexWitness<E>,
    incoming_w: &AllocatedProjectedWitness<E>,
    nifs: &AllocatedNIFS<E>,
    ro_consts: ROConstantsCircuit<E>,
  ) -> Result<Self, SynthesisError> {
    let expected_pred = AllocatedNum::alloc(cs.namespace(|| "expected_predicate_id"), || {
      Ok(E::Base::from(predicate_id as u64))
    })?;
    assert_equal::<E, _>(
      cs.namespace(|| "predicate_id_match"),
      predicate_id_num,
      &expected_pred,
    );

    let mut ro = E::ROCircuit::new(ro_consts);
    ro.absorb(params);
    ro.absorb(predicate_id_num);
    u.absorb_in_ro(&mut ro);
    let incoming_comm_M = structure.predicate_commitments(predicate_id);
    let incoming_points: [AllocatedPoint<E>; 3] = core::array::from_fn(|j| {
      AllocatedPoint::alloc(
        cs.namespace(|| format!("incoming_M_{j}")),
        Some(incoming_comm_M[j].to_coordinates()),
      )
      .unwrap()
    });
    for point in &incoming_points {
      ro.absorb(&point.x);
      ro.absorb(&point.y);
      ro.absorb(&point.is_infinity);
    }

    let gamma_bits = ro.squeeze(cs.namespace(|| "gamma_bits"), NUM_CHALLENGE_BITS)?;
    let gamma = le_bits_to_num(cs.namespace(|| "gamma"), &gamma_bits)?;
    let alpha = (0..structure.s_max)
      .map(|i| {
        let bits = ro.squeeze(
          cs.namespace(|| format!("alpha_bits_{i}")),
          NUM_CHALLENGE_BITS,
        )?;
        le_bits_to_num(cs.namespace(|| format!("alpha_{i}")), &bits)
      })
      .collect::<Result<Vec<_>, _>>()?;

    let gamma_pows = powers::<E, _>(cs.namespace(|| "gamma_pows"), &gamma, 4, "gamma")?;
    let gamma_sigma_1 = gamma_pows[1].mul(cs.namespace(|| "gamma_sigma_1"), &self.v[1])?;
    let gamma_sigma_2 = gamma_pows[2].mul(cs.namespace(|| "gamma_sigma_2"), &self.v[2])?;
    let expected_sum_x = self.v[0]
      .add(cs.namespace(|| "sum_x_0"), &gamma_sigma_1)?
      .add(cs.namespace(|| "sum_x_1"), &gamma_sigma_2)?;
    let mut claim_x =
      nifs.sc_proof_x.polys[0][0].add(cs.namespace(|| "claim_x"), &nifs.sc_proof_x.polys[0][1])?;
    assert_equal::<E, _>(cs.namespace(|| "sum_x_match"), &claim_x, &expected_sum_x);
    let eval_points_x = [
      E::Base::ZERO,
      E::Base::ONE,
      E::Base::from(2u64),
      E::Base::from(3u64),
    ];
    let mut r_x_point = Vec::with_capacity(structure.s_max);

    for (round, poly) in nifs.sc_proof_x.polys.iter().enumerate() {
      let sum01 = poly[0].add(cs.namespace(|| format!("sum01_x_{round}")), &poly[1])?;
      assert_equal::<E, _>(
        cs.namespace(|| format!("claim_x_eq_{round}")),
        &sum01,
        &claim_x,
      );
      for eval in poly {
        ro.absorb(eval);
      }
      let bits = ro.squeeze(
        cs.namespace(|| format!("rx_bits_{round}")),
        NUM_CHALLENGE_BITS,
      )?;
      let r = le_bits_to_num(cs.namespace(|| format!("rx_{round}")), &bits)?;
      claim_x = interpolate::<E, _>(
        cs.namespace(|| format!("interp_x_{round}")),
        poly,
        &r,
        &eval_points_x,
      )?;
      r_x_point.push(r);
    }
    for (i, (a, b)) in r_x_point
      .iter()
      .zip(nifs.sc_proof_x.point.iter())
      .enumerate()
    {
      assert_equal::<E, _>(cs.namespace(|| format!("rx_point_match_{i}")), a, b);
    }
    let r_x_prime = r_x_point.iter().cloned().rev().collect::<Vec<_>>();

    let mut z_running = Vec::with_capacity(running_w.W.len() + 1 + self.X.len());
    z_running.extend(running_w.W.iter().cloned());
    z_running.push(self.u.clone());
    z_running.extend(self.X.iter().cloned());
    let mut z_new = Vec::with_capacity(incoming_w.W.len() + 1 + u.X.len());
    z_new.extend(incoming_w.W.iter().cloned());
    z_new.push(alloc_one(cs.namespace(|| "z_new_one")));
    z_new.extend(u.X.iter().cloned());

    let sigmas = (0..3)
      .map(|j| {
        eval_matrix_folded::<E, _>(
          cs.namespace(|| format!("sigma_eval_{j}")),
          structure,
          &running_lambda.lambda,
          j,
          &r_x_prime,
          &self.r_y,
          &format!("sigma_eval_{j}"),
        )
      })
      .collect::<Result<Vec<_>, _>>()?;
    for (j, sigma) in sigmas.iter().enumerate() {
      assert_equal::<E, _>(
        cs.namespace(|| format!("sigma_match_{j}")),
        sigma,
        &nifs.sigmas[j],
      );
    }

    let taus = (0..3)
      .map(|j| {
        eval_row_compression_predicate::<E, _>(
          cs.namespace(|| format!("tau_eval_{j}")),
          structure,
          predicate_id,
          j,
          &r_x_prime,
          &z_new,
          &format!("tau_eval_{j}"),
        )
      })
      .collect::<Result<Vec<_>, _>>()?;
    for (j, tau) in taus.iter().enumerate() {
      assert_equal::<E, _>(
        cs.namespace(|| format!("tau_match_{j}")),
        tau,
        &nifs.taus[j],
      );
    }

    let eq_running_rx = eq_points::<E, _>(
      cs.namespace(|| "eq_running_rx"),
      &self.r_x,
      &r_x_prime,
      "eq_running_rx",
    )?;
    let eq_alpha = eq_points::<E, _>(cs.namespace(|| "eq_alpha"), &alpha, &r_x_prime, "eq_alpha")?;
    let sigma_gamma_1 = gamma_pows[1].mul(cs.namespace(|| "sigma_gamma_1"), &sigmas[1])?;
    let sigma_gamma_2 = gamma_pows[2].mul(cs.namespace(|| "sigma_gamma_2"), &sigmas[2])?;
    let sigma_acc = sigmas[0]
      .add(cs.namespace(|| "sigma_acc_0"), &sigma_gamma_1)?
      .add(cs.namespace(|| "sigma_acc_1"), &sigma_gamma_2)?;
    let cx_left = eq_running_rx.mul(cs.namespace(|| "cx_left"), &sigma_acc)?;
    let tau_prod = taus[0].mul(cs.namespace(|| "tau_prod"), &taus[1])?;
    let tau_diff = sub::<E, _>(cs.namespace(|| "tau_diff"), &tau_prod, &taus[2])?;
    let eq_alpha_tau = eq_alpha.mul(cs.namespace(|| "eq_alpha_tau"), &tau_diff)?;
    let cx_right = gamma_pows[3].mul(cs.namespace(|| "cx_right"), &eq_alpha_tau)?;
    let cx = cx_left.add(cs.namespace(|| "cx"), &cx_right)?;
    assert_equal::<E, _>(cs.namespace(|| "claim_x_match_cx"), &claim_x, &cx);

    let delta_bits = ro.squeeze(cs.namespace(|| "delta_bits"), NUM_CHALLENGE_BITS)?;
    let delta = le_bits_to_num(cs.namespace(|| "delta"), &delta_bits)?;
    let delta_pows = powers::<E, _>(cs.namespace(|| "delta_pows"), &delta, 7, "delta")?;
    let delta_sigma_1 = delta_pows[1].mul(cs.namespace(|| "delta_sigma_1"), &sigmas[1])?;
    let delta_sigma_2 = delta_pows[2].mul(cs.namespace(|| "delta_sigma_2"), &sigmas[2])?;
    let delta_v3 = delta_pows[3].mul(cs.namespace(|| "delta_v3"), &self.v[3])?;
    let delta_tau_0 = delta_pows[4].mul(cs.namespace(|| "delta_tau_0"), &taus[0])?;
    let delta_tau_1 = delta_pows[5].mul(cs.namespace(|| "delta_tau_1"), &taus[1])?;
    let delta_tau_2 = delta_pows[6].mul(cs.namespace(|| "delta_tau_2"), &taus[2])?;
    let expected_sum_y = sigmas[0]
      .add(cs.namespace(|| "sum_y_0"), &delta_sigma_1)?
      .add(cs.namespace(|| "sum_y_1"), &delta_sigma_2)?
      .add(cs.namespace(|| "sum_y_2"), &delta_v3)?
      .add(cs.namespace(|| "sum_y_3"), &delta_tau_0)?
      .add(cs.namespace(|| "sum_y_4"), &delta_tau_1)?
      .add(cs.namespace(|| "sum_y_5"), &delta_tau_2)?;
    let mut claim_y =
      nifs.sc_proof_y.polys[0][0].add(cs.namespace(|| "claim_y"), &nifs.sc_proof_y.polys[0][1])?;
    assert_equal::<E, _>(cs.namespace(|| "sum_y_match"), &claim_y, &expected_sum_y);

    let eval_points_y = [E::Base::ZERO, E::Base::ONE, E::Base::from(2u64)];
    let mut r_y_point = Vec::with_capacity(structure.s_prime_max);
    for (round, poly) in nifs.sc_proof_y.polys.iter().enumerate() {
      let sum01 = poly[0].add(cs.namespace(|| format!("sum01_y_{round}")), &poly[1])?;
      assert_equal::<E, _>(
        cs.namespace(|| format!("claim_y_eq_{round}")),
        &sum01,
        &claim_y,
      );
      for eval in poly {
        ro.absorb(eval);
      }
      let bits = ro.squeeze(
        cs.namespace(|| format!("ry_bits_{round}")),
        NUM_CHALLENGE_BITS,
      )?;
      let r = le_bits_to_num(cs.namespace(|| format!("ry_{round}")), &bits)?;
      claim_y = interpolate::<E, _>(
        cs.namespace(|| format!("interp_y_{round}")),
        poly,
        &r,
        &eval_points_y,
      )?;
      r_y_point.push(r);
    }
    for (i, (a, b)) in r_y_point
      .iter()
      .zip(nifs.sc_proof_y.point.iter())
      .enumerate()
    {
      assert_equal::<E, _>(cs.namespace(|| format!("ry_point_match_{i}")), a, b);
    }
    let r_y_prime = r_y_point.iter().cloned().rev().collect::<Vec<_>>();

    let mut epsilons = (0..3)
      .map(|j| {
        eval_matrix_folded::<E, _>(
          cs.namespace(|| format!("epsilon_eval_{j}")),
          structure,
          &running_lambda.lambda,
          j,
          &r_x_prime,
          &r_y_prime,
          &format!("epsilon_eval_{j}"),
        )
      })
      .collect::<Result<Vec<_>, _>>()?;
    epsilons.push(eval_z::<E, _>(
      cs.namespace(|| "epsilon_z"),
      &z_running,
      &r_y_prime,
      structure.s_prime_max,
      "epsilon_z",
    )?);
    for (j, epsilon) in epsilons.iter().enumerate() {
      assert_equal::<E, _>(
        cs.namespace(|| format!("epsilon_match_{j}")),
        epsilon,
        &nifs.epsilons[j],
      );
    }

    let mut thetas = (0..3)
      .map(|j| {
        eval_matrix_predicate::<E, _>(
          cs.namespace(|| format!("theta_eval_{j}")),
          structure,
          predicate_id,
          j,
          &r_x_prime,
          &r_y_prime,
          &format!("theta_eval_{j}"),
        )
      })
      .collect::<Result<Vec<_>, _>>()?;
    thetas.push(eval_z::<E, _>(
      cs.namespace(|| "theta_z"),
      &z_new,
      &r_y_prime,
      structure.s_prime_max,
      "theta_z",
    )?);
    for (j, theta) in thetas.iter().enumerate() {
      assert_equal::<E, _>(
        cs.namespace(|| format!("theta_match_{j}")),
        theta,
        &nifs.thetas[j],
      );
    }

    let eq_running_ry = eq_points::<E, _>(
      cs.namespace(|| "eq_running_ry"),
      &self.r_y,
      &r_y_prime,
      "eq_running_ry",
    )?;
    let eq_eps_0 = eq_running_ry.mul(cs.namespace(|| "eq_eps_0"), &epsilons[0])?;
    let eq_eps_1 = eq_running_ry.mul(cs.namespace(|| "eq_eps_1"), &epsilons[1])?;
    let eq_eps_2 = eq_running_ry.mul(cs.namespace(|| "eq_eps_2"), &epsilons[2])?;
    let eq_eps_3 = eq_running_ry.mul(cs.namespace(|| "eq_eps_3"), &epsilons[3])?;
    let cy_0 = delta_pows[0].mul(cs.namespace(|| "cy_0"), &eq_eps_0)?;
    let cy_1 = delta_pows[1].mul(cs.namespace(|| "cy_1"), &eq_eps_1)?;
    let cy_2 = delta_pows[2].mul(cs.namespace(|| "cy_2"), &eq_eps_2)?;
    let cy_3 = delta_pows[3].mul(cs.namespace(|| "cy_3"), &eq_eps_3)?;
    let theta_0z = thetas[0].mul(cs.namespace(|| "theta_0z"), &thetas[3])?;
    let theta_1z = thetas[1].mul(cs.namespace(|| "theta_1z"), &thetas[3])?;
    let theta_2z = thetas[2].mul(cs.namespace(|| "theta_2z"), &thetas[3])?;
    let cy_4 = delta_pows[4].mul(cs.namespace(|| "cy_4"), &theta_0z)?;
    let cy_5 = delta_pows[5].mul(cs.namespace(|| "cy_5"), &theta_1z)?;
    let cy_6 = delta_pows[6].mul(cs.namespace(|| "cy_6"), &theta_2z)?;
    let cy = cy_0
      .add(cs.namespace(|| "cy_acc_0"), &cy_1)?
      .add(cs.namespace(|| "cy_acc_1"), &cy_2)?
      .add(cs.namespace(|| "cy_acc_2"), &cy_3)?
      .add(cs.namespace(|| "cy_acc_3"), &cy_4)?
      .add(cs.namespace(|| "cy_acc_4"), &cy_5)?
      .add(cs.namespace(|| "cy_acc_5"), &cy_6)?;
    assert_equal::<E, _>(cs.namespace(|| "claim_y_match_cy"), &claim_y, &cy);

    let rho_bits = ro.squeeze(cs.namespace(|| "rho_bits"), NUM_CHALLENGE_BITS)?;
    let rho = le_bits_to_num(cs.namespace(|| "rho"), &rho_bits)?;
    let rW = u.comm_W.scalar_mul(cs.namespace(|| "rho_W"), &rho_bits)?;
    let W_fold = self.W.add(cs.namespace(|| "W_fold"), &rW)?;
    let M = core::array::from_fn(|j| {
      let term = incoming_points[j]
        .scalar_mul(cs.namespace(|| format!("rho_M_{j}")), &rho_bits)
        .unwrap();
      self.M[j]
        .add(cs.namespace(|| format!("M_fold_{j}")), &term)
        .unwrap()
    });
    let u_scaled = self.u.add(cs.namespace(|| "u_fold"), &rho)?;
    let X = self
      .X
      .iter()
      .zip(u.X.iter())
      .enumerate()
      .map(|(i, (x1, x2))| {
        let term = rho.mul(cs.namespace(|| format!("rho_x_{i}")), x2)?;
        x1.add(cs.namespace(|| format!("x_fold_{i}")), &term)
      })
      .collect::<Result<Vec<_>, _>>()?;
    let v = nifs
      .epsilons
      .iter()
      .zip(nifs.thetas.iter())
      .enumerate()
      .map(|(i, (a, b))| {
        let term = rho.mul(cs.namespace(|| format!("rho_theta_{i}")), b)?;
        a.add(cs.namespace(|| format!("v_fold_{i}")), &term)
      })
      .collect::<Result<Vec<_>, _>>()?;

    Ok(Self {
      W: W_fold,
      M,
      u: u_scaled,
      X,
      r_x: r_x_prime,
      r_y: r_y_prime,
      v,
    })
  }

  pub fn conditionally_select<CS: ConstraintSystem<E::Base>>(
    &self,
    mut cs: CS,
    other: &Self,
    condition: &Boolean,
  ) -> Result<Self, SynthesisError> {
    Ok(Self {
      W: AllocatedPoint::conditionally_select(
        cs.namespace(|| "W select"),
        &self.W,
        &other.W,
        condition,
      )?,
      M: core::array::from_fn(|j| {
        AllocatedPoint::conditionally_select(
          cs.namespace(|| format!("M select {j}")),
          &self.M[j],
          &other.M[j],
          condition,
        )
        .unwrap()
      }),
      u: conditionally_select(cs.namespace(|| "u select"), &self.u, &other.u, condition)?,
      X: self
        .X
        .iter()
        .zip(other.X.iter())
        .enumerate()
        .map(|(i, (a, b))| {
          conditionally_select(cs.namespace(|| format!("X select {i}")), a, b, condition)
        })
        .collect::<Result<Vec<_>, _>>()?,
      r_x: self
        .r_x
        .iter()
        .zip(other.r_x.iter())
        .enumerate()
        .map(|(i, (a, b))| {
          conditionally_select(cs.namespace(|| format!("rx select {i}")), a, b, condition)
        })
        .collect::<Result<Vec<_>, _>>()?,
      r_y: self
        .r_y
        .iter()
        .zip(other.r_y.iter())
        .enumerate()
        .map(|(i, (a, b))| {
          conditionally_select(cs.namespace(|| format!("ry select {i}")), a, b, condition)
        })
        .collect::<Result<Vec<_>, _>>()?,
      v: self
        .v
        .iter()
        .zip(other.v.iter())
        .enumerate()
        .map(|(i, (a, b))| {
          conditionally_select(cs.namespace(|| format!("v select {i}")), a, b, condition)
        })
        .collect::<Result<Vec<_>, _>>()?,
    })
  }
}

impl<E: Engine> AllocatedNIFS<E> {
  fn alloc_sumcheck_proof<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    proof: Option<&SumcheckProof<E>>,
    rounds: usize,
    eval_len: usize,
    label: &str,
  ) -> Result<AllocatedSumcheckProof<E>, SynthesisError> {
    let point = alloc_num_vec::<E, _>(
      cs.namespace(|| format!("{label}_point")),
      proof.map(|proof| &proof.point),
      rounds,
      &format!("{label}_point"),
    )?;
    let polys = (0..rounds)
      .map(|i| {
        (0..eval_len)
          .map(|j| {
            AllocatedNum::alloc(cs.namespace(|| format!("{label}_poly_{i}_{j}")), || {
              Ok(
                proof
                  .and_then(|proof| proof.polys.get(i))
                  .and_then(|poly| poly.get(j).copied())
                  .unwrap_or(E::Base::ZERO),
              )
            })
          })
          .collect::<Result<Vec<_>, _>>()
      })
      .collect::<Result<Vec<_>, _>>()?;
    Ok(AllocatedSumcheckProof { point, polys })
  }

  pub fn alloc<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    nifs: Option<&NIFS<E>>,
    structure: &GlobalStructure<E>,
  ) -> Result<Self, SynthesisError> {
    let sc_proof_x = Self::alloc_sumcheck_proof(
      cs.namespace(|| "proof_x"),
      nifs.map(|n| &n.sc_proof_x),
      structure.s_max,
      4,
      "x",
    )?;
    let sc_proof_y = Self::alloc_sumcheck_proof(
      cs.namespace(|| "proof_y"),
      nifs.map(|n| &n.sc_proof_y),
      structure.s_prime_max,
      3,
      "y",
    )?;
    let sigmas = alloc_num_vec::<E, _>(
      cs.namespace(|| "sigmas"),
      nifs.map(|n| &n.sigmas),
      3,
      "sigma",
    )?;
    let taus = alloc_num_vec::<E, _>(cs.namespace(|| "taus"), nifs.map(|n| &n.taus), 3, "tau")?;
    let epsilons =
      alloc_num_vec::<E, _>(cs.namespace(|| "eps"), nifs.map(|n| &n.epsilons), 4, "eps")?;
    let thetas = alloc_num_vec::<E, _>(
      cs.namespace(|| "thetas"),
      nifs.map(|n| &n.thetas),
      4,
      "theta",
    )?;
    Ok(Self {
      sc_proof_x,
      sc_proof_y,
      sigmas,
      taus,
      epsilons,
      thetas,
    })
  }
}
