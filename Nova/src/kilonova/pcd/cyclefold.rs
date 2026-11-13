//! Multi-input CycleFold circuit of the tree PCD and the native folds of tree CycleFold
//! accumulators (P6).
//!
//! One merge node performs one HFS v2 fold with μ running and ν incoming instances. Its E1
//! group operations are, with the shared 128-bit ρ,
//!
//! - `W_out = Σ_i ρ^i W_i` over the μ + ν witness commitments (running first),
//! - Direct only: `M_out[j] = Σ_{i<μ} ρ^i M_i[j] + Σ_{l<ν} ρ^{μ+l} ι_{k_l}[j]`, with every
//!   `ι_{k_l}` selected **inside** the circuit from the family constants.
//!
//! Both are evaluated by Horner's rule `P_0 + ρ(P_1 + ρ(P_2 + …))`, so only the 128-bit ρ is
//! ever a scalar (no ρ^i, which would not fit the circuit field). Public inputs, in order:
//! `ρ, [k_0..k_{ν−1}], W_0..W_{μ+ν−1}, W_out, then for each j: M_0[j]..M_{μ−1}[j], M_out[j]`.
//! For μ = ν = 1 the order equals the P5 circuit's (`ivc::cyclefold`).
//!
//! Tree CycleFold accumulators carry `u` as limbs (see `pcd::gadgets::CfAcc`); the native twins
//! here ([`cf_fold_relaxed_prove`], [`cf_fold_fresh_prove`]) use the same transcript.
use super::gadgets::{TAG_CF_FRESH, TAG_CF_RELAXED};
use crate::{
  constants::NUM_CHALLENGE_BITS,
  errors::NovaError,
  frontend::{
    num::AllocatedNum, solver::SatisfyingAssignment, AllocatedBit, ConstraintSystem,
    LinearCombination, SynthesisError,
  },
  gadgets::{
    ecc::AllocatedPoint,
    utils::{base_as_scalar, field_switch},
  },
  kilonova::ivc::{
    cyclefold::{Coords, CycleFoldCircuit},
    gadgets::{limbs_of, one_hot},
  },
  r1cs::{R1CSInstance, R1CSShape, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness},
  traits::{commitment::CommitmentEngineTrait, AbsorbInROTrait, Engine, ROConstants, ROTrait},
  Commitment, CommitmentKey,
};
use ff::{Field, PrimeFieldBits};

/// Witness values of one multi-input CycleFold step.
#[derive(Clone, Debug)]
pub struct CycleFoldInputsN<E1: Engine> {
  /// Fold challenge ρ (< 2^128).
  pub rho: E1::Scalar,
  /// Predicate ids of the ν incoming instances (Direct only; ignored for Span).
  pub ks: Vec<usize>,
  /// μ + ν witness commitments (running first).
  pub w: Vec<Coords<E1::Base>>,
  /// Folded witness commitment.
  pub w_out: Coords<E1::Base>,
  /// Per matrix j (Direct only): the μ running index commitments and the folded one.
  pub m: Vec<(Vec<Coords<E1::Base>>, Coords<E1::Base>)>,
}

/// The multi-input CycleFold circuit for a family of `iota.len()` predicates.
#[derive(Clone)]
pub struct CycleFoldCircuitN<'a, E1: Engine> {
  /// ι_k[j] coordinates; `iota.len()` = K.
  pub iota: &'a [Vec<Coords<E1::Base>>],
  /// Running inputs μ.
  pub mu: usize,
  /// Incoming inputs ν.
  pub nu: usize,
  /// Number of index RLCs (t for Direct, 0 for Span).
  pub t_idx: usize,
  /// Values (None when synthesizing the shape).
  pub inputs: Option<CycleFoldInputsN<E1>>,
}

/// Number of public inputs of the multi-input CycleFold circuit.
pub fn num_inputs_n(mu: usize, nu: usize, t_idx: usize) -> usize {
  let ks = if t_idx > 0 { nu } else { 0 };
  1 + ks + 2 * (mu + nu + 1) + t_idx * 2 * (mu + 1)
}

/// `Σ_i ρ^i P_i` by Horner's rule (`n − 1` scalar multiplications by the 128-bit ρ).
fn horner<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  points: &[AllocatedPoint<E>],
  bits: &[AllocatedBit],
) -> Result<AllocatedPoint<E>, SynthesisError> {
  let n = points.len();
  let mut acc = points[n - 1].clone();
  for i in (0..n - 1).rev() {
    let r = acc.scalar_mul(cs.namespace(|| format!("rho * acc{i}")), bits)?;
    acc = points[i].add(cs.namespace(|| format!("P{i} + rho acc")), &r)?;
  }
  Ok(acc)
}

impl<E1: Engine> CycleFoldCircuitN<'_, E1> {
  /// ι_{k}[j] selected from the constants by the one-hot bits of k.
  fn select_iota<CS: ConstraintSystem<E1::Base>>(
    &self,
    mut cs: CS,
    kb: &[AllocatedBit],
    j: usize,
  ) -> Result<AllocatedPoint<E1>, SynthesisError> {
    let fields: [fn(&Coords<E1::Base>) -> E1::Base; 3] = [
      |c| c.0,
      |c| c.1,
      |c| if c.2 { E1::Base::ONE } else { E1::Base::ZERO },
    ];
    let mut coords = Vec::with_capacity(3);
    for (n, f) in ["x", "y", "inf"].iter().zip(fields) {
      let val = kb
        .iter()
        .zip(self.iota)
        .try_fold(E1::Base::ZERO, |acc, (b, io)| {
          b.get_value()
            .map(|bit| if bit { acc + f(&io[j]) } else { acc })
        });
      let v = AllocatedNum::alloc(cs.namespace(|| format!("iota {n}")), || {
        val.ok_or(SynthesisError::AssignmentMissing)
      })?;
      cs.enforce(
        || format!("iota {n} = sum b_i c_i"),
        |lc| {
          kb.iter()
            .zip(self.iota)
            .fold(lc, |lc, (b, io)| lc + (f(&io[j]), b.get_variable()))
        },
        |lc| lc + CS::one(),
        |lc| lc + v.get_variable(),
      );
      coords.push(v);
    }
    Ok(AllocatedPoint {
      x: coords[0].clone(),
      y: coords[1].clone(),
      is_infinity: coords[2].clone(),
    })
  }

  /// Synthesizes the circuit.
  pub fn synthesize<CS: ConstraintSystem<E1::Base>>(
    &self,
    cs: &mut CS,
  ) -> Result<(), SynthesisError> {
    type C<'b, E> = CycleFoldCircuit<'b, E>;
    let (mu, nu) = (self.mu, self.nu);
    let k_family = self.iota.len();
    let inp = self.inputs.as_ref();
    if let Some(v) = inp {
      if v.w.len() != mu + nu || v.m.len() != self.t_idx || (self.t_idx > 0 && v.ks.len() != nu) {
        return Err(SynthesisError::IncompatibleLengthVector(
          "CycleFold inputs".into(),
        ));
      }
    }

    // Public inputs, in order.
    let rho_b = inp.map(|i| field_switch::<E1::Scalar, E1::Base>(i.rho));
    let rho = AllocatedNum::alloc_input(cs.namespace(|| "rho"), || {
      rho_b.ok_or(SynthesisError::AssignmentMissing)
    })?;
    let ks = if self.t_idx > 0 {
      (0..nu)
        .map(|l| {
          AllocatedNum::alloc_input(cs.namespace(|| format!("k{l}")), || {
            inp
              .map(|i| E1::Base::from(i.ks[l] as u64))
              .ok_or(SynthesisError::AssignmentMissing)
          })
        })
        .collect::<Result<Vec<_>, _>>()?
    } else {
      Vec::new()
    };
    let mut w_in = Vec::with_capacity(mu + nu + 1);
    for i in 0..mu + nu {
      w_in.push(C::<E1>::alloc_point_input(
        cs.namespace(|| format!("W{i}")),
        inp.map(|v| v.w[i]),
      )?);
    }
    w_in.push(C::<E1>::alloc_point_input(
      cs.namespace(|| "W_out"),
      inp.map(|v| v.w_out),
    )?);
    let mut m_in = Vec::with_capacity(self.t_idx);
    for j in 0..self.t_idx {
      let runs = (0..mu)
        .map(|i| {
          C::<E1>::alloc_point_input(
            cs.namespace(|| format!("M{i}_{j}")),
            inp.map(|v| v.m[j].0[i]),
          )
        })
        .collect::<Result<Vec<_>, _>>()?;
      let out =
        C::<E1>::alloc_point_input(cs.namespace(|| format!("M_out{j}")), inp.map(|v| v.m[j].1))?;
      m_in.push((runs, out));
    }

    // ρ < 2^128 as little-endian bits.
    let bits = (0..NUM_CHALLENGE_BITS)
      .map(|i| {
        AllocatedBit::alloc(
          cs.namespace(|| format!("rho bit {i}")),
          rho_b.map(|r| r.to_le_bits()[i]),
        )
      })
      .collect::<Result<Vec<_>, _>>()?;
    {
      let mut coeff = E1::Base::ONE;
      let mut lc = LinearCombination::zero();
      for b in &bits {
        lc = lc + (coeff, b.get_variable());
        coeff = coeff.double();
      }
      cs.enforce(
        || "rho = sum bits",
        |_| lc,
        |l| l + CS::one(),
        |l| l + rho.get_variable(),
      );
    }

    let w: Vec<AllocatedPoint<E1>> = w_in
      .iter()
      .enumerate()
      .map(|(i, p)| C::<E1>::to_point(cs.namespace(|| format!("W{i} point")), p))
      .collect::<Result<_, _>>()?;
    let w_fold = horner(cs.namespace(|| "W fold"), &w[..mu + nu], &bits)?;
    C::<E1>::enforce_equal(cs.namespace(|| "W_out check"), &w_fold, &w[mu + nu]);

    if self.t_idx > 0 {
      let kbs = ks
        .iter()
        .enumerate()
        .map(|(l, k)| one_hot(cs.namespace(|| format!("k{l} one-hot")), k, k_family))
        .collect::<Result<Vec<_>, _>>()?;
      for (j, (runs, out)) in m_in.iter().enumerate() {
        let mut cs = cs.namespace(|| format!("M{j}"));
        let mut pts = Vec::with_capacity(mu + nu);
        for (i, r) in runs.iter().enumerate() {
          pts.push(C::<E1>::to_point(
            cs.namespace(|| format!("run point {i}")),
            r,
          )?);
        }
        for (l, kb) in kbs.iter().enumerate() {
          pts.push(self.select_iota(cs.namespace(|| format!("iota {l}")), kb, j)?);
        }
        let out = C::<E1>::to_point(cs.namespace(|| "out point"), out)?;
        let fold = horner(cs.namespace(|| "fold"), &pts, &bits)?;
        C::<E1>::enforce_equal(cs.namespace(|| "M_out check"), &fold, &out);
      }
    }
    Ok(())
  }

  /// The public inputs for given values (the order of [`Self::synthesize`]).
  pub fn public_inputs(&self, v: &CycleFoldInputsN<E1>) -> Vec<E1::Base> {
    let mut x = vec![field_switch::<E1::Scalar, E1::Base>(v.rho)];
    if self.t_idx > 0 {
      x.extend(v.ks.iter().map(|k| E1::Base::from(*k as u64)));
    }
    for c in v.w.iter().chain(std::iter::once(&v.w_out)) {
      x.push(c.0);
      x.push(c.1);
    }
    for (runs, out) in &v.m {
      for c in runs.iter().chain(std::iter::once(out)) {
        x.push(c.0);
        x.push(c.1);
      }
    }
    x
  }
}

/// Synthesizes the witness of a multi-input CycleFold circuit and commits to it (no blinding).
pub fn cyclefold_instance_witness_n<E1, E2>(
  circuit: &CycleFoldCircuitN<'_, E1>,
  shape: &R1CSShape<E2>,
  ck: &CommitmentKey<E2>,
) -> Result<(R1CSInstance<E2>, R1CSWitness<E2>), NovaError>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  let mut cs = SatisfyingAssignment::<E2>::new();
  circuit.synthesize(&mut cs)?;
  let mut w = cs.aux_assignment().to_vec();
  if w.len() > shape.num_vars {
    return Err(NovaError::InvalidWitnessLength);
  }
  w.resize(shape.num_vars, E2::Scalar::ZERO);
  let x = cs.input_assignment()[1..].to_vec();
  let comm_w = E2::CE::commit(ck, &w, &E2::Scalar::ZERO);
  Ok((
    R1CSInstance {
      comm_W: comm_w,
      X: x,
    },
    R1CSWitness {
      W: w,
      r_W: E2::Scalar::ZERO,
    },
  ))
}

/// Absorbs a tree CycleFold accumulator: `W(x, y, inf), E(x, y, inf), u limbs, X limbs`
/// (the order of `CfAcc::absorb`).
pub fn absorb_acc<E2: Engine>(ro: &mut E2::RO, u: &RelaxedR1CSInstance<E2>) {
  u.comm_W.absorb_in_ro(ro);
  u.comm_E.absorb_in_ro(ro);
  for x in std::iter::once(&u.u).chain(&u.X) {
    for l in limbs_of::<E2::Scalar, E2::Base>(x) {
      ro.absorb(l);
    }
  }
}

/// `r = H(TAG_CF_RELAXED, pp, U1, U2, T)`.
pub fn cf_relaxed_challenge<E2: Engine>(
  ro_consts: &ROConstants<E2>,
  pp_digest: E2::Base,
  u1: &RelaxedR1CSInstance<E2>,
  u2: &RelaxedR1CSInstance<E2>,
  comm_t: &Commitment<E2>,
) -> E2::Scalar {
  let mut ro = E2::RO::new(ro_consts.clone());
  ro.absorb(E2::Base::from(TAG_CF_RELAXED));
  ro.absorb(pp_digest);
  absorb_acc(&mut ro, u1);
  absorb_acc(&mut ro, u2);
  comm_t.absorb_in_ro(&mut ro);
  base_as_scalar::<E2>(ro.squeeze(NUM_CHALLENGE_BITS))
}

/// `r = H(TAG_CF_FRESH, pp, U, u.W, u.X limbs, T)`.
pub fn cf_fresh_challenge<E2: Engine>(
  ro_consts: &ROConstants<E2>,
  pp_digest: E2::Base,
  big_u: &RelaxedR1CSInstance<E2>,
  u: &R1CSInstance<E2>,
  comm_t: &Commitment<E2>,
) -> E2::Scalar {
  let mut ro = E2::RO::new(ro_consts.clone());
  ro.absorb(E2::Base::from(TAG_CF_FRESH));
  ro.absorb(pp_digest);
  absorb_acc(&mut ro, big_u);
  u.comm_W.absorb_in_ro(&mut ro);
  for x in &u.X {
    for l in limbs_of::<E2::Scalar, E2::Base>(x) {
      ro.absorb(l);
    }
  }
  comm_t.absorb_in_ro(&mut ro);
  base_as_scalar::<E2>(ro.squeeze(NUM_CHALLENGE_BITS))
}

/// Folded accumulator, its witness and the cross-term commitment.
pub type CfFoldOut<E2> = (
  Commitment<E2>,
  RelaxedR1CSInstance<E2>,
  RelaxedR1CSWitness<E2>,
);

/// Relaxed–relaxed fold of `(u2, w2)` into `(u1, w1)`.
#[allow(clippy::too_many_arguments)]
pub fn cf_fold_relaxed_prove<E2: Engine>(
  ck: &CommitmentKey<E2>,
  ro_consts: &ROConstants<E2>,
  pp_digest: E2::Base,
  shape: &R1CSShape<E2>,
  u1: &RelaxedR1CSInstance<E2>,
  w1: &RelaxedR1CSWitness<E2>,
  u2: &RelaxedR1CSInstance<E2>,
  w2: &RelaxedR1CSWitness<E2>,
) -> Result<CfFoldOut<E2>, NovaError> {
  let (t, comm_t) = shape.commit_T_relaxed(ck, u1, w1, u2, w2, &E2::Scalar::ZERO)?;
  let r = cf_relaxed_challenge(ro_consts, pp_digest, u1, u2, &comm_t);
  Ok((
    comm_t,
    u1.fold_relaxed(u2, &comm_t, &r),
    w1.fold_relaxed(w2, &t, &E2::Scalar::ZERO, &r)?,
  ))
}

/// Fresh-instance fold of `(u, w)` into `(big_u, big_w)`.
#[allow(clippy::too_many_arguments)]
pub fn cf_fold_fresh_prove<E2: Engine>(
  ck: &CommitmentKey<E2>,
  ro_consts: &ROConstants<E2>,
  pp_digest: E2::Base,
  shape: &R1CSShape<E2>,
  big_u: &RelaxedR1CSInstance<E2>,
  big_w: &RelaxedR1CSWitness<E2>,
  u: &R1CSInstance<E2>,
  w: &R1CSWitness<E2>,
) -> Result<CfFoldOut<E2>, NovaError> {
  let (t, comm_t) = shape.commit_T(ck, big_u, big_w, u, w, &E2::Scalar::ZERO)?;
  let r = cf_fresh_challenge(ro_consts, pp_digest, big_u, u, &comm_t);
  Ok((
    comm_t,
    big_u.fold(u, &comm_t, &r),
    big_w.fold(w, &t, &E2::Scalar::ZERO, &r)?,
  ))
}
