//! CycleFold circuit and the native n-input Nova fold of its instances (P5, D1 option (a)).
//!
//! The circuit lives over `E1::Base = E2::Scalar`, where the coordinates of E1 points are
//! native. It performs the E1 group operations of one HFS v2 fold (μ = ν = 1) with one shared
//! 128-bit ρ:
//!
//! - `W_out = W_run + ρ·W_inc` (witness commitments),
//! - Direct only: `M_out[j] = M_run[j] + ρ·ι_k[j]` for j < t, with ι_k selected **inside** the
//!   circuit from the K family constants by a one-hot decomposition of the public k.
//!
//! Public inputs, in order: `ρ, [k], W_run.(x,y), W_inc.(x,y), W_out.(x,y), then for each j:
//! M_run[j].(x,y), M_out[j].(x,y)`. An input point `(0, 0)` is the identity (it is not on the
//! curve), so no infinity flag is public. The instance is committed on E2 and folded into a
//! running relaxed R1CS accumulator by the primary circuit (`gadgets::AllocatedRelaxedR1CSInstanceN`).
use super::gadgets::{limbs_of, TAG_CF_FOLD};
use crate::{
  constants::NUM_CHALLENGE_BITS,
  errors::NovaError,
  frontend::{
    num::AllocatedNum, solver::SatisfyingAssignment, AllocatedBit, ConstraintSystem, SynthesisError,
  },
  gadgets::{
    ecc::AllocatedPoint,
    utils::{base_as_scalar, field_switch},
  },
  r1cs::{R1CSInstance, R1CSShape, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness},
  traits::{commitment::CommitmentEngineTrait, AbsorbInROTrait, Engine, ROConstants, ROTrait},
  Commitment, CommitmentKey,
};
use ff::{Field, PrimeField, PrimeFieldBits};
use serde::{Deserialize, Serialize};

/// Affine coordinates `(x, y, is_infinity)` of an E1 point.
pub type Coords<B> = (B, B, bool);

/// Witness values of one CycleFold step.
#[derive(Clone, Debug)]
pub struct CycleFoldInputs<E1: Engine> {
  /// Fold challenge ρ (< 2^128).
  pub rho: E1::Scalar,
  /// Predicate id of the folded incoming instance (Direct only).
  pub k: usize,
  /// Running, incoming and folded witness commitments.
  pub w: [Coords<E1::Base>; 3],
  /// Running and folded index commitments, per matrix (Direct only).
  pub m: Vec<(Coords<E1::Base>, Coords<E1::Base>)>,
}

/// The CycleFold circuit for a family of `iota.len()` predicates and `t_idx` index RLCs
/// (`t` for Direct, 0 for Span).
#[derive(Clone)]
pub struct CycleFoldCircuit<'a, E1: Engine> {
  /// ι_k[j] coordinates; `iota.len()` = K, each of length t_idx.
  pub iota: &'a [Vec<Coords<E1::Base>>],
  /// Number of index RLCs.
  pub t_idx: usize,
  /// Values (None when synthesizing the shape).
  pub inputs: Option<CycleFoldInputs<E1>>,
}

/// Number of public inputs of the CycleFold circuit.
pub fn num_inputs(t_idx: usize) -> usize {
  if t_idx == 0 {
    7
  } else {
    8 + 4 * t_idx
  }
}

struct InPoint<F: PrimeField> {
  x: AllocatedNum<F>,
  y: AllocatedNum<F>,
}

impl<E1: Engine> CycleFoldCircuit<'_, E1> {
  fn alloc_point_input<CS: ConstraintSystem<E1::Base>>(
    mut cs: CS,
    c: Option<Coords<E1::Base>>,
  ) -> Result<InPoint<E1::Base>, SynthesisError> {
    let x = AllocatedNum::alloc_input(cs.namespace(|| "x"), || {
      c.map(|c| c.0).ok_or(SynthesisError::AssignmentMissing)
    })?;
    let y = AllocatedNum::alloc_input(cs.namespace(|| "y"), || {
      c.map(|c| c.1).ok_or(SynthesisError::AssignmentMissing)
    })?;
    Ok(InPoint { x, y })
  }

  /// `(x, y)` as an `AllocatedPoint` with a derived infinity bit: `b·x = b·y = 0` and the
  /// on-curve check unless `b`. Since `(0, 0)` is not on the curve, `b` is unique.
  fn to_point<CS: ConstraintSystem<E1::Base>>(
    mut cs: CS,
    p: &InPoint<E1::Base>,
  ) -> Result<AllocatedPoint<E1>, SynthesisError> {
    let inf = AllocatedNum::alloc(cs.namespace(|| "inf"), || {
      let (x, y) = (
        p.x.get_value().ok_or(SynthesisError::AssignmentMissing)?,
        p.y.get_value().ok_or(SynthesisError::AssignmentMissing)?,
      );
      Ok(if x.is_zero_vartime() && y.is_zero_vartime() {
        E1::Base::ONE
      } else {
        E1::Base::ZERO
      })
    })?;
    cs.enforce(
      || "inf is bit",
      |lc| lc + inf.get_variable(),
      |lc| lc + CS::one() - inf.get_variable(),
      |lc| lc,
    );
    for (n, c) in [("x", &p.x), ("y", &p.y)] {
      cs.enforce(
        || format!("inf * {n} = 0"),
        |lc| lc + inf.get_variable(),
        |lc| lc + c.get_variable(),
        |lc| lc,
      );
    }
    let pt = AllocatedPoint {
      x: p.x.clone(),
      y: p.y.clone(),
      is_infinity: inf,
    };
    pt.check_on_curve(cs.namespace(|| "on curve"))?;
    Ok(pt)
  }

  fn enforce_equal<CS: ConstraintSystem<E1::Base>>(
    mut cs: CS,
    a: &AllocatedPoint<E1>,
    b: &AllocatedPoint<E1>,
  ) {
    for (n, p, q) in [
      ("x", &a.x, &b.x),
      ("y", &a.y, &b.y),
      ("inf", &a.is_infinity, &b.is_infinity),
    ] {
      cs.enforce(
        || format!("{n} equal"),
        |lc| lc + p.get_variable() - q.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc,
      );
    }
  }

  /// Synthesizes the circuit.
  pub fn synthesize<CS: ConstraintSystem<E1::Base>>(
    &self,
    cs: &mut CS,
  ) -> Result<(), SynthesisError> {
    let k_family = self.iota.len();
    let inp = self.inputs.as_ref();

    // Public inputs, in order.
    let rho_b = inp.map(|i| field_switch::<E1::Scalar, E1::Base>(i.rho));
    let rho = AllocatedNum::alloc_input(cs.namespace(|| "rho"), || {
      rho_b.ok_or(SynthesisError::AssignmentMissing)
    })?;
    let k = if self.t_idx > 0 {
      Some(AllocatedNum::alloc_input(cs.namespace(|| "k"), || {
        inp
          .map(|i| E1::Base::from(i.k as u64))
          .ok_or(SynthesisError::AssignmentMissing)
      })?)
    } else {
      None
    };
    let names = ["W_run", "W_inc", "W_out"];
    let mut w_in = Vec::with_capacity(3);
    for (i, n) in names.iter().enumerate() {
      w_in.push(Self::alloc_point_input(
        cs.namespace(|| *n),
        inp.map(|v| v.w[i]),
      )?);
    }
    let mut m_in = Vec::with_capacity(self.t_idx);
    for j in 0..self.t_idx {
      let run =
        Self::alloc_point_input(cs.namespace(|| format!("M_run{j}")), inp.map(|v| v.m[j].0))?;
      let out =
        Self::alloc_point_input(cs.namespace(|| format!("M_out{j}")), inp.map(|v| v.m[j].1))?;
      m_in.push((run, out));
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
      let mut lc = crate::frontend::LinearCombination::zero();
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
      .zip(names)
      .map(|(p, n)| Self::to_point(cs.namespace(|| format!("{n} point")), p))
      .collect::<Result<_, _>>()?;
    let rw = w[1].scalar_mul(cs.namespace(|| "rho * W_inc"), &bits)?;
    let w_fold = w[0].add(cs.namespace(|| "W_run + rho W_inc"), &rw)?;
    Self::enforce_equal(cs.namespace(|| "W_out check"), &w_fold, &w[2]);

    if let Some(k) = k {
      let kb = super::gadgets::one_hot(cs.namespace(|| "k one-hot"), &k, k_family)?;
      for (j, (run, out)) in m_in.iter().enumerate() {
        let mut cs = cs.namespace(|| format!("M{j}"));
        // ι_k[j] = Σ_i b_i ι_i[j] (constants).
        let mut coords = Vec::with_capacity(3);
        for (n, f) in [
          (
            "x",
            (|c: &Coords<E1::Base>| c.0) as fn(&Coords<E1::Base>) -> E1::Base,
          ),
          ("y", |c: &Coords<E1::Base>| c.1),
          (
            "inf",
            |c: &Coords<E1::Base>| {
              if c.2 {
                E1::Base::ONE
              } else {
                E1::Base::ZERO
              }
            },
          ),
        ] {
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
        let iota = AllocatedPoint {
          x: coords[0].clone(),
          y: coords[1].clone(),
          is_infinity: coords[2].clone(),
        };
        let run = Self::to_point(cs.namespace(|| "run point"), run)?;
        let out = Self::to_point(cs.namespace(|| "out point"), out)?;
        let ri = iota.scalar_mul(cs.namespace(|| "rho * iota"), &bits)?;
        let fold = run.add(cs.namespace(|| "M_run + rho iota"), &ri)?;
        Self::enforce_equal(cs.namespace(|| "M_out check"), &fold, &out);
      }
    }
    Ok(())
  }

  /// The public inputs for given values (the order of [`Self::synthesize`]).
  pub fn public_inputs(&self, v: &CycleFoldInputs<E1>) -> Vec<E1::Base> {
    let mut x = vec![field_switch::<E1::Scalar, E1::Base>(v.rho)];
    if self.t_idx > 0 {
      x.push(E1::Base::from(v.k as u64));
    }
    for c in &v.w {
      x.push(c.0);
      x.push(c.1);
    }
    for (r, o) in &v.m {
      for c in [r, o] {
        x.push(c.0);
        x.push(c.1);
      }
    }
    x
  }
}

/// Synthesizes the CycleFold witness for `inputs` and commits to it (no blinding: the scheme is
/// not zero-knowledge). The instance's public inputs are the circuit's, so a caller that
/// builds `X` differently (the primary circuit does, from its own variables) gets an
/// unsatisfied instance.
pub fn cyclefold_instance_witness<E1, E2>(
  circuit: &CycleFoldCircuit<'_, E1>,
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

/// Proof of one CycleFold fold: the cross-term commitment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CycleFoldFoldProof<E2: Engine> {
  /// `Com(T)`.
  pub comm_t: Commitment<E2>,
}

/// The fold challenge `r = H(TAG_CF_FOLD, pp_digest, U, u, T)` over `E2::Base` (the order of
/// `AllocatedRelaxedR1CSInstanceN::fold_with_r1cs`).
pub fn cf_challenge<E2: Engine>(
  ro_consts: &ROConstants<E2>,
  pp_digest: E2::Base,
  big_u: &RelaxedR1CSInstance<E2>,
  u: &R1CSInstance<E2>,
  comm_t: &Commitment<E2>,
) -> E2::Scalar {
  let mut ro = E2::RO::new(ro_consts.clone());
  ro.absorb(E2::Base::from(TAG_CF_FOLD));
  ro.absorb(pp_digest);
  big_u.absorb_in_ro(&mut ro);
  u.comm_W.absorb_in_ro(&mut ro);
  for x in &u.X {
    for l in limbs_of::<E2::Scalar, E2::Base>(x) {
      ro.absorb(l);
    }
  }
  comm_t.absorb_in_ro(&mut ro);
  base_as_scalar::<E2>(ro.squeeze(NUM_CHALLENGE_BITS))
}

/// Folds `(u, w)` into `(U, W)` (Nova NIFS with the running instance absorbed).
#[allow(clippy::type_complexity)]
pub fn cf_fold_prove<E2: Engine>(
  ck: &CommitmentKey<E2>,
  ro_consts: &ROConstants<E2>,
  pp_digest: E2::Base,
  shape: &R1CSShape<E2>,
  big_u: &RelaxedR1CSInstance<E2>,
  big_w: &RelaxedR1CSWitness<E2>,
  u: &R1CSInstance<E2>,
  w: &R1CSWitness<E2>,
) -> Result<
  (
    CycleFoldFoldProof<E2>,
    RelaxedR1CSInstance<E2>,
    RelaxedR1CSWitness<E2>,
  ),
  NovaError,
> {
  let (t, comm_t) = shape.commit_T(ck, big_u, big_w, u, w, &E2::Scalar::ZERO)?;
  let r = cf_challenge(ro_consts, pp_digest, big_u, u, &comm_t);
  let u_new = big_u.fold(u, &comm_t, &r);
  let w_new = big_w.fold(w, &t, &E2::Scalar::ZERO, &r)?;
  Ok((CycleFoldFoldProof { comm_t }, u_new, w_new))
}

/// Verifier side of [`cf_fold_prove`].
pub fn cf_fold_verify<E2: Engine>(
  ro_consts: &ROConstants<E2>,
  pp_digest: E2::Base,
  big_u: &RelaxedR1CSInstance<E2>,
  u: &R1CSInstance<E2>,
  proof: &CycleFoldFoldProof<E2>,
) -> RelaxedR1CSInstance<E2> {
  let r = cf_challenge(ro_consts, pp_digest, big_u, u, &proof.comm_t);
  big_u.fold(u, &proof.comm_t, &r)
}
