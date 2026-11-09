//! Primary augmented circuit of predicate k (P5), over `E1::Scalar`.
//!
//! Inputs are non-deterministic advice: the digests, the step counter, `z_0`, `z_i`, the trace
//! hash, the running ACCS `U_i`, the incoming CCCS `u_i` (predicate `k_prev`), the HFS v2
//! proof, the folded commitments as hints, the running CycleFold accumulator, the new
//! CycleFold instance's commitment and the cross term. The circuit:
//!
//! 1. checks `u_i.io[0] = H(TAG_LINK, pp, hfs, i, z_0, z_i, trace_i, U_i, cfU_i)` unless `i = 0`;
//! 2. verifies the HFS v2 fold of `(U_i, u_i)` natively (gadget, gated by `i ≠ 0`);
//! 3. builds the CycleFold instance's public inputs from ρ, `k_prev` and the limbs of the
//!    input and hinted points, and folds it into the CycleFold accumulator;
//! 4. outputs `U_{i+1}`, `cfU_{i+1}` (defaults when `i = 0`), `trace_{i+1} = H(TAG_TRACE,
//!    trace_i, k)` with **k a constant of this circuit**, `z_{i+1} = F_k(z_i)` (or `F_k(z_0)`),
//!    and the single public output `H(TAG_LINK, pp, hfs, i + 1, z_0, z_{i+1}, trace_{i+1},
//!    U_{i+1}, cfU_{i+1})`.
//!
//! It never reads another circuit's witness or a matrix (succinct).
use super::{
  cyclefold::Coords,
  gadgets::{
    alloc_constant, alloc_vec, cyclefold_inputs, one_hot, select_vec, verify_hfs, AllocIncoming,
    AllocIndex, AllocProof, AllocRunning, AllocatedRelaxedR1CSInstanceN, Expr, HfsGadgetParams,
    NnPoint,
  },
  IvcVariant, TAG_LINK, TAG_TRACE,
};
use crate::{
  constants::NUM_HASH_BITS,
  frontend::{num::AllocatedNum, AllocatedBit, Boolean, ConstraintSystem, SynthesisError},
  gadgets::{
    ecc::AllocatedPoint,
    utils::{alloc_num_equals, alloc_zero, conditionally_select, le_bits_to_num},
  },
  kilonova::{
    hfs::{CcsTemplate, HfsProof, IncomingInstance, RunningInstance},
    PredicateSet,
  },
  r1cs::RelaxedR1CSInstance,
  traits::{
    commitment::CommitmentTrait, Engine, RO2ConstantsCircuit, ROCircuitTrait, ROConstantsCircuit,
  },
  Commitment,
};
use ff::Field;

/// Public data that shapes the primary circuit.
#[derive(Clone)]
pub(crate) struct PrimaryParams<E1: Engine, E2: Engine> {
  pub(crate) template: CcsTemplate<E1::Scalar>,
  pub(crate) tag_input: u64,
  pub(crate) k: usize,
  pub(crate) s: usize,
  pub(crate) s_prime: usize,
  pub(crate) arity: usize,
  pub(crate) num_io: usize,
  pub(crate) direct: bool,
  /// ι_k[j] coordinates (K × t).
  pub(crate) iota: Vec<Vec<Coords<E1::Base>>>,
  pub(crate) n_cf: usize,
  pub(crate) ro2_consts: RO2ConstantsCircuit<E1>,
  pub(crate) ro_cf_consts: ROConstantsCircuit<E2>,
}

/// Witness values of one step.
#[derive(Clone)]
pub(crate) struct PrimaryInputs<E1: Engine, E2: Engine, V: IvcVariant<E1>> {
  pub(crate) pp_digest: E1::Scalar,
  pub(crate) hfs_digest: E1::Scalar,
  pub(crate) i: E1::Scalar,
  pub(crate) z0: Vec<E1::Scalar>,
  pub(crate) zi: Vec<E1::Scalar>,
  pub(crate) trace: E1::Scalar,
  pub(crate) run: RunningInstance<E1, V>,
  pub(crate) inc: IncomingInstance<E1>,
  pub(crate) proof: HfsProof<E1>,
  pub(crate) hint_w: Commitment<E1>,
  pub(crate) hint_m: Vec<Commitment<E1>>,
  pub(crate) cf_run: RelaxedR1CSInstance<E2>,
  pub(crate) cf_w: Commitment<E2>,
  pub(crate) cf_t: Commitment<E2>,
}

/// The primary augmented circuit of predicate `k`.
pub(crate) struct PrimaryCircuit<'a, E1: Engine, E2: Engine, PS, V: IvcVariant<E1>> {
  pub(crate) params: &'a PrimaryParams<E1, E2>,
  pub(crate) predicates: &'a PS,
  pub(crate) k: usize,
  pub(crate) inputs: Option<PrimaryInputs<E1, E2, V>>,
}

/// Link hash `H(TAG_LINK, pp, hfs, i, z_0, z_i, trace, U, cfU)` in the circuit.
#[allow(clippy::too_many_arguments)]
fn link_hash<E1, E2, CS>(
  mut cs: CS,
  consts: RO2ConstantsCircuit<E1>,
  pp: &AllocatedNum<E1::Scalar>,
  hfs: &AllocatedNum<E1::Scalar>,
  i: &AllocatedNum<E1::Scalar>,
  z0: &[AllocatedNum<E1::Scalar>],
  zi: &[AllocatedNum<E1::Scalar>],
  trace: &AllocatedNum<E1::Scalar>,
  run: &AllocRunning<E1::Scalar>,
  cf: &AllocatedRelaxedR1CSInstanceN<E2>,
) -> Result<AllocatedNum<E1::Scalar>, SynthesisError>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  CS: ConstraintSystem<E1::Scalar>,
{
  let mut ro = E1::RO2Circuit::new(consts);
  let tag = alloc_constant(cs.namespace(|| "tag"), E1::Scalar::from(TAG_LINK))?;
  ro.absorb(&tag);
  ro.absorb(pp);
  ro.absorb(hfs);
  ro.absorb(i);
  z0.iter().chain(zi).for_each(|z| ro.absorb(z));
  ro.absorb(trace);
  run.absorb(&mut ro);
  cf.absorb(&mut ro);
  let bits = ro.squeeze(cs.namespace(|| "squeeze"), NUM_HASH_BITS)?;
  le_bits_to_num(cs.namespace(|| "hash"), &bits)
}

impl<E1, E2, PS, V> PrimaryCircuit<'_, E1, E2, PS, V>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  PS: PredicateSet<E1::Scalar>,
  V: IvcVariant<E1>,
{
  fn alloc_running<CS: ConstraintSystem<E1::Scalar>>(
    &self,
    mut cs: CS,
  ) -> Result<AllocRunning<E1::Scalar>, SynthesisError> {
    let p = self.params;
    let t = p.template.t();
    let run = self.inputs.as_ref().map(|i| &i.run);
    let comm_w = NnPoint::alloc(
      cs.namespace(|| "comm_w"),
      run.map(|r| r.comm_w.to_coordinates()),
      false,
    )?;
    let index = if p.direct {
      let pts = run.map(|r| V::index_coords(&r.index));
      AllocIndex::Direct(
        (0..t)
          .map(|j| {
            NnPoint::alloc(
              cs.namespace(|| format!("M{j}")),
              pts.as_ref().map(|v| v[j]),
              false,
            )
          })
          .collect::<Result<_, _>>()?,
      )
    } else {
      let l = run.map(|r| V::index_scalars(&r.index));
      AllocIndex::Span(alloc_vec(cs.namespace(|| "lambda"), l.as_deref(), p.k)?)
    };
    let u = AllocatedNum::alloc(cs.namespace(|| "u"), || {
      Ok(run.map_or(E1::Scalar::ZERO, |r| r.u))
    })?;
    Ok(AllocRunning {
      comm_w,
      index,
      u,
      io: alloc_vec(cs.namespace(|| "io"), run.map(|r| &r.io[..]), p.num_io)?,
      r_x: alloc_vec(cs.namespace(|| "r_x"), run.map(|r| &r.r_x[..]), p.s)?,
      r_y: alloc_vec(cs.namespace(|| "r_y"), run.map(|r| &r.r_y[..]), p.s_prime)?,
      v: alloc_vec(cs.namespace(|| "v"), run.map(|r| &r.v[..]), t + 1)?,
    })
  }

  fn default_running<CS: ConstraintSystem<E1::Scalar>>(
    &self,
    mut cs: CS,
  ) -> Result<AllocRunning<E1::Scalar>, SynthesisError> {
    let p = self.params;
    let t = p.template.t();
    let zeros = |cs: &mut CS, n: &str, len: usize| {
      (0..len)
        .map(|i| alloc_constant(cs.namespace(|| format!("{n}{i}")), E1::Scalar::ZERO))
        .collect::<Result<Vec<_>, _>>()
    };
    let comm_w = NnPoint::identity(cs.namespace(|| "comm_w"))?;
    let index = if p.direct {
      AllocIndex::Direct(
        (0..t)
          .map(|j| NnPoint::identity(cs.namespace(|| format!("M{j}"))))
          .collect::<Result<_, _>>()?,
      )
    } else {
      AllocIndex::Span(zeros(&mut cs, "lambda", p.k)?)
    };
    Ok(AllocRunning {
      comm_w,
      index,
      u: alloc_constant(cs.namespace(|| "u"), E1::Scalar::ZERO)?,
      io: zeros(&mut cs, "io", p.num_io)?,
      r_x: zeros(&mut cs, "r_x", p.s)?,
      r_y: zeros(&mut cs, "r_y", p.s_prime)?,
      v: zeros(&mut cs, "v", t + 1)?,
    })
  }

  fn alloc_proof<CS: ConstraintSystem<E1::Scalar>>(
    &self,
    mut cs: CS,
  ) -> Result<AllocProof<E1::Scalar>, SynthesisError> {
    let p = self.params;
    let t = p.template.t();
    let pf = self.inputs.as_ref().map(|i| &i.proof);
    let rounds = |cs: &mut CS, n: &str, msgs: Option<&Vec<Vec<E1::Scalar>>>, r: usize, w: usize| {
      (0..r)
        .map(|i| {
          alloc_vec(
            cs.namespace(|| format!("{n}{i}")),
            msgs.map(|m| &m[i][..]),
            w,
          )
        })
        .collect::<Result<Vec<_>, _>>()
    };
    let sc_x = rounds(
      &mut cs,
      "sc_x",
      pf.map(|p| &p.sc_x),
      p.s,
      p.template.deg_x() + 1,
    )?;
    let sc_y = rounds(&mut cs, "sc_y", pf.map(|p| &p.sc_y), p.s_prime, 3)?;
    Ok(AllocProof {
      sc_x,
      sigma: alloc_vec(cs.namespace(|| "sigma"), pf.map(|p| &p.sigma[0][..]), t)?,
      tau: alloc_vec(cs.namespace(|| "tau"), pf.map(|p| &p.tau[0][..]), t)?,
      sc_y,
      eps: alloc_vec(cs.namespace(|| "eps"), pf.map(|p| &p.eps[0][..]), t + 1)?,
      theta: alloc_vec(cs.namespace(|| "theta"), pf.map(|p| &p.theta[0][..]), t + 1)?,
    })
  }

  /// Synthesizes the circuit; returns `z_{i+1}`.
  pub(crate) fn synthesize<CS: ConstraintSystem<E1::Scalar>>(
    &self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<E1::Scalar>>, SynthesisError> {
    let p = self.params;
    let t = p.template.t();
    let inp = self.inputs.as_ref();
    let scalar = |cs: &mut CS, n: &str, f: &dyn Fn(&PrimaryInputs<E1, E2, V>) -> E1::Scalar| {
      AllocatedNum::alloc(cs.namespace(|| n.to_string()), || {
        Ok(inp.map_or(E1::Scalar::ZERO, f))
      })
    };

    // Advice.
    let pp_digest = scalar(cs, "pp_digest", &|i| i.pp_digest)?;
    let hfs_digest = scalar(cs, "hfs_digest", &|i| i.hfs_digest)?;
    let i = scalar(cs, "i", &|i| i.i)?;
    let z0 = alloc_vec(cs.namespace(|| "z0"), inp.map(|i| &i.z0[..]), p.arity)?;
    let zi = alloc_vec(cs.namespace(|| "zi"), inp.map(|i| &i.zi[..]), p.arity)?;
    let trace = scalar(cs, "trace", &|i| i.trace)?;
    let run = self.alloc_running(cs.namespace(|| "U"))?;
    let inc = {
      let mut cs = cs.namespace(|| "u");
      let k = AllocatedNum::alloc(cs.namespace(|| "k_prev"), || {
        Ok(inp.map_or(E1::Scalar::ZERO, |i| E1::Scalar::from(i.inc.k as u64)))
      })?;
      let k_bits = one_hot(cs.namespace(|| "k_prev one-hot"), &k, p.k)?;
      let comm_w = NnPoint::alloc(
        cs.namespace(|| "comm_w"),
        inp.map(|i| i.inc.comm_w.to_coordinates()),
        true,
      )?;
      let io = alloc_vec(cs.namespace(|| "io"), inp.map(|i| &i.inc.io[..]), p.num_io)?;
      AllocIncoming {
        k,
        k_bits,
        comm_w,
        io,
      }
    };
    let proof = self.alloc_proof(cs.namespace(|| "proof"))?;
    let hint_w = NnPoint::alloc(
      cs.namespace(|| "hint W"),
      inp.map(|i| i.hint_w.to_coordinates()),
      true,
    )?;
    let hint_m = if p.direct {
      (0..t)
        .map(|j| {
          NnPoint::alloc(
            cs.namespace(|| format!("hint M{j}")),
            inp.map(|i| i.hint_m[j].to_coordinates()),
            true,
          )
        })
        .collect::<Result<Vec<_>, _>>()?
    } else {
      Vec::new()
    };
    let cf_run = AllocatedRelaxedR1CSInstanceN::<E2>::alloc(
      cs.namespace(|| "cfU"),
      inp.map(|i| &i.cf_run),
      p.n_cf,
    )?;
    let cf_w = AllocatedPoint::<E2>::alloc(
      cs.namespace(|| "cf comm_w"),
      inp.map(|i| i.cf_w.to_coordinates()),
    )?;
    cf_w.check_on_curve(cs.namespace(|| "cf comm_w on curve"))?;
    let cf_t = AllocatedPoint::<E2>::alloc(
      cs.namespace(|| "cf T"),
      inp.map(|i| i.cf_t.to_coordinates()),
    )?;
    cf_t.check_on_curve(cs.namespace(|| "cf T on curve"))?;

    // Base case.
    let zero = alloc_zero(cs.namespace(|| "zero"));
    let is_base = alloc_num_equals(cs.namespace(|| "is base"), &i, &zero)?;
    let base = Boolean::from(is_base.clone());
    let active = Expr::constant::<CS>(E1::Scalar::ONE).sub(&Expr::bit(&is_base));

    // 1. Link hash of the input state.
    let h_in = link_hash::<E1, E2, _>(
      cs.namespace(|| "input hash"),
      p.ro2_consts.clone(),
      &pp_digest,
      &hfs_digest,
      &i,
      &z0,
      &zi,
      &trace,
      &run,
      &cf_run,
    )?;
    let hash_ok = alloc_num_equals(cs.namespace(|| "u.io = H(state)"), &inc.io[0], &h_in)?;
    let fail = AllocatedBit::nor(cs.namespace(|| "hash ok nor base"), &hash_ok, &is_base)?;
    cs.enforce(
      || "hash ok or base",
      |lc| lc + fail.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc,
    );

    // 2. HFS v2 verifier.
    let gp = HfsGadgetParams {
      template: &p.template,
      tag_input: p.tag_input,
      s: p.s,
      iota: &p.iota,
    };
    let out = verify_hfs::<E1, _>(
      cs.namespace(|| "hfs"),
      &gp,
      p.ro2_consts.clone(),
      &hfs_digest,
      &run,
      &inc,
      &proof,
      &active,
    )?;
    let run_fold = AllocRunning {
      comm_w: hint_w.clone(),
      index: match &out.lambda {
        Some(l) => AllocIndex::Span(l.clone()),
        None => AllocIndex::Direct(hint_m.clone()),
      },
      u: out.u.clone(),
      io: out.io.clone(),
      r_x: out.r_x.clone(),
      r_y: out.r_y.clone(),
      v: out.v.clone(),
    };

    // 3. CycleFold instance and its fold.
    let m_pairs: Vec<(NnPoint<E1::Scalar>, NnPoint<E1::Scalar>)> = match &run.index {
      AllocIndex::Direct(m) => m.iter().cloned().zip(hint_m.iter().cloned()).collect(),
      AllocIndex::Span(_) => Vec::new(),
    };
    let x = cyclefold_inputs(
      &out.rho_bits,
      p.direct.then_some(&inc.k_bits[..]),
      [&run.comm_w, &inc.comm_w, &hint_w],
      &m_pairs,
    );
    debug_assert_eq!(x.len(), p.n_cf);
    let cf_fold = cf_run.fold_with_r1cs(
      cs.namespace(|| "cyclefold fold"),
      &pp_digest,
      &cf_w,
      &x,
      &cf_t,
      p.ro_cf_consts.clone(),
    )?;

    // 4. Outputs.
    let run_default = self.default_running(cs.namespace(|| "U default"))?;
    let run_new = AllocRunning::select(cs.namespace(|| "U new"), &run_default, &run_fold, &base)?;
    let cf_default =
      AllocatedRelaxedR1CSInstanceN::<E2>::default(cs.namespace(|| "cfU default"), p.n_cf)?;
    let cf_new = AllocatedRelaxedR1CSInstanceN::select(
      cs.namespace(|| "cfU new"),
      &cf_default,
      &cf_fold,
      &base,
    )?;
    let trace_in = conditionally_select(cs.namespace(|| "trace in"), &zero, &trace, &base)?;
    let trace_new = {
      let mut ro = E1::RO2Circuit::new(p.ro2_consts.clone());
      let tag = alloc_constant(cs.namespace(|| "trace tag"), E1::Scalar::from(TAG_TRACE))?;
      let k = alloc_constant(
        cs.namespace(|| "predicate id"),
        E1::Scalar::from(self.k as u64),
      )?;
      ro.absorb(&tag);
      ro.absorb(&trace_in);
      ro.absorb(&k);
      let bits = ro.squeeze(cs.namespace(|| "trace squeeze"), NUM_HASH_BITS)?;
      le_bits_to_num(cs.namespace(|| "trace hash"), &bits)?
    };
    let z_in = select_vec(cs.namespace(|| "z in"), &z0, &zi, &base)?;
    let z_next = self
      .predicates
      .synthesize(self.k, &mut cs.namespace(|| "F"), &z_in)?;
    if z_next.len() != p.arity {
      return Err(SynthesisError::IncompatibleLengthVector("z_next".into()));
    }
    let i_new = Expr::num(&i)
      .add(&Expr::constant::<CS>(E1::Scalar::ONE))
      .alloc(cs.namespace(|| "i + 1"))?;
    let h_out = link_hash::<E1, E2, _>(
      cs.namespace(|| "output hash"),
      p.ro2_consts.clone(),
      &pp_digest,
      &hfs_digest,
      &i_new,
      &z0,
      &z_next,
      &trace_new,
      &run_new,
      &cf_new,
    )?;
    h_out.inputize(cs.namespace(|| "output"))?;
    Ok(z_next)
  }
}
