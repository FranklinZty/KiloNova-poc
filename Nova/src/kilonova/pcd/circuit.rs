//! Node circuits of the tree PCD (P6), over `E1::Scalar`. One family member per role:
//!
//! - **leaf k** (k < K_leaf): advice `(p, x_p)`; enforces `p < L`; `y = F_k(x_p)` (the P4 chain
//!   member k); statement `([p, p+1), β^p·y, H(TAG_LEAF, p, k, x_p))` with k a constant;
//!   accumulators are the defaults (base case, no verifier);
//! - **dummy**: advice `[lo, hi)`; enforces `lo ≥ L`, `hi > lo`; statement
//!   `([lo, hi), 0, H(TAG_DUMMY, lo, hi))`; default accumulators (base case);
//! - **merge**: a children `(S_c, U_c, u_c, cfU_c)`; checks every `u_c.io[0] = H_link(ctx, S_c,
//!   U_c, cfU_c)` under the **node's own** task context; enforces contiguous, ordered,
//!   equal-width ranges; verifies one HFS v2 fold of μ = a running and ν = a incoming instances
//!   (always active); folds the a CycleFold accumulators and the fresh CycleFold instance;
//!   outputs `([lo_0, hi_{a−1}), Σ r_c, H(TAG_NODE, lo, hi, h_0..h_{a−1}))`.
//!
//! Every member has one public output `H_link(pp, hfs, task_id, L, lo, hi, r, h, U, cfU)`. None
//! reads another circuit's witness or a matrix (succinct).
use super::{
  gadgets::{to_bits, verify_hfs_multi, AllocProofN, CfAcc},
  BETA, RANGE_BITS, TAG_TREE_DUMMY, TAG_TREE_LEAF, TAG_TREE_LINK, TAG_TREE_NODE,
};
use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_HASH_BITS},
  frontend::{
    num::AllocatedNum, AllocatedBit, ConstraintSystem, LinearCombination, SynthesisError,
  },
  gadgets::{
    ecc::AllocatedPoint,
    nonnative::{
      bignat::{BigNat, BigNatParams},
      util::f_to_nat,
    },
    utils::le_bits_to_num,
  },
  kilonova::{
    hfs::{CcsTemplate, HfsProof, IncomingInstance, RunningInstance},
    ivc::{
      cyclefold::Coords,
      gadgets::{
        alloc_constant, alloc_vec, bignat_of_bits, one_hot, AllocIncoming, AllocIndex,
        AllocRunning, Expr, HfsGadgetParams, NnPoint,
      },
      IvcVariant,
    },
    PredicateSet,
  },
  r1cs::RelaxedR1CSInstance,
  traits::{
    commitment::CommitmentTrait, Engine, RO2ConstantsCircuit, ROCircuitTrait, ROConstantsCircuit,
  },
  Commitment,
};
use ff::{Field, PrimeField, PrimeFieldBits};

/// Role of a family member.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeRole {
  /// Leaf running leaf predicate k.
  Leaf(usize),
  /// Internal node with a predecessors.
  Merge,
  /// Padding subtree beyond L.
  Dummy,
}

/// Public data that shapes the node circuits.
#[derive(Clone)]
pub(crate) struct NodeParams<E1: Engine, E2: Engine> {
  pub(crate) template: CcsTemplate<E1::Scalar>,
  pub(crate) tag_input: u64,
  /// Family size K = K_leaf + 2.
  pub(crate) k: usize,
  /// PCD arity a.
  pub(crate) a: usize,
  pub(crate) s: usize,
  pub(crate) s_prime: usize,
  /// Length of a leaf input and of a node result.
  pub(crate) arity: usize,
  pub(crate) num_io: usize,
  pub(crate) direct: bool,
  pub(crate) iota: Vec<Vec<Coords<E1::Base>>>,
  pub(crate) n_cf: usize,
  pub(crate) ro2_consts: RO2ConstantsCircuit<E1>,
  pub(crate) ro_cf_consts: ROConstantsCircuit<E2>,
}

/// Task context shared by every node of a tree.
#[derive(Clone, Debug)]
pub(crate) struct Ctx<F> {
  pub(crate) pp_digest: F,
  pub(crate) hfs_digest: F,
  pub(crate) task_id: F,
  pub(crate) num_leaves: u64,
}

/// One child of a merge node as seen by the parent.
#[derive(Clone)]
pub(crate) struct ChildIn<E1: Engine, E2: Engine, V: IvcVariant<E1>> {
  pub(crate) lo: u64,
  pub(crate) hi: u64,
  pub(crate) r: Vec<E1::Scalar>,
  pub(crate) h: E1::Scalar,
  pub(crate) run: RunningInstance<E1, V>,
  pub(crate) inc: IncomingInstance<E1>,
  pub(crate) cf: RelaxedR1CSInstance<E2>,
}

/// Role-specific witness values.
#[derive(Clone)]
pub(crate) enum RoleIn<E1: Engine, E2: Engine, V: IvcVariant<E1>> {
  Leaf {
    p: u64,
    x: Vec<E1::Scalar>,
  },
  Dummy {
    lo: u64,
    hi: u64,
  },
  Merge {
    children: Vec<ChildIn<E1, E2, V>>,
    proof: HfsProof<E1>,
    hint_w: Commitment<E1>,
    hint_m: Vec<Commitment<E1>>,
    cf_t_relaxed: Vec<Commitment<E2>>,
    cf_w: Commitment<E2>,
    cf_t: Commitment<E2>,
  },
}

/// Witness values of one node.
#[derive(Clone)]
pub(crate) struct NodeInputs<E1: Engine, E2: Engine, V: IvcVariant<E1>> {
  pub(crate) ctx: Ctx<E1::Scalar>,
  pub(crate) role: RoleIn<E1, E2, V>,
}

/// A node circuit.
pub(crate) struct NodeCircuit<'a, E1: Engine, E2: Engine, P, V: IvcVariant<E1>> {
  pub(crate) params: &'a NodeParams<E1, E2>,
  pub(crate) leaf: &'a P,
  pub(crate) role: NodeRole,
  pub(crate) inputs: Option<&'a NodeInputs<E1, E2, V>>,
}

struct CtxVars<F: PrimeField> {
  pp: AllocatedNum<F>,
  hfs: AllocatedNum<F>,
  task: AllocatedNum<F>,
  l: AllocatedNum<F>,
}

/// Poseidon over `E1::Scalar` of `tag ‖ xs`, `NUM_HASH_BITS` output.
fn hash<E1: Engine, CS: ConstraintSystem<E1::Scalar>>(
  mut cs: CS,
  consts: RO2ConstantsCircuit<E1>,
  tag: u64,
  xs: &[&AllocatedNum<E1::Scalar>],
) -> Result<AllocatedNum<E1::Scalar>, SynthesisError> {
  let mut ro = E1::RO2Circuit::new(consts);
  let t = alloc_constant(cs.namespace(|| "tag"), E1::Scalar::from(tag))?;
  ro.absorb(&t);
  xs.iter().for_each(|x| ro.absorb(x));
  let bits = ro.squeeze(cs.namespace(|| "squeeze"), NUM_HASH_BITS)?;
  le_bits_to_num(cs.namespace(|| "hash"), &bits)
}

/// The node link hash `H(TAG_LINK, pp, hfs, task_id, L, lo, hi, r, h, U, cfU)` in the circuit.
#[allow(clippy::too_many_arguments)]
fn link_hash<E1, E2, CS>(
  mut cs: CS,
  consts: RO2ConstantsCircuit<E1>,
  ctx: &CtxVars<E1::Scalar>,
  lo: &AllocatedNum<E1::Scalar>,
  hi: &AllocatedNum<E1::Scalar>,
  r: &[AllocatedNum<E1::Scalar>],
  h: &AllocatedNum<E1::Scalar>,
  run: &AllocRunning<E1::Scalar>,
  cf: &CfAcc<E2>,
) -> Result<AllocatedNum<E1::Scalar>, SynthesisError>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  CS: ConstraintSystem<E1::Scalar>,
{
  let mut ro = E1::RO2Circuit::new(consts);
  let tag = alloc_constant(cs.namespace(|| "tag"), E1::Scalar::from(TAG_TREE_LINK))?;
  ro.absorb(&tag);
  for x in [&ctx.pp, &ctx.hfs, &ctx.task, &ctx.l, lo, hi] {
    ro.absorb(x);
  }
  r.iter().for_each(|x| ro.absorb(x));
  ro.absorb(h);
  run.absorb(&mut ro);
  cf.absorb(&mut ro);
  let bits = ro.squeeze(cs.namespace(|| "squeeze"), NUM_HASH_BITS)?;
  le_bits_to_num(cs.namespace(|| "hash"), &bits)
}

/// The CycleFold public inputs as bignats, in the order of `CycleFoldCircuitN`:
/// `ρ, [k_l], W_i (running, incoming), W_out, (M_i[j], M_out[j])_j`.
fn cyclefold_inputs_n<F: PrimeField + PrimeFieldBits>(
  rho_bits: &[AllocatedBit],
  k_bits: &[&[AllocatedBit]],
  w: &[&NnPoint<F>],
  m: &[(Vec<&NnPoint<F>>, &NnPoint<F>)],
) -> Vec<BigNat<F>> {
  let mut out = vec![bignat_of_bits(rho_bits)];
  for kb in k_bits {
    // k = Σ i·b_i < 2^64: a single limb that is a linear combination of booleans.
    let mut lc = LinearCombination::zero();
    let mut val = Some(F::ZERO);
    for (i, b) in kb.iter().enumerate() {
      lc = lc + (F::from(i as u64), b.get_variable());
      val = val
        .zip(b.get_value())
        .map(|(v, bit)| if bit { v + F::from(i as u64) } else { v });
    }
    let mut limbs = vec![lc];
    limbs.extend((1..BN_N_LIMBS).map(|_| LinearCombination::zero()));
    let limb_values = val.map(|v| {
      let mut vs = vec![v];
      vs.extend((1..BN_N_LIMBS).map(|_| F::ZERO));
      vs
    });
    out.push(BigNat {
      value: val.map(|v| f_to_nat(&v)),
      limb_values,
      limbs,
      params: BigNatParams::new(BN_LIMB_WIDTH, BN_N_LIMBS),
    });
  }
  let mut push = |p: &NnPoint<F>| {
    let (x, y) = p.coords_bignat();
    out.push(x);
    out.push(y);
  };
  w.iter().for_each(|p| push(p));
  for (runs, o) in m {
    runs.iter().for_each(|p| push(p));
    push(o);
  }
  out
}

/// Allocates `r` rows of `w` values each.
fn alloc_rows<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  v: Option<&Vec<Vec<F>>>,
  r: usize,
  w: usize,
) -> Result<Vec<Vec<AllocatedNum<F>>>, SynthesisError> {
  (0..r)
    .map(|i| alloc_vec(cs.namespace(|| format!("{i}")), v.map(|v| &v[i][..]), w))
    .collect()
}

impl<E1, E2, P, V> NodeCircuit<'_, E1, E2, P, V>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  P: PredicateSet<E1::Scalar>,
  V: IvcVariant<E1>,
{
  fn alloc_ctx<CS: ConstraintSystem<E1::Scalar>>(
    &self,
    mut cs: CS,
  ) -> Result<CtxVars<E1::Scalar>, SynthesisError> {
    let c = self.inputs.map(|i| &i.ctx);
    let mut a = |n: &str, f: &dyn Fn(&Ctx<E1::Scalar>) -> E1::Scalar| {
      AllocatedNum::alloc(cs.namespace(|| n.to_string()), || {
        Ok(c.map_or(E1::Scalar::ZERO, f))
      })
    };
    Ok(CtxVars {
      pp: a("pp_digest", &|c| c.pp_digest)?,
      hfs: a("hfs_digest", &|c| c.hfs_digest)?,
      task: a("task_id", &|c| c.task_id)?,
      l: a("L", &|c| E1::Scalar::from(c.num_leaves))?,
    })
  }

  fn alloc_running<CS: ConstraintSystem<E1::Scalar>>(
    &self,
    mut cs: CS,
    run: Option<&RunningInstance<E1, V>>,
  ) -> Result<AllocRunning<E1::Scalar>, SynthesisError> {
    let p = self.params;
    let t = p.template.t();
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
    let zero = alloc_constant(cs.namespace(|| "zero"), E1::Scalar::ZERO)?;
    let zeros = |n: usize| vec![zero.clone(); n];
    let index = if p.direct {
      AllocIndex::Direct(
        (0..t)
          .map(|j| NnPoint::identity(cs.namespace(|| format!("M{j}"))))
          .collect::<Result<_, _>>()?,
      )
    } else {
      AllocIndex::Span(zeros(p.k))
    };
    Ok(AllocRunning {
      comm_w: NnPoint::identity(cs.namespace(|| "comm_w"))?,
      index,
      u: zero.clone(),
      io: zeros(p.num_io),
      r_x: zeros(p.s),
      r_y: zeros(p.s_prime),
      v: zeros(t + 1),
    })
  }

  /// Output of a base-case node (leaf or dummy): the link hash with default accumulators.
  fn output_base<CS: ConstraintSystem<E1::Scalar>>(
    &self,
    cs: &mut CS,
    ctx: &CtxVars<E1::Scalar>,
    lo: &AllocatedNum<E1::Scalar>,
    hi: &AllocatedNum<E1::Scalar>,
    r: &[AllocatedNum<E1::Scalar>],
    h: &AllocatedNum<E1::Scalar>,
  ) -> Result<(), SynthesisError> {
    let run = self.default_running(cs.namespace(|| "U default"))?;
    let cf = CfAcc::<E2>::default(cs.namespace(|| "cfU default"), self.params.n_cf)?;
    let out = link_hash::<E1, E2, _>(
      cs.namespace(|| "output hash"),
      self.params.ro2_consts.clone(),
      ctx,
      lo,
      hi,
      r,
      h,
      &run,
      &cf,
    )?;
    out.inputize(cs.namespace(|| "output"))
  }

  /// Synthesizes the circuit; returns the node result r.
  pub(crate) fn synthesize<CS: ConstraintSystem<E1::Scalar>>(
    &self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<E1::Scalar>>, SynthesisError> {
    match self.role {
      NodeRole::Leaf(k) => self.synthesize_leaf(cs, k),
      NodeRole::Dummy => self.synthesize_dummy(cs),
      NodeRole::Merge => self.synthesize_merge(cs),
    }
  }

  fn synthesize_leaf<CS: ConstraintSystem<E1::Scalar>>(
    &self,
    cs: &mut CS,
    k: usize,
  ) -> Result<Vec<AllocatedNum<E1::Scalar>>, SynthesisError> {
    let p = self.params;
    let (pv, xv) = match self.inputs.map(|i| &i.role) {
      Some(RoleIn::Leaf { p, x }) => (Some(*p), Some(x.as_slice())),
      Some(_) => return Err(SynthesisError::Unsatisfiable),
      None => (None, None),
    };
    let ctx = self.alloc_ctx(cs.namespace(|| "ctx"))?;
    let pos = AllocatedNum::alloc(cs.namespace(|| "p"), || {
      Ok(E1::Scalar::from(pv.unwrap_or(0)))
    })?;
    let x = alloc_vec(cs.namespace(|| "x"), xv, p.arity)?;

    // 0 ≤ p < 2^32 and p < L.
    let p_bits = to_bits(cs.namespace(|| "range p"), &Expr::num(&pos), RANGE_BITS)?;
    to_bits(
      cs.namespace(|| "range p < L"),
      &Expr::num(&ctx.l)
        .sub(&Expr::num(&pos))
        .sub(&Expr::constant::<CS>(E1::Scalar::ONE)),
      RANGE_BITS,
    )?;

    // β^p = Π_i (1 + b_i (β^{2^i} − 1)).
    let mut pow = Expr::constant::<CS>(E1::Scalar::ONE);
    let mut base = E1::Scalar::from(BETA);
    for (i, b) in p_bits.iter().enumerate() {
      let f =
        Expr::constant::<CS>(E1::Scalar::ONE).add(&Expr::bit(b).scale(base - E1::Scalar::ONE));
      pow = if i == 0 {
        f
      } else {
        Expr::num(&pow.mul(cs.namespace(|| format!("beta^p {i}")), &f)?)
      };
      base = base.square();
    }

    let y = self.leaf.synthesize(k, &mut cs.namespace(|| "F"), &x)?;
    if y.len() != p.arity {
      return Err(SynthesisError::IncompatibleLengthVector("F_k(x)".into()));
    }
    let r = y
      .iter()
      .enumerate()
      .map(|(e, ye)| pow.mul(cs.namespace(|| format!("r{e}")), &Expr::num(ye)))
      .collect::<Result<Vec<_>, _>>()?;
    let kc = alloc_constant(cs.namespace(|| "leaf id"), E1::Scalar::from(k as u64))?;
    let mut xs = vec![&pos, &kc];
    xs.extend(x.iter());
    let h = hash::<E1, _>(
      cs.namespace(|| "leaf hash"),
      p.ro2_consts.clone(),
      TAG_TREE_LEAF,
      &xs,
    )?;
    let hi = Expr::num(&pos)
      .add(&Expr::constant::<CS>(E1::Scalar::ONE))
      .alloc(cs.namespace(|| "p + 1"))?;
    self.output_base(cs, &ctx, &pos, &hi, &r, &h)?;
    Ok(r)
  }

  fn synthesize_dummy<CS: ConstraintSystem<E1::Scalar>>(
    &self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<E1::Scalar>>, SynthesisError> {
    let p = self.params;
    let (lov, hiv) = match self.inputs.map(|i| &i.role) {
      Some(RoleIn::Dummy { lo, hi }) => (*lo, *hi),
      Some(_) => return Err(SynthesisError::Unsatisfiable),
      None => (0, 0),
    };
    let ctx = self.alloc_ctx(cs.namespace(|| "ctx"))?;
    let lo = AllocatedNum::alloc(cs.namespace(|| "lo"), || Ok(E1::Scalar::from(lov)))?;
    let hi = AllocatedNum::alloc(cs.namespace(|| "hi"), || Ok(E1::Scalar::from(hiv)))?;
    // lo ≥ L and hi > lo.
    to_bits(
      cs.namespace(|| "range lo >= L"),
      &Expr::num(&lo).sub(&Expr::num(&ctx.l)),
      RANGE_BITS,
    )?;
    to_bits(
      cs.namespace(|| "range hi > lo"),
      &Expr::num(&hi)
        .sub(&Expr::num(&lo))
        .sub(&Expr::constant::<CS>(E1::Scalar::ONE)),
      RANGE_BITS,
    )?;
    let zero = alloc_constant(cs.namespace(|| "zero result"), E1::Scalar::ZERO)?;
    let r = vec![zero; p.arity];
    let h = hash::<E1, _>(
      cs.namespace(|| "dummy hash"),
      p.ro2_consts.clone(),
      TAG_TREE_DUMMY,
      &[&lo, &hi],
    )?;
    self.output_base(cs, &ctx, &lo, &hi, &r, &h)?;
    Ok(r)
  }

  fn synthesize_merge<CS: ConstraintSystem<E1::Scalar>>(
    &self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<E1::Scalar>>, SynthesisError> {
    let p = self.params;
    let a = p.a;
    let t = p.template.t();
    let m = match self.inputs.map(|i| &i.role) {
      Some(RoleIn::Merge {
        children,
        proof,
        hint_w,
        hint_m,
        cf_t_relaxed,
        cf_w,
        cf_t,
      }) => {
        if children.len() != a || cf_t_relaxed.len() + 1 != a {
          return Err(SynthesisError::IncompatibleLengthVector("children".into()));
        }
        Some((children, proof, hint_w, hint_m, cf_t_relaxed, cf_w, cf_t))
      }
      Some(_) => return Err(SynthesisError::Unsatisfiable),
      None => None,
    };
    let ctx = self.alloc_ctx(cs.namespace(|| "ctx"))?;

    // Children (advice).
    struct Child<F: PrimeField, E2: Engine> {
      lo: AllocatedNum<F>,
      hi: AllocatedNum<F>,
      r: Vec<AllocatedNum<F>>,
      h: AllocatedNum<F>,
      run: AllocRunning<F>,
      inc: AllocIncoming<F>,
      cf: CfAcc<E2>,
    }
    let mut children = Vec::with_capacity(a);
    for c in 0..a {
      let ch = m.map(|m| &m.0[c]);
      let mut cs = cs.namespace(|| format!("child{c}"));
      let lo = AllocatedNum::alloc(cs.namespace(|| "lo"), || {
        Ok(ch.map_or(E1::Scalar::ZERO, |c| E1::Scalar::from(c.lo)))
      })?;
      let hi = AllocatedNum::alloc(cs.namespace(|| "hi"), || {
        Ok(ch.map_or(E1::Scalar::ZERO, |c| E1::Scalar::from(c.hi)))
      })?;
      let r = alloc_vec(cs.namespace(|| "r"), ch.map(|c| &c.r[..]), p.arity)?;
      let h = AllocatedNum::alloc(cs.namespace(|| "h"), || {
        Ok(ch.map_or(E1::Scalar::ZERO, |c| c.h))
      })?;
      let run = self.alloc_running(cs.namespace(|| "U"), ch.map(|c| &c.run))?;
      let inc = {
        let mut cs = cs.namespace(|| "u");
        let k = AllocatedNum::alloc(cs.namespace(|| "k"), || {
          Ok(ch.map_or(E1::Scalar::ZERO, |c| E1::Scalar::from(c.inc.k as u64)))
        })?;
        let k_bits = one_hot(cs.namespace(|| "k one-hot"), &k, p.k)?;
        let comm_w = NnPoint::alloc(
          cs.namespace(|| "comm_w"),
          ch.map(|c| c.inc.comm_w.to_coordinates()),
          true,
        )?;
        let io = alloc_vec(cs.namespace(|| "io"), ch.map(|c| &c.inc.io[..]), p.num_io)?;
        AllocIncoming {
          k,
          k_bits,
          comm_w,
          io,
        }
      };
      let cf = CfAcc::<E2>::alloc(cs.namespace(|| "cfU"), ch.map(|c| &c.cf), p.n_cf)?;
      children.push(Child {
        lo,
        hi,
        r,
        h,
        run,
        inc,
        cf,
      });
    }

    // HFS proof and hints.
    let proof = {
      let mut cs = cs.namespace(|| "proof");
      let pf = m.map(|m| m.1);
      AllocProofN {
        sc_x: alloc_rows(
          cs.namespace(|| "sc_x"),
          pf.map(|p| &p.sc_x),
          p.s,
          p.template.deg_x() + 1,
        )?,
        sigma: alloc_rows(cs.namespace(|| "sigma"), pf.map(|p| &p.sigma), a, t)?,
        tau: alloc_rows(cs.namespace(|| "tau"), pf.map(|p| &p.tau), a, t)?,
        sc_y: alloc_rows(cs.namespace(|| "sc_y"), pf.map(|p| &p.sc_y), p.s_prime, 3)?,
        eps: alloc_rows(cs.namespace(|| "eps"), pf.map(|p| &p.eps), a, t + 1)?,
        theta: alloc_rows(cs.namespace(|| "theta"), pf.map(|p| &p.theta), a, t + 1)?,
      }
    };
    let hint_w = NnPoint::alloc(
      cs.namespace(|| "hint W"),
      m.map(|m| m.2.to_coordinates()),
      true,
    )?;
    let hint_m = if p.direct {
      (0..t)
        .map(|j| {
          NnPoint::alloc(
            cs.namespace(|| format!("hint M{j}")),
            m.map(|m| m.3[j].to_coordinates()),
            true,
          )
        })
        .collect::<Result<Vec<_>, _>>()?
    } else {
      Vec::new()
    };
    let cf_pt = |cs: &mut CS, n: String, c: Option<&Commitment<E2>>| {
      let pt =
        AllocatedPoint::<E2>::alloc(cs.namespace(|| n.clone()), c.map(|c| c.to_coordinates()))?;
      pt.check_on_curve(cs.namespace(|| format!("{n} on curve")))?;
      Ok::<_, SynthesisError>(pt)
    };
    let cf_t_rel = (1..a)
      .map(|c| cf_pt(cs, format!("cf T{c}"), m.map(|m| &m.4[c - 1])))
      .collect::<Result<Vec<_>, _>>()?;
    let cf_w = cf_pt(cs, "cf comm_w".into(), m.map(|m| m.5))?;
    let cf_t = cf_pt(cs, "cf T".into(), m.map(|m| m.6))?;

    // 1. Every child hashes its statement and accumulators under this node's task context.
    for (c, ch) in children.iter().enumerate() {
      let mut cs = cs.namespace(|| format!("child{c} hash"));
      let h = link_hash::<E1, E2, _>(
        cs.namespace(|| "H"),
        p.ro2_consts.clone(),
        &ctx,
        &ch.lo,
        &ch.hi,
        &ch.r,
        &ch.h,
        &ch.run,
        &ch.cf,
      )?;
      cs.enforce(
        || format!("child{c} io = H(child)"),
        |lc| lc + ch.inc.io[0].get_variable() - h.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc,
      );
    }

    // 2. Contiguous, ordered, equal-width ranges.
    let width0 = Expr::num(&children[0].hi).sub(&Expr::num(&children[0].lo));
    {
      let mut cs = cs.namespace(|| "ranges");
      for c in 1..a {
        let (prev, cur) = (&children[c - 1], &children[c]);
        cs.enforce(
          || format!("lo{c} = hi{}", c - 1),
          |lc| lc + cur.lo.get_variable() - prev.hi.get_variable(),
          |lc| lc + CS::one(),
          |lc| lc,
        );
        let wc = Expr::num(&cur.hi).sub(&Expr::num(&cur.lo)).sub(&width0);
        cs.enforce(
          || format!("width{c} = width0"),
          |_| wc.lc.clone(),
          |lc| lc + CS::one(),
          |lc| lc,
        );
      }
    }

    // 3. HFS v2 fold of μ = a running and ν = a incoming instances (always active).
    let gp = HfsGadgetParams {
      template: &p.template,
      tag_input: p.tag_input,
      s: p.s,
      iota: &p.iota,
    };
    let runs: Vec<AllocRunning<E1::Scalar>> = children.iter().map(|c| c.run.clone()).collect();
    let incs: Vec<AllocIncoming<E1::Scalar>> = children
      .iter()
      .map(|c| AllocIncoming {
        k: c.inc.k.clone(),
        k_bits: c.inc.k_bits.clone(),
        comm_w: c.inc.comm_w.clone(),
        io: c.inc.io.clone(),
      })
      .collect();
    let out = verify_hfs_multi::<E1, _>(
      cs.namespace(|| "hfs"),
      &gp,
      p.ro2_consts.clone(),
      &ctx.hfs,
      &runs,
      &incs,
      &proof,
      &Expr::constant::<CS>(E1::Scalar::ONE),
    )?;
    let run_new = AllocRunning {
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

    // 4. CycleFold: the fresh instance's inputs, then fold the a accumulators and it.
    let k_bits: Vec<&[AllocatedBit]> = if p.direct {
      children.iter().map(|c| &c.inc.k_bits[..]).collect()
    } else {
      Vec::new()
    };
    let w_pts: Vec<&NnPoint<E1::Scalar>> = children
      .iter()
      .map(|c| &c.run.comm_w)
      .chain(children.iter().map(|c| &c.inc.comm_w))
      .chain(std::iter::once(&hint_w))
      .collect();
    let m_pts: Vec<(Vec<&NnPoint<E1::Scalar>>, &NnPoint<E1::Scalar>)> = (0..hint_m.len())
      .map(|j| {
        let runs = children
          .iter()
          .map(|c| match &c.run.index {
            AllocIndex::Direct(m) => &m[j],
            AllocIndex::Span(_) => unreachable!("Direct index"),
          })
          .collect();
        (runs, &hint_m[j])
      })
      .collect();
    let x = cyclefold_inputs_n(&out.rho_bits, &k_bits, &w_pts, &m_pts);
    debug_assert_eq!(x.len(), p.n_cf);
    let mut acc = children[0].cf.clone();
    for c in 1..a {
      acc = acc.fold_relaxed(
        cs.namespace(|| format!("cyclefold relaxed{c}")),
        &ctx.pp,
        &children[c].cf,
        &cf_t_rel[c - 1],
        p.ro_cf_consts.clone(),
      )?;
    }
    let acc = acc.fold_fresh(
      cs.namespace(|| "cyclefold fresh"),
      &ctx.pp,
      &cf_w,
      &x,
      &cf_t,
      p.ro_cf_consts.clone(),
    )?;

    // 5. Statement: [lo_0, hi_{a−1}), Σ r_c, tree hash.
    let r = (0..p.arity)
      .map(|e| {
        children
          .iter()
          .fold(Expr::zero(), |acc, c| acc.add(&Expr::num(&c.r[e])))
          .alloc(cs.namespace(|| format!("result{e}")))
      })
      .collect::<Result<Vec<_>, _>>()?;
    let (lo, hi) = (&children[0].lo, &children[a - 1].hi);
    let mut xs = vec![lo, hi];
    xs.extend(children.iter().map(|c| &c.h));
    let h = hash::<E1, _>(
      cs.namespace(|| "node hash"),
      p.ro2_consts.clone(),
      TAG_TREE_NODE,
      &xs,
    )?;
    let h_out = link_hash::<E1, E2, _>(
      cs.namespace(|| "output hash"),
      p.ro2_consts.clone(),
      &ctx,
      lo,
      hi,
      &r,
      &h,
      &run_new,
      &acc,
    )?;
    h_out.inputize(cs.namespace(|| "output"))?;
    Ok(r)
  }
}
