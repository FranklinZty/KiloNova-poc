//! Per-component constraint counts of the primary circuit (PLAN.md P5 acceptance).
//!
//! [`BreakdownCS`] counts every constraint once, under the namespace path in which it is
//! enforced, so the components are disjoint and sum to the total. [`category`] maps a path
//! (top-level namespace of `circuit.rs` and, inside the HFS gadget, the second level) to a
//! component.
use super::{circuit::PrimaryCircuit, IvcError, IvcVariant, PredicateProgram, PublicParams};
use crate::{
  frontend::{ConstraintSystem, Index, LinearCombination, SynthesisError, Variable},
  traits::Engine,
};
use ff::PrimeField;
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, marker::PhantomData};

/// Components reported (disjoint).
pub const CATEGORIES: [&str; 10] = [
  "application",
  "selection",
  "hfs_sumcheck",
  "hfs_transcript",
  "hfs_claims",
  "hfs_index",
  "hashing",
  "nonnative_hints",
  "cyclefold_fold",
  "control",
];

/// The component of a constraint enforced under `path`.
pub fn category(path: &[String]) -> &'static str {
  let top = path.first().map(String::as_str).unwrap_or("");
  let second = path.get(1).map(String::as_str).unwrap_or("");
  match top {
    "F" => "application",
    "phi" | "phi selects k" => "selection",
    "hfs" => {
      if second.starts_with("sc_x") || second.starts_with("sc_y") {
        "hfs_sumcheck"
      } else if second.starts_with("iota") || second.starts_with("lambda") {
        "hfs_index"
      } else if matches!(
        second,
        "tag input" | "mu" | "gamma" | "delta" | "rho" | "tag x" | "tag y"
      ) || second.starts_with("alpha")
      {
        "hfs_transcript"
      } else {
        "hfs_claims"
      }
    }
    "input hash" | "output hash" | "trace tag" | "predicate id" | "trace squeeze"
    | "trace hash" => "hashing",
    "U" | "u" | "proof" => "nonnative_hints",
    t if t.starts_with("hint") => "nonnative_hints",
    "cfU" | "cyclefold fold" => "cyclefold_fold",
    t if t.starts_with("cf ") => "cyclefold_fold",
    _ => "control",
  }
}

/// Constraint counts per component and in total.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Breakdown {
  /// Total constraints (rows, including native power rows).
  pub total: usize,
  /// Auxiliary variables.
  pub num_aux: usize,
  /// Per component, keys from [`CATEGORIES`].
  pub by_category: BTreeMap<String, usize>,
  /// Per top-level namespace (and second level inside `hfs`), for inspection.
  pub by_namespace: BTreeMap<String, usize>,
}

/// A counting constraint system that attributes each constraint to its namespace path.
pub struct BreakdownCS<F: PrimeField> {
  stack: Vec<String>,
  out: Breakdown,
  inputs: usize,
  _p: PhantomData<F>,
}

impl<F: PrimeField> Default for BreakdownCS<F> {
  fn default() -> Self {
    Self {
      stack: Vec::new(),
      out: Breakdown::default(),
      inputs: 1,
      _p: PhantomData,
    }
  }
}

impl<F: PrimeField> BreakdownCS<F> {
  /// The result.
  pub fn finish(self) -> Breakdown {
    self.out
  }
}

impl<F: PrimeField> ConstraintSystem<F> for BreakdownCS<F> {
  type Root = Self;

  fn alloc<Fn_, A, AR>(&mut self, _a: A, _f: Fn_) -> Result<Variable, SynthesisError>
  where
    Fn_: FnOnce() -> Result<F, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    self.out.num_aux += 1;
    Ok(Variable::new_unchecked(Index::Aux(self.out.num_aux - 1)))
  }

  fn alloc_input<Fn_, A, AR>(&mut self, _a: A, _f: Fn_) -> Result<Variable, SynthesisError>
  where
    Fn_: FnOnce() -> Result<F, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    self.inputs += 1;
    Ok(Variable::new_unchecked(Index::Input(self.inputs - 1)))
  }

  fn enforce<A, AR, LA, LB, LC>(&mut self, _a: A, _la: LA, _lb: LB, _lc: LC)
  where
    A: FnOnce() -> AR,
    AR: Into<String>,
    LA: FnOnce(LinearCombination<F>) -> LinearCombination<F>,
    LB: FnOnce(LinearCombination<F>) -> LinearCombination<F>,
    LC: FnOnce(LinearCombination<F>) -> LinearCombination<F>,
  {
    self.out.total += 1;
    *self
      .out
      .by_category
      .entry(category(&self.stack).to_string())
      .or_default() += 1;
    let key = match self.stack.first().map(String::as_str) {
      Some("hfs") => format!(
        "hfs/{}",
        self
          .stack
          .get(1)
          .map(|s| s.trim_end_matches(char::is_numeric))
          .unwrap_or("")
      ),
      Some(t) => t.trim_end_matches(char::is_numeric).to_string(),
      None => String::new(),
    };
    *self.out.by_namespace.entry(key).or_default() += 1;
  }

  fn push_namespace<NR, N>(&mut self, name_fn: N)
  where
    NR: Into<String>,
    N: FnOnce() -> NR,
  {
    self.stack.push(name_fn().into());
  }

  fn pop_namespace(&mut self) {
    self.stack.pop();
  }

  fn get_root(&mut self) -> &mut Self::Root {
    self
  }
}

/// Breakdown of predicate `id`'s primary circuit at the parameters' dimensions.
pub fn primary_breakdown<E1, E2, PS, V>(
  pp: &PublicParams<E1, E2, V>,
  predicates: &PS,
  id: usize,
) -> Result<Breakdown, IvcError>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  PS: PredicateProgram<E1::Scalar>,
  V: IvcVariant<E1>,
{
  let mut cs = BreakdownCS::<E1::Scalar>::default();
  PrimaryCircuit::<E1, E2, PS, V> {
    params: &pp.primary,
    predicates,
    k: id,
    inputs: None,
  }
  .synthesize(&mut cs)?;
  Ok(cs.finish())
}
