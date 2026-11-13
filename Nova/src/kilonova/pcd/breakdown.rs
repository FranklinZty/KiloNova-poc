//! Per-component constraint counts of the tree PCD node circuits (P6), with the P5
//! `BreakdownCS` and a tree path → component map. Components are disjoint and sum to the
//! CountingCS total (asserted in the tests and by `kn-scenario tree`).
use super::{
  circuit::{NodeCircuit, NodeRole},
  TreeError, TreeParams,
};
use crate::{
  kilonova::{
    ivc::{
      breakdown::{Breakdown, BreakdownCS},
      IvcVariant,
    },
    PredicateSet,
  },
  traits::Engine,
};

/// Components reported for node circuits (disjoint).
pub const TREE_CATEGORIES: [&str; 12] = [
  "application",
  "leaf_logic",
  "hfs_sumcheck",
  "hfs_transcript",
  "hfs_claims",
  "hfs_index",
  "child_link_hashes",
  "hashing",
  "ranges",
  "nonnative_hints",
  "cyclefold_fold",
  "control",
];

/// The component of a constraint enforced under `path` in a node circuit.
pub fn tree_category(path: &[String]) -> &'static str {
  let top = path.first().map(String::as_str).unwrap_or("");
  let second = path.get(1).map(String::as_str).unwrap_or("");
  match top {
    "F" => "application",
    "range p" | "range p < L" | "leaf id" | "p + 1" => "leaf_logic",
    t if t.starts_with("beta^p") || (t.starts_with('r') && t[1..].parse::<usize>().is_ok()) => {
      "leaf_logic"
    }
    "range lo >= L" | "range hi > lo" | "ranges" => "ranges",
    "hfs" => {
      if second.starts_with("sc_x") || second.starts_with("sc_y") {
        "hfs_sumcheck"
      } else if second.starts_with("iota") || second.starts_with("lambda") {
        "hfs_index"
      } else if matches!(
        second,
        "tag input" | "mu" | "nu" | "gamma" | "delta" | "rho" | "tag x" | "tag y"
      ) || second.starts_with("alpha")
      {
        "hfs_transcript"
      } else {
        "hfs_claims"
      }
    }
    t if t.starts_with("child") && t.ends_with(" hash") => "child_link_hashes",
    "output hash" | "node hash" | "leaf hash" | "dummy hash" => "hashing",
    "proof" => "nonnative_hints",
    t if t.starts_with("child") || t.starts_with("hint") => "nonnative_hints",
    t if t.starts_with("cyclefold") || t.starts_with("cf ") => "cyclefold_fold",
    _ => "control",
  }
}

/// Breakdown of the circuit of member `role` at the parameters' dimensions.
pub fn node_breakdown<E1, E2, P, V>(
  pp: &TreeParams<E1, E2, V>,
  leaf: &P,
  role: NodeRole,
) -> Result<Breakdown, TreeError>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  P: PredicateSet<E1::Scalar>,
  V: IvcVariant<E1>,
{
  let mut cs = BreakdownCS::<E1::Scalar>::with_categorizer(tree_category);
  NodeCircuit::<E1, E2, P, V> {
    params: &pp.node,
    leaf,
    role,
    inputs: None,
  }
  .synthesize(&mut cs)?;
  Ok(cs.finish())
}
