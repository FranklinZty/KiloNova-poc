//! W4 task-tree generator (PLAN.md §6 W4): fixed leaf tasks, the a-ary layout with the dummy
//! rule, and the expected target result.
//!
//! A task is a list of L leaf tasks `(k_p, x_p)`: leaf predicate `k_p` (a member of the P4
//! chain family) applied to the input `x_p ∈ F²`. Inputs may repeat; positions are unique.
//! The target result is `R = Σ_{p<L} β^p · F_{k_p}(x_p)`, the same for every arity.
//!
//! Layout for arity a: depth `d = min{d : a^d ≥ L}`, capacity `N = a^d`; the node at level h,
//! index j covers `[j·a^h, (j+1)·a^h)`. A node with `lo < L` is a leaf (h = 0) or a merge
//! (h ≥ 1); a node with `lo ≥ L` whose parent has `lo < L` is a **dummy** (maximal padding
//! subtree, one proof); nodes inside a dummy subtree do not exist.
use super::{BETA, PCD_VERSION};
use crate::digest::{DigestComputer, SimpleDigestible};
use ff::PrimeField;
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};
use serde::{Deserialize, Serialize};

/// One leaf task.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeafTask<F> {
  /// Leaf predicate (position in the leaf family).
  pub k: usize,
  /// Input `x_p`.
  pub x: Vec<F>,
}

/// A W4 task: L fixed leaf tasks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeTask<F> {
  label: String,
  leaves: Vec<LeafTask<F>>,
}

#[derive(Serialize)]
struct TaskView<'a> {
  version: u64,
  label: &'a str,
  num_leaves: u64,
  leaves: Vec<(u64, Vec<String>)>,
}

impl SimpleDigestible for TaskView<'_> {}

/// Role of a node in a layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LayoutRole {
  /// Real leaf at position p (leaf predicate k).
  Leaf {
    /// Position.
    p: usize,
    /// Leaf predicate.
    k: usize,
  },
  /// Internal node (a predecessors).
  Merge,
  /// Padding subtree beyond L.
  Dummy,
}

/// One node of a layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LayoutNode {
  /// Level (0 = leaves).
  pub level: usize,
  /// Range start.
  pub lo: u64,
  /// Range end (exclusive).
  pub hi: u64,
  /// Role.
  pub role: LayoutRole,
}

/// The a-ary layout of a task.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TreeLayout {
  /// Arity.
  pub a: usize,
  /// Depth d.
  pub depth: usize,
  /// Capacity a^d.
  pub capacity: u64,
  /// Nodes per level, level 0 first, left to right.
  pub levels: Vec<Vec<LayoutNode>>,
}

impl TreeLayout {
  /// Number of nodes with the given role kind.
  pub fn count(&self, f: impl Fn(&LayoutRole) -> bool) -> usize {
    self.levels.iter().flatten().filter(|n| f(&n.role)).count()
  }

  /// Real leaves.
  pub fn num_leaves(&self) -> usize {
    self.count(|r| matches!(r, LayoutRole::Leaf { .. }))
  }

  /// Merge (internal) nodes.
  pub fn num_merges(&self) -> usize {
    self.count(|r| matches!(r, LayoutRole::Merge))
  }

  /// Dummy (padding) nodes.
  pub fn num_dummies(&self) -> usize {
    self.count(|r| matches!(r, LayoutRole::Dummy))
  }
}

/// Smallest d with `a^d ≥ l` (l ≥ 1, a ≥ 2).
pub fn depth_for(l: u64, a: usize) -> usize {
  let mut d = 0;
  let mut cap = 1u64;
  while cap < l {
    cap *= a as u64;
    d += 1;
  }
  d
}

impl<F: PrimeField> TreeTask<F> {
  /// A task from explicit leaves.
  pub fn new(label: impl Into<String>, leaves: Vec<LeafTask<F>>) -> Self {
    Self {
      label: label.into(),
      leaves,
    }
  }

  /// A seeded task of `num_leaves` leaves over `k_leaf` predicates: positions `0..k_leaf` use
  /// every predicate once, then predicates and inputs are drawn from ChaCha20(seed).
  pub fn generate(seed: u64, num_leaves: usize, k_leaf: usize) -> Self {
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let leaves = (0..num_leaves)
      .map(|p| {
        let k = if p < k_leaf {
          p
        } else {
          (rng.next_u32() as usize) % k_leaf
        };
        let x = vec![F::from(rng.next_u64()), F::from(rng.next_u64())];
        LeafTask { k, x }
      })
      .collect();
    Self::new(format!("kn-p6-w4-seed{seed}"), leaves)
  }

  /// The label.
  pub fn label(&self) -> &str {
    &self.label
  }

  /// The leaves.
  pub fn leaves(&self) -> &[LeafTask<F>] {
    &self.leaves
  }

  /// L.
  pub fn num_leaves(&self) -> usize {
    self.leaves.len()
  }

  /// Task identity: SHA3-256 → 250-bit field element over `(PCD_VERSION, label, L, leaves)`.
  pub fn task_id(&self) -> F {
    let view = TaskView {
      version: PCD_VERSION,
      label: &self.label,
      num_leaves: self.leaves.len() as u64,
      leaves: self
        .leaves
        .iter()
        .map(|l| (l.k as u64, l.x.iter().map(|x| format!("{x:?}")).collect()))
        .collect(),
    };
    DigestComputer::<F, _>::new(&view)
      .digest()
      .expect("task digest")
  }

  /// The layout for arity a (a ≥ 2, L ≥ 1).
  pub fn layout(&self, a: usize) -> TreeLayout {
    assert!(a >= 2 && !self.leaves.is_empty());
    let l = self.leaves.len() as u64;
    let depth = depth_for(l, a);
    let capacity = (a as u64).pow(depth as u32);
    let mut levels = Vec::with_capacity(depth + 1);
    for h in 0..=depth {
      let w = (a as u64).pow(h as u32);
      let mut nodes = Vec::new();
      for j in 0..capacity / w {
        let lo = j * w;
        let parent_lo = (j / a as u64) * w * a as u64;
        let role = if lo < l {
          if h == 0 {
            LayoutRole::Leaf {
              p: lo as usize,
              k: self.leaves[lo as usize].k,
            }
          } else {
            LayoutRole::Merge
          }
        } else if h < depth && parent_lo < l {
          LayoutRole::Dummy
        } else {
          continue;
        };
        nodes.push(LayoutNode {
          level: h,
          lo,
          hi: lo + w,
          role,
        });
      }
      levels.push(nodes);
    }
    TreeLayout {
      a,
      depth,
      capacity,
      levels,
    }
  }

  /// `R = Σ_p β^p · F_{k_p}(x_p)` with the native leaf functions `eval(k, x)`.
  pub fn expected_result(&self, eval: impl Fn(usize, &[F]) -> Vec<F>) -> Vec<F> {
    let mut acc: Vec<F> = Vec::new();
    let mut pow = F::ONE;
    let beta = F::from(BETA);
    for l in &self.leaves {
      let y = eval(l.k, &l.x);
      if acc.is_empty() {
        acc = vec![F::ZERO; y.len()];
      }
      for (a, y) in acc.iter_mut().zip(y) {
        *a += pow * y;
      }
      pow *= beta;
    }
    acc
  }
}
