//! Primary shapes: R1CS rows from the frontend plus, for the combined template, native
//! degree-5 rows.
//!
//! The frontend only emits rank-1 constraints. A predicate that wants a native high-degree
//! row calls [`enforce_pow5`], which emits a constraint annotated [`KN_NATIVE_POW5`].
//! [`KnShapeCS`] records such constraints as rows of the matrices D (from the `a` side) and E
//! (from the `c` side) of the template [`PrimaryTemplate::R1csPow5`]:
//! `(A z)∘(B z) − C z + (D z)^5 − E z = 0`. R1CS rows have D = E = 0 and power rows have
//! A = B = C = 0, so every row is one of the two relations. No intermediate multiplication
//! witnesses are introduced for `x^5`: the application stays degree 5 inside the recursion.
//!
//! The witness generator (`SatisfyingAssignment`) ignores constraints, so the same predicate
//! code serves both the shape and the witness.
use crate::{
  frontend::{
    num::AllocatedNum, ConstraintSystem, Index, LinearCombination, SynthesisError, Variable,
  },
  kilonova::hfs::{CcsShape, CcsTemplate, HfsError},
};
use ff::PrimeField;
use serde::{Deserialize, Serialize};

/// Annotation that marks a native degree-5 row `(a)^5 = c`.
pub const KN_NATIVE_POW5: &str = "KN_NATIVE_POW5";

/// The CCS template of the primary relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrimaryTemplate {
  /// R1CS only (t = 3, d = 2).
  R1cs,
  /// R1CS plus native fifth-power rows (t = 5, d = 5).
  R1csPow5,
}

impl PrimaryTemplate {
  /// The HFS template.
  pub fn template<F: PrimeField>(&self) -> CcsTemplate<F> {
    match self {
      PrimaryTemplate::R1cs => CcsTemplate::r1cs(),
      PrimaryTemplate::R1csPow5 => CcsTemplate::new(
        5,
        vec![vec![0, 1], vec![2], vec![3; 5], vec![4]],
        vec![F::ONE, -F::ONE, F::ONE, -F::ONE],
      )
      .expect("valid template"),
    }
  }

  /// Number of matrices.
  pub fn t(&self) -> usize {
    match self {
      PrimaryTemplate::R1cs => 3,
      PrimaryTemplate::R1csPow5 => 5,
    }
  }
}

/// Enforces `y = x^5` as **one native degree-5 row** (template [`PrimaryTemplate::R1csPow5`]).
/// Under the R1CS template, setup rejects the shape.
pub fn enforce_pow5<F: PrimeField, CS: ConstraintSystem<F>>(
  cs: &mut CS,
  x: &AllocatedNum<F>,
  y: &AllocatedNum<F>,
) {
  cs.enforce(
    || KN_NATIVE_POW5,
    |lc| lc + x.get_variable(),
    |lc| lc,
    |lc| lc + y.get_variable(),
  );
}

/// A shape-recording constraint system that separates native power rows.
pub struct KnShapeCS<F: PrimeField> {
  pub(crate) r1cs: Vec<(
    LinearCombination<F>,
    LinearCombination<F>,
    LinearCombination<F>,
  )>,
  pub(crate) pow: Vec<(LinearCombination<F>, LinearCombination<F>)>,
  inputs: usize,
  aux: usize,
}

impl<F: PrimeField> Default for KnShapeCS<F> {
  fn default() -> Self {
    Self {
      r1cs: Vec::new(),
      pow: Vec::new(),
      inputs: 1,
      aux: 0,
    }
  }
}

impl<F: PrimeField> KnShapeCS<F> {
  /// Number of auxiliary variables (witness length before padding).
  pub fn num_aux(&self) -> usize {
    self.aux
  }

  /// Number of public inputs (without the constant one).
  pub fn num_io(&self) -> usize {
    self.inputs - 1
  }

  /// Number of rows (R1CS rows first, then power rows).
  pub fn num_rows(&self) -> usize {
    self.r1cs.len() + self.pow.len()
  }

  /// Number of native power rows.
  pub fn num_pow_rows(&self) -> usize {
    self.pow.len()
  }

  /// The CCS shape padded to `m` rows and `num_w` witness columns.
  pub fn to_ccs(
    &self,
    tpl: PrimaryTemplate,
    m: usize,
    num_w: usize,
  ) -> Result<CcsShape<F>, HfsError> {
    if tpl == PrimaryTemplate::R1cs && !self.pow.is_empty() {
      return Err(HfsError::InvalidTemplate(format!(
        "{} native power rows under the R1CS template",
        self.pow.len()
      )));
    }
    if m < self.num_rows() || num_w < self.aux {
      return Err(HfsError::InvalidFamily("padding below the raw size".into()));
    }
    let col = |v: Variable| match v.get_unchecked() {
      Index::Input(i) => num_w + i,
      Index::Aux(i) => i,
    };
    let push = |mat: &mut Vec<(usize, usize, F)>, row: usize, lc: &LinearCombination<F>| {
      for (v, c) in lc.iter() {
        if !bool::from(c.is_zero()) {
          mat.push((row, col(v), *c));
        }
      }
    };
    let mut mats = vec![Vec::new(); tpl.t()];
    for (row, (a, b, c)) in self.r1cs.iter().enumerate() {
      push(&mut mats[0], row, a);
      push(&mut mats[1], row, b);
      push(&mut mats[2], row, c);
    }
    for (i, (d, e)) in self.pow.iter().enumerate() {
      let row = self.r1cs.len() + i;
      push(&mut mats[3], row, d);
      push(&mut mats[4], row, e);
    }
    CcsShape::new(m, num_w, self.num_io(), mats)
  }
}

impl<F: PrimeField> ConstraintSystem<F> for KnShapeCS<F> {
  type Root = Self;

  fn alloc<Fn_, A, AR>(&mut self, _a: A, _f: Fn_) -> Result<Variable, SynthesisError>
  where
    Fn_: FnOnce() -> Result<F, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    self.aux += 1;
    Ok(Variable::new_unchecked(Index::Aux(self.aux - 1)))
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

  fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
  where
    A: FnOnce() -> AR,
    AR: Into<String>,
    LA: FnOnce(LinearCombination<F>) -> LinearCombination<F>,
    LB: FnOnce(LinearCombination<F>) -> LinearCombination<F>,
    LC: FnOnce(LinearCombination<F>) -> LinearCombination<F>,
  {
    let (a, b, c) = (
      a(LinearCombination::zero()),
      b(LinearCombination::zero()),
      c(LinearCombination::zero()),
    );
    if annotation().into() == KN_NATIVE_POW5 {
      self.pow.push((a, c));
    } else {
      self.r1cs.push((a, b, c));
    }
  }

  fn push_namespace<NR, N>(&mut self, _name_fn: N)
  where
    NR: Into<String>,
    N: FnOnce() -> NR,
  {
  }

  fn pop_namespace(&mut self) {}

  fn get_root(&mut self) -> &mut Self::Root {
    self
  }
}

/// Checks a CCCS assignment `z = (w ‖ 1 ‖ io)` row by row (used by the native verifier for the
/// last incoming instance).
pub fn ccs_is_satisfied<F: PrimeField>(tpl: &CcsTemplate<F>, shape: &CcsShape<F>, z: &[F]) -> bool {
  if z.len() != shape.n() {
    return false;
  }
  let mz: Vec<Vec<F>> = (0..tpl.t()).map(|j| shape.mul_vec(j, z)).collect();
  (0..shape.m()).all(|r| {
    let vals: Vec<F> = mz.iter().map(|v| v[r]).collect();
    bool::from(tpl.combine(&vals).is_zero())
  })
}
