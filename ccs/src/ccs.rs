//! Customizable constraint systems: `Σ_k c_k · ∘_{j ∈ S_k} (M_j · z) = 0`.
use crate::{dim, CcsError, SparseMatrix};
use ff::PrimeField;

/// The fixed part of a CCS shared by a predicate family: t matrices, q product terms given as
/// multisets of matrix indices (repeats allowed), and q coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Template<F: PrimeField> {
  pub t: usize,
  pub multisets: Vec<Vec<usize>>,
  pub coeffs: Vec<F>,
}

impl<F: PrimeField> Template<F> {
  /// R1CS: `(A z) ∘ (B z) − C z = 0`; t = 3, q = 2, d = 2.
  pub fn r1cs() -> Self {
    Self {
      t: 3,
      multisets: vec![vec![0, 1], vec![2]],
      coeffs: vec![F::ONE, -F::ONE],
    }
  }

  /// `(M₀ z)^d − M₁ z = 0`: one matrix repeated d times (a true multiset); t = 2, q = 2.
  pub fn power(d: usize) -> Self {
    Self {
      t: 2,
      multisets: vec![vec![0; d], vec![1]],
      coeffs: vec![F::ONE, -F::ONE],
    }
  }

  /// `∘_{j<d} (M_j z) − M_d z = 0`: d distinct matrices; t = d + 1, q = 2.
  pub fn product(d: usize) -> Self {
    Self {
      t: d + 1,
      multisets: vec![(0..d).collect(), vec![d]],
      coeffs: vec![F::ONE, -F::ONE],
    }
  }

  pub fn q(&self) -> usize {
    self.multisets.len()
  }

  /// Maximum multiset size (the product degree).
  pub fn degree(&self) -> usize {
    self.multisets.iter().map(Vec::len).max().unwrap_or(0)
  }

  pub fn validate(&self) -> Result<(), CcsError> {
    if self.t == 0 || self.multisets.is_empty() {
      return Err(CcsError::InvalidTemplate("t and q must be positive".into()));
    }
    dim(
      "template coefficients",
      self.multisets.len(),
      self.coeffs.len(),
    )?;
    for (k, s) in self.multisets.iter().enumerate() {
      if s.is_empty() {
        return Err(CcsError::InvalidTemplate(format!("multiset {k} is empty")));
      }
      if let Some(j) = s.iter().find(|&&j| j >= self.t) {
        return Err(CcsError::InvalidTemplate(format!(
          "multiset {k} uses matrix {j} but t = {}",
          self.t
        )));
      }
    }
    Ok(())
  }
}

/// A CCS over `m` rows and `n = num_w + 1 + num_io` columns, with `z = (w ‖ u ‖ io)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ccs<F: PrimeField> {
  pub m: usize,
  pub num_w: usize,
  pub num_io: usize,
  pub template: Template<F>,
  pub matrices: Vec<SparseMatrix<F>>,
}

impl<F: PrimeField> Ccs<F> {
  /// Validates and returns the CCS.
  pub fn new(
    m: usize,
    num_w: usize,
    num_io: usize,
    template: Template<F>,
    matrices: Vec<SparseMatrix<F>>,
  ) -> Result<Self, CcsError> {
    let ccs = Self {
      m,
      num_w,
      num_io,
      template,
      matrices,
    };
    ccs.validate()?;
    Ok(ccs)
  }

  pub fn n(&self) -> usize {
    self.num_w + 1 + self.num_io
  }

  /// Column of `u` (the constant 1 for a fresh instance).
  pub fn u_col(&self) -> usize {
    self.num_w
  }

  pub fn io_col(&self, i: usize) -> usize {
    self.num_w + 1 + i
  }

  pub fn t(&self) -> usize {
    self.template.t
  }

  pub fn q(&self) -> usize {
    self.template.q()
  }

  pub fn degree(&self) -> usize {
    self.template.degree()
  }

  pub fn nnz(&self) -> usize {
    self.matrices.iter().map(SparseMatrix::nnz).sum()
  }

  pub fn validate(&self) -> Result<(), CcsError> {
    self.template.validate()?;
    dim("number of matrices", self.template.t, self.matrices.len())?;
    for (j, mat) in self.matrices.iter().enumerate() {
      dim(&format!("rows of M{j}"), self.m, mat.rows())?;
      dim(&format!("columns of M{j}"), self.n(), mat.cols())?;
    }
    Ok(())
  }

  /// `z = (w ‖ u ‖ io)`, with length checks.
  pub fn z(&self, w: &[F], u: F, io: &[F]) -> Result<Vec<F>, CcsError> {
    dim("witness", self.num_w, w.len())?;
    dim("public io", self.num_io, io.len())?;
    Ok([w, &[u], io].concat())
  }

  /// Per-row value of `Σ_k c_k ∘_{j∈S_k} (M_j z)`.
  pub fn residual(&self, z: &[F]) -> Result<Vec<F>, CcsError> {
    dim("z", self.n(), z.len())?;
    let mz = self
      .matrices
      .iter()
      .map(|m| m.mul_vec(z))
      .collect::<Result<Vec<_>, _>>()?;
    let mut res = vec![F::ZERO; self.m];
    for (s, c) in self.template.multisets.iter().zip(&self.template.coeffs) {
      for (row, r) in res.iter_mut().enumerate() {
        *r += s.iter().fold(*c, |acc, &j| acc * mz[j][row]);
      }
    }
    Ok(res)
  }

  /// `Ok` iff every row of the relation holds; otherwise the first failing row.
  pub fn is_satisfied(&self, z: &[F]) -> Result<(), CcsError> {
    match self
      .residual(z)?
      .iter()
      .position(|r| !bool::from(r.is_zero()))
    {
      None => Ok(()),
      Some(row) => Err(CcsError::Unsatisfied { row }),
    }
  }
}
