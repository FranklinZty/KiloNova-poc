//! `NativeCcsBuilder`: rows are written directly against a fixed template, so a degree-d
//! constraint costs one row and no intermediate witnesses.
use crate::{dim, Ccs, CcsError, SparseMatrix, Template};
use ff::PrimeField;

/// A variable of the assignment. Columns are fixed at `build()`: `W(i) ↦ i`,
/// `One ↦ num_w`, `Io(i) ↦ num_w + 1 + i` (layout `z = (w ‖ u ‖ io)`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Var {
  W(usize),
  One,
  Io(usize),
}

/// A linear combination of variables.
pub type Lc<F> = Vec<(Var, F)>;

/// A satisfying assignment produced together with the CCS (u = 1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Assignment<F: PrimeField> {
  pub w: Vec<F>,
  pub io: Vec<F>,
}

impl<F: PrimeField> Assignment<F> {
  /// `z = (w ‖ 1 ‖ io)`.
  pub fn z(&self) -> Vec<F> {
    [self.w.as_slice(), &[F::ONE], self.io.as_slice()].concat()
  }
}

pub struct NativeCcsBuilder<F: PrimeField> {
  template: Template<F>,
  w: Vec<Option<F>>,
  io: Vec<Option<F>>,
  rows: Vec<Vec<Lc<F>>>,
}

impl<F: PrimeField> NativeCcsBuilder<F> {
  pub fn new(template: Template<F>) -> Result<Self, CcsError> {
    template.validate()?;
    Ok(Self {
      template,
      w: Vec::new(),
      io: Vec::new(),
      rows: Vec::new(),
    })
  }

  /// Allocates a private witness variable; `None` builds the shape only.
  pub fn alloc_w(&mut self, value: Option<F>) -> Var {
    self.w.push(value);
    Var::W(self.w.len() - 1)
  }

  /// Allocates a public input/output variable.
  pub fn alloc_io(&mut self, value: Option<F>) -> Var {
    self.io.push(value);
    Var::Io(self.io.len() - 1)
  }

  /// Value of a variable, if known (`One` is always 1).
  pub fn value(&self, v: Var) -> Option<F> {
    match v {
      Var::W(i) => self.w.get(i).copied().flatten(),
      Var::One => Some(F::ONE),
      Var::Io(i) => self.io.get(i).copied().flatten(),
    }
  }

  /// Adds one constraint row: one linear combination per template matrix.
  pub fn push_row(&mut self, lcs: Vec<Lc<F>>) -> Result<(), CcsError> {
    dim("linear combinations in a row", self.template.t, lcs.len())?;
    self.rows.push(lcs);
    Ok(())
  }

  pub fn num_rows(&self) -> usize {
    self.rows.len()
  }

  /// Builds the CCS, and the assignment when every variable has a value.
  pub fn build(self) -> Result<(Ccs<F>, Option<Assignment<F>>), CcsError> {
    let (num_w, num_io, m) = (self.w.len(), self.io.len(), self.rows.len());
    let n = num_w + 1 + num_io;
    let col = |v: Var| -> Result<usize, CcsError> {
      match v {
        Var::W(i) if i < num_w => Ok(i),
        Var::One => Ok(num_w),
        Var::Io(i) if i < num_io => Ok(num_w + 1 + i),
        _ => Err(CcsError::IndexOutOfRange {
          row: m,
          col: n,
          rows: m,
          cols: n,
        }),
      }
    };
    let mut triplets = vec![Vec::new(); self.template.t];
    for (row, lcs) in self.rows.iter().enumerate() {
      for (j, lc) in lcs.iter().enumerate() {
        for &(v, c) in lc {
          triplets[j].push((row, col(v)?, c));
        }
      }
    }
    let matrices = triplets
      .into_iter()
      .map(|t| SparseMatrix::from_triplets(m, n, t))
      .collect::<Result<Vec<_>, _>>()?;
    let ccs = Ccs::new(m, num_w, num_io, self.template, matrices)?;
    let assignment = match (
      self.w.iter().copied().collect::<Option<Vec<F>>>(),
      self.io.iter().copied().collect::<Option<Vec<F>>>(),
    ) {
      (Some(w), Some(io)) => Some(Assignment { w, io }),
      _ => None,
    };
    Ok((ccs, assignment))
  }
}

/// Evaluates a linear combination given variable values.
pub fn eval_lc<F: PrimeField>(b: &NativeCcsBuilder<F>, lc: &Lc<F>) -> Option<F> {
  lc.iter()
    .try_fold(F::ZERO, |acc, &(v, c)| Some(acc + c * b.value(v)?))
}
