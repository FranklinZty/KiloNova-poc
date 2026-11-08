//! CCS template, predicate shapes and the public parameters of the v2 HFS.
use super::{check_len, HfsError};
use crate::{
  digest::{DigestComputer, SimpleDigestible},
  kilonova::transcript::v2::HFS_TRANSCRIPT_VERSION,
  r1cs::R1CSShape,
  traits::{commitment::CommitmentEngineTrait, Engine, RO2Constants},
  Commitment, CommitmentKey,
};
use ff::{Field, PrimeField};
use serde::{de::DeserializeOwned, Deserialize, Serialize};

/// Label of the witness commitment key.
pub(crate) const CK_LABEL: &[u8] = b"kn-hfs-v2-ck";
/// Label of the index commitment key (t·K generators; `comm_M[j]` uses generators jK..(j+1)K).
pub(crate) const CK_INDEX_LABEL: &[u8] = b"kn-hfs-v2-index";

/// `max(1, ⌈log₂ len⌉)`: variables of an MLE over `len` entries (same rule as kn-ccs and v1).
pub fn num_vars(len: usize) -> usize {
  (len.max(1).next_power_of_two().trailing_zeros() as usize).max(1)
}

/// The fixed part of a CCS shared by a predicate family: `Σ_k c_k ∘_{j ∈ S_k} (M_j z) = 0`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound(serialize = "F: Serialize", deserialize = "F: DeserializeOwned"))]
pub struct CcsTemplate<F: PrimeField> {
  t: usize,
  multisets: Vec<Vec<usize>>,
  coeffs: Vec<F>,
}

impl<F: PrimeField> CcsTemplate<F> {
  /// Validates and returns a template.
  pub fn new(t: usize, multisets: Vec<Vec<usize>>, coeffs: Vec<F>) -> Result<Self, HfsError> {
    if t == 0 || multisets.is_empty() {
      return Err(HfsError::InvalidTemplate("t and q must be positive".into()));
    }
    check_len("template coefficients", multisets.len(), coeffs.len())?;
    for (k, s) in multisets.iter().enumerate() {
      if s.is_empty() {
        return Err(HfsError::InvalidTemplate(format!("multiset {k} is empty")));
      }
      if let Some(j) = s.iter().find(|&&j| j >= t) {
        return Err(HfsError::InvalidTemplate(format!(
          "multiset {k} uses matrix {j} but t = {t}"
        )));
      }
    }
    Ok(Self {
      t,
      multisets,
      coeffs,
    })
  }

  /// R1CS: `(A z) ∘ (B z) − C z`.
  pub fn r1cs() -> Self {
    Self::new(3, vec![vec![0, 1], vec![2]], vec![F::ONE, -F::ONE]).unwrap()
  }

  /// `(M₀ z)^d − M₁ z` (repeated multiset).
  pub fn power(d: usize) -> Result<Self, HfsError> {
    Self::new(2, vec![vec![0; d], vec![1]], vec![F::ONE, -F::ONE])
  }

  /// Number of matrices.
  pub fn t(&self) -> usize {
    self.t
  }

  /// Number of product terms.
  pub fn q(&self) -> usize {
    self.multisets.len()
  }

  /// Multisets of matrix indices.
  pub fn multisets(&self) -> &[Vec<usize>] {
    &self.multisets
  }

  /// Term coefficients.
  pub fn coeffs(&self) -> &[F] {
    &self.coeffs
  }

  /// Product degree d (largest multiset).
  pub fn degree(&self) -> usize {
    self.multisets.iter().map(Vec::len).max().unwrap_or(0)
  }

  /// Degree of the X-phase round polynomials: `max(d + 1, 2)`.
  pub fn deg_x(&self) -> usize {
    (self.degree() + 1).max(2)
  }

  /// `Σ_k c_k Π_{j ∈ S_k} vals[j]`.
  pub fn combine(&self, vals: &[F]) -> F {
    self
      .multisets
      .iter()
      .zip(&self.coeffs)
      .fold(F::ZERO, |acc, (ms, c)| {
        acc + ms.iter().fold(*c, |p, &j| p * vals[j])
      })
  }
}

/// One predicate: `m` rows, `n = num_w + 1 + num_io` columns, `z = (w ‖ u ‖ io)`, and t sparse
/// matrices given as `(row, col, value)` entries.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound(serialize = "F: Serialize", deserialize = "F: DeserializeOwned"))]
pub struct CcsShape<F: PrimeField> {
  m: usize,
  num_w: usize,
  num_io: usize,
  matrices: Vec<Vec<(usize, usize, F)>>,
}

impl<F: PrimeField> CcsShape<F> {
  /// Validates entry ranges and returns the shape. Duplicate entries are summed by every
  /// consumer, so they are allowed.
  pub fn new(
    m: usize,
    num_w: usize,
    num_io: usize,
    matrices: Vec<Vec<(usize, usize, F)>>,
  ) -> Result<Self, HfsError> {
    let n = num_w + 1 + num_io;
    for (j, mat) in matrices.iter().enumerate() {
      if let Some(e) = mat.iter().find(|e| e.0 >= m || e.1 >= n) {
        return Err(HfsError::InvalidFamily(format!(
          "entry ({}, {}) of M{j} outside a {m}x{n} matrix",
          e.0, e.1
        )));
      }
    }
    Ok(Self {
      m,
      num_w,
      num_io,
      matrices,
    })
  }

  /// Rows.
  pub fn m(&self) -> usize {
    self.m
  }

  /// Witness length.
  pub fn num_w(&self) -> usize {
    self.num_w
  }

  /// Public input/output length.
  pub fn num_io(&self) -> usize {
    self.num_io
  }

  /// Columns `num_w + 1 + num_io`.
  pub fn n(&self) -> usize {
    self.num_w + 1 + self.num_io
  }

  /// The matrices.
  pub fn matrices(&self) -> &[Vec<(usize, usize, F)>] {
    &self.matrices
  }

  /// Non-zero entries over all matrices.
  pub fn nnz(&self) -> usize {
    self.matrices.iter().map(Vec::len).sum()
  }

  /// `M_j · z` (length m).
  pub(crate) fn mul_vec(&self, j: usize, z: &[F]) -> Vec<F> {
    let mut out = vec![F::ZERO; self.m];
    for &(r, c, v) in &self.matrices[j] {
      out[r] += v * z[c];
    }
    out
  }
}

impl<E: Engine> From<&R1CSShape<E>> for CcsShape<E::Scalar> {
  /// The R1CS of an existing `R1CSShape` (layout `(W ‖ u ‖ X)` is the same), template
  /// [`CcsTemplate::r1cs`].
  fn from(shape: &R1CSShape<E>) -> Self {
    let mats = [&shape.A, &shape.B, &shape.C]
      .iter()
      .map(|m| m.iter().collect())
      .collect();
    CcsShape {
      m: shape.num_cons,
      num_w: shape.num_vars,
      num_io: shape.num_io,
      matrices: mats,
    }
  }
}

/// What the structure digest covers.
#[derive(Serialize)]
#[serde(bound = "")]
struct DigestView<'a, E: Engine> {
  version: u64,
  template: &'a CcsTemplate<E::Scalar>,
  shapes: &'a [CcsShape<E::Scalar>],
  ck_label: &'a [u8],
  ck_len: usize,
  ck_index_label: &'a [u8],
  ck_index_len: usize,
}

impl<E: Engine> SimpleDigestible for DigestView<'_, E> {}

/// Public parameters of the v2 HFS for a family of K predicates: the template, the shapes,
/// commitment keys, the incoming index commitments ι_k and the structure digest.
#[derive(Clone)]
pub struct HfsParams<E: Engine> {
  template: CcsTemplate<E::Scalar>,
  shapes: Vec<CcsShape<E::Scalar>>,
  s: usize,
  s_prime: usize,
  ck: CommitmentKey<E>,
  ck_index: CommitmentKey<E>,
  iota: Vec<Vec<Commitment<E>>>,
  ro_consts: RO2Constants<E>,
  digest: E::Scalar,
}

impl<E: Engine> HfsParams<E> {
  /// Builds the parameters. All members must have the same dimensions; they share `template`.
  pub fn new(
    template: CcsTemplate<E::Scalar>,
    shapes: Vec<CcsShape<E::Scalar>>,
  ) -> Result<Self, HfsError> {
    // Re-validate: the fields are private, but a deserialised template is not trusted.
    let template = CcsTemplate::new(
      template.t,
      template.multisets.clone(),
      template.coeffs.clone(),
    )?;
    let first = shapes
      .first()
      .ok_or_else(|| HfsError::InvalidFamily("empty family".into()))?;
    for (i, sh) in shapes.iter().enumerate() {
      let sh = CcsShape::new(sh.m, sh.num_w, sh.num_io, sh.matrices.clone())?;
      if sh.matrices.len() != template.t {
        return Err(HfsError::InvalidFamily(format!(
          "member {i} has {} matrices, the template has t = {}",
          sh.matrices.len(),
          template.t
        )));
      }
      if (sh.m, sh.num_w, sh.num_io) != (first.m, first.num_w, first.num_io) {
        return Err(HfsError::InvalidFamily(format!(
          "member {i} is {}x({}+1+{}), member 0 is {}x({}+1+{})",
          sh.m, sh.num_w, sh.num_io, first.m, first.num_w, first.num_io
        )));
      }
    }
    let (k, t) = (shapes.len(), template.t);
    let s = num_vars(first.m);
    let s_prime = num_vars(first.n());
    let ck_len = first.num_w.max(1);
    let ck_index_len = t * k;
    let ck = E::CE::setup(CK_LABEL, ck_len);
    let ck_index = E::CE::setup(CK_INDEX_LABEL, ck_index_len);
    let digest = DigestComputer::<E::Scalar, _>::new(&DigestView::<E> {
      version: HFS_TRANSCRIPT_VERSION,
      template: &template,
      shapes: &shapes,
      ck_label: CK_LABEL,
      ck_len,
      ck_index_label: CK_INDEX_LABEL,
      ck_index_len,
    })
    .digest()
    .map_err(|e| HfsError::InvalidFamily(format!("digest: {e}")))?;
    let mut pp = Self {
      template,
      shapes,
      s,
      s_prime,
      ck,
      ck_index,
      iota: Vec::new(),
      ro_consts: RO2Constants::<E>::default(),
      digest,
    };
    pp.iota = (0..k).map(|i| pp.commit_index_all(&pp.e_k(i))).collect();
    Ok(pp)
  }

  /// Family size K.
  pub fn k(&self) -> usize {
    self.shapes.len()
  }

  /// Number of matrices t.
  pub fn t(&self) -> usize {
    self.template.t
  }

  /// The template.
  pub fn template(&self) -> &CcsTemplate<E::Scalar> {
    &self.template
  }

  /// Predicate `k`.
  pub fn shape(&self, k: usize) -> &CcsShape<E::Scalar> {
    &self.shapes[k]
  }

  /// All predicates.
  pub fn shapes(&self) -> &[CcsShape<E::Scalar>] {
    &self.shapes
  }

  /// Rows m.
  pub fn m(&self) -> usize {
    self.shapes[0].m
  }

  /// Witness length.
  pub fn num_w(&self) -> usize {
    self.shapes[0].num_w
  }

  /// Public io length.
  pub fn num_io(&self) -> usize {
    self.shapes[0].num_io
  }

  /// Columns n.
  pub fn n(&self) -> usize {
    self.shapes[0].n()
  }

  /// Row variables s.
  pub fn s(&self) -> usize {
    self.s
  }

  /// Column variables s'.
  pub fn s_prime(&self) -> usize {
    self.s_prime
  }

  /// Structure digest (absorbed first after the input tag).
  pub fn digest(&self) -> E::Scalar {
    self.digest
  }

  /// ι_k = (Com(ck_index[j], e_k))_j.
  pub fn iota(&self, k: usize) -> &[Commitment<E>] {
    &self.iota[k]
  }

  pub(crate) fn ro_consts(&self) -> &RO2Constants<E> {
    &self.ro_consts
  }

  /// Unit vector e_k of length K.
  pub fn e_k(&self, k: usize) -> Vec<E::Scalar> {
    let mut e = vec![E::Scalar::ZERO; self.k()];
    e[k] = E::Scalar::ONE;
    e
  }

  /// `Com(ck, w)` without blinding (the scheme is not zero-knowledge).
  pub fn commit_w(&self, w: &[E::Scalar]) -> Result<Commitment<E>, HfsError> {
    check_len("witness", self.num_w(), w.len())?;
    Ok(E::CE::commit(&self.ck, w, &E::Scalar::ZERO))
  }

  /// `comm_M[j] = Com(ck_index[jK..(j+1)K], λ)`.
  pub fn commit_index(&self, j: usize, lambda: &[E::Scalar]) -> Result<Commitment<E>, HfsError> {
    check_len("lambda", self.k(), lambda.len())?;
    if j >= self.t() {
      return Err(HfsError::Shape {
        what: "index commitment slot".into(),
        expected: self.t(),
        got: j,
      });
    }
    let mut v = vec![E::Scalar::ZERO; j * self.k()];
    v.extend_from_slice(lambda);
    Ok(E::CE::commit(&self.ck_index, &v, &E::Scalar::ZERO))
  }

  fn commit_index_all(&self, lambda: &[E::Scalar]) -> Vec<Commitment<E>> {
    (0..self.t())
      .map(|j| self.commit_index(j, lambda).expect("lambda has length K"))
      .collect()
  }
}
