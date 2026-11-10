//! Fixed predicate family and index-span paths (PLAN.md P4).
//!
//! - [`PredicateFamily`]: the authenticated list of the K predicate shapes the HFS folds over,
//!   with **stable member ids**, a shared public interface (state arity, `num_io`), one CCS
//!   template, identical padded dimensions, a selector (φ) descriptor and a **family digest**.
//!   [`HfsParams::from_family`] makes the family digest the digest absorbed by every HFS v2
//!   transcript, and the recursive layer binds it in `pp_digest` and in every link hash.
//! - The **canonical matrix encoding** ([`encode_member`]) is byte-identical to
//!   `kn_ccs::encode::encode` (pinned by a test against the oracle crate, which stays a
//!   dev-dependency): `"KNCCS\x01" | m | num_w | num_io | t | q | q × (coeff | len | indices) |
//!   t × (nnz | nnz × (row | col | value))`, entries sorted by (row, col), duplicates summed,
//!   zeros dropped, integers u64 little-endian, field elements `F::Repr`.
//! - Index-span paths: the **explicit folded-matrix path** [`FoldedMatrices`]
//!   (`M_{λ,j} = Σ_k λ_k M_{k,j}`, built from λ or step by step with the fold rule
//!   `M ← M + w·M_k`) and the **weighted-evaluation path** [`weighted_eval`]
//!   (`Σ_k λ_k M̃_{k,j}(r_x, r_y)` over the fixed base matrices). The tests cross-check both
//!   against each other, the protocol's claims, the decider and the kn-ccs oracle.
//! - [`SupportStats`]: union of supports and the bytes of the base matrices, the explicit
//!   folded matrices and λ (the K-dependent density cost, `docs/protocol-spec.md` §10).
use crate::{
  digest::{DigestComputer, SimpleDigestible},
  kilonova::hfs::{CcsShape, CcsTemplate, HfsError, HfsParams},
  traits::Engine,
};
use ff::PrimeField;
use serde::Serialize;
use sha3::{Digest, Sha3_256};

#[cfg(test)]
mod tests;

/// Version of the family digest layout.
pub const FAMILY_VERSION: u64 = 1;
/// Magic and version of the canonical CCS encoding (same as `kn_ccs::encode`).
const MAGIC: &[u8; 6] = b"KNCCS\x01";

/// A sparse matrix in canonical form: `(row, col, value)` sorted by (row, col), no duplicate
/// positions and no zero values.
pub type Entries<F> = Vec<(usize, usize, F)>;

/// Canonical form of arbitrary entries: sorted, duplicates summed, zeros dropped (the rule of
/// `kn_ccs::SparseMatrix::from_triplets`).
pub fn canonical_entries<F: PrimeField>(entries: &[(usize, usize, F)]) -> Entries<F> {
  let mut all = entries.to_vec();
  all.sort_by_key(|e| (e.0, e.1));
  let mut out: Entries<F> = Vec::with_capacity(all.len());
  for (r, c, v) in all {
    match out.last_mut() {
      Some(last) if last.0 == r && last.1 == c => last.2 += v,
      _ => out.push((r, c, v)),
    }
  }
  out.retain(|e| !bool::from(e.2.is_zero()));
  out
}

fn write_encoding<F: PrimeField>(
  template: &CcsTemplate<F>,
  shape: &CcsShape<F>,
  sink: &mut impl FnMut(&[u8]),
) {
  let u = |v: usize| (v as u64).to_le_bytes();
  sink(MAGIC);
  for v in [
    shape.m(),
    shape.num_w(),
    shape.num_io(),
    template.t(),
    template.q(),
  ] {
    sink(&u(v));
  }
  for (c, s) in template.coeffs().iter().zip(template.multisets()) {
    sink(c.to_repr().as_ref());
    sink(&u(s.len()));
    for &j in s {
      sink(&u(j));
    }
  }
  for mat in shape.matrices() {
    let entries = canonical_entries(mat);
    sink(&u(entries.len()));
    for (r, c, v) in entries {
      sink(&u(r));
      sink(&u(c));
      sink(v.to_repr().as_ref());
    }
  }
}

/// The canonical encoding of one member (byte-identical to `kn_ccs::encode::encode`).
pub fn encode_member<F: PrimeField>(template: &CcsTemplate<F>, shape: &CcsShape<F>) -> Vec<u8> {
  let mut out = Vec::new();
  write_encoding(template, shape, &mut |b| out.extend_from_slice(b));
  out
}

/// `SHA3-256` of the canonical encoding, streamed (the encoding is never materialised).
pub fn member_digest<F: PrimeField>(template: &CcsTemplate<F>, shape: &CcsShape<F>) -> [u8; 32] {
  let mut h = Sha3_256::new();
  write_encoding(template, shape, &mut |b| h.update(b));
  h.finalize().into()
}

/// Everything about a family except its matrices (kept by the public parameters).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FamilyMeta<F: PrimeField> {
  label: String,
  ids: Vec<String>,
  arity: usize,
  num_io: usize,
  selector: Vec<u8>,
  member_digests: Vec<[u8; 32]>,
  digest: F,
}

impl<F: PrimeField> FamilyMeta<F> {
  /// Family name.
  pub fn label(&self) -> &str {
    &self.label
  }

  /// Stable member ids; position k is the protocol id of member `ids[k]`.
  pub fn ids(&self) -> &[String] {
    &self.ids
  }

  /// Family size K.
  pub fn k(&self) -> usize {
    self.ids.len()
  }

  /// Arity of the state (public interface).
  pub fn arity(&self) -> usize {
    self.arity
  }

  /// Canonical bytes describing the selector φ.
  pub fn selector(&self) -> &[u8] {
    &self.selector
  }

  /// SHA3-256 of each member's canonical encoding.
  pub fn member_digests(&self) -> &[[u8; 32]] {
    &self.member_digests
  }

  /// The family digest.
  pub fn digest(&self) -> F {
    self.digest
  }

  /// Position (protocol id) of a stable id.
  pub fn position(&self, id: &str) -> Option<usize> {
    self.ids.iter().position(|x| x == id)
  }

  /// Rejects (layer Input) unless the digest is `expected`.
  pub fn check_digest(&self, expected: F) -> Result<(), HfsError> {
    if self.digest == expected {
      Ok(())
    } else {
      Err(HfsError::InvalidFamily(
        "family digest differs from the pinned digest (reordered or substituted member?)".into(),
      ))
    }
  }

  /// Rejects (layer Input) unless `shape` is exactly member `k` (canonical encoding).
  pub fn check_member(
    &self,
    k: usize,
    template: &CcsTemplate<F>,
    shape: &CcsShape<F>,
  ) -> Result<(), HfsError> {
    let d = self
      .member_digests
      .get(k)
      .ok_or(HfsError::PredicateId { id: k, k: self.k() })?;
    if *d == member_digest(template, shape) {
      Ok(())
    } else {
      Err(HfsError::InvalidFamily(format!(
        "member {k} ({}) does not match its canonical encoding (substituted matrix)",
        self.ids[k]
      )))
    }
  }
}

#[derive(Serialize)]
struct FamilyDigestView<'a> {
  version: u64,
  label: &'a str,
  arity: usize,
  num_io: usize,
  selector: &'a [u8],
  ids: &'a [String],
  members: &'a [[u8; 32]],
  ck_label: &'a [u8],
  ck_len: usize,
  ck_index_label: &'a [u8],
  ck_index_len: usize,
}

impl SimpleDigestible for FamilyDigestView<'_> {}

/// A fixed predicate family: K members sharing the public interface, the template and the padded
/// dimensions, with stable ids and a digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateFamily<F: PrimeField> {
  meta: FamilyMeta<F>,
  template: CcsTemplate<F>,
  shapes: Vec<CcsShape<F>>,
}

impl<F: PrimeField> PredicateFamily<F> {
  /// Validates the members (K ≥ 1, unique non-empty ids, one template, t matrices each, entries
  /// in range, identical dimensions) and computes the digest.
  pub fn new(
    label: impl Into<String>,
    ids: Vec<String>,
    arity: usize,
    selector: Vec<u8>,
    template: CcsTemplate<F>,
    shapes: Vec<CcsShape<F>>,
  ) -> Result<Self, HfsError> {
    let label = label.into();
    let first = shapes
      .first()
      .ok_or_else(|| HfsError::InvalidFamily("empty family".into()))?;
    if ids.len() != shapes.len() {
      return Err(HfsError::InvalidFamily(format!(
        "{} ids for {} members",
        ids.len(),
        shapes.len()
      )));
    }
    for (i, id) in ids.iter().enumerate() {
      if id.is_empty() {
        return Err(HfsError::InvalidFamily(format!(
          "member {i} has an empty id"
        )));
      }
      if ids[..i].contains(id) {
        return Err(HfsError::InvalidFamily(format!("duplicate member id {id}")));
      }
    }
    let template = CcsTemplate::new(
      template.t(),
      template.multisets().to_vec(),
      template.coeffs().to_vec(),
    )?;
    for (i, sh) in shapes.iter().enumerate() {
      CcsShape::new(sh.m(), sh.num_w(), sh.num_io(), sh.matrices().to_vec())?;
      if sh.matrices().len() != template.t() {
        return Err(HfsError::InvalidFamily(format!(
          "member {i} has {} matrices, the template has t = {}",
          sh.matrices().len(),
          template.t()
        )));
      }
      if (sh.m(), sh.num_w(), sh.num_io()) != (first.m(), first.num_w(), first.num_io()) {
        return Err(HfsError::InvalidFamily(format!(
          "member {i} is {}x({}+1+{}), member 0 is {}x({}+1+{})",
          sh.m(),
          sh.num_w(),
          sh.num_io(),
          first.m(),
          first.num_w(),
          first.num_io()
        )));
      }
    }
    let member_digests: Vec<[u8; 32]> = shapes
      .iter()
      .map(|sh| member_digest(&template, sh))
      .collect();
    let num_io = first.num_io();
    let digest = DigestComputer::<F, _>::new(&FamilyDigestView {
      version: FAMILY_VERSION,
      label: &label,
      arity,
      num_io,
      selector: &selector,
      ids: &ids,
      members: &member_digests,
      ck_label: crate::kilonova::hfs::CK_LABEL,
      ck_len: first.num_w().max(1),
      ck_index_label: crate::kilonova::hfs::CK_INDEX_LABEL,
      ck_index_len: template.t() * shapes.len(),
    })
    .digest()
    .map_err(|e| HfsError::InvalidFamily(format!("digest: {e}")))?;
    Ok(Self {
      meta: FamilyMeta {
        label,
        ids,
        arity,
        num_io,
        selector,
        member_digests,
        digest,
      },
      template,
      shapes,
    })
  }

  /// The metadata (ids, digests).
  pub fn meta(&self) -> &FamilyMeta<F> {
    &self.meta
  }

  /// The family digest.
  pub fn digest(&self) -> F {
    self.meta.digest
  }

  /// Family size K.
  pub fn k(&self) -> usize {
    self.shapes.len()
  }

  /// The shared template.
  pub fn template(&self) -> &CcsTemplate<F> {
    &self.template
  }

  /// The members, in protocol order.
  pub fn shapes(&self) -> &[CcsShape<F>] {
    &self.shapes
  }

  /// The HFS parameters of this family (moves the matrices) and the metadata.
  pub fn into_hfs_params<E: Engine<Scalar = F>>(
    self,
  ) -> Result<(HfsParams<E>, FamilyMeta<F>), HfsError> {
    let pp = HfsParams::<E>::build(self.template, self.shapes, Some(self.meta.digest))?;
    Ok((pp, self.meta))
  }
}

// ---------------------------------------------------------------------------------------------
// Index-span paths
// ---------------------------------------------------------------------------------------------

/// `eq(p, ·)` over the hypercube, entry `b = Σ b_i 2^i` is `Π_i (b_i ? p_i : 1 − p_i)`. Written
/// separately from the HFS sum-check and the decider (independent evaluation path).
fn eq_table<F: PrimeField>(p: &[F]) -> Vec<F> {
  let mut t = vec![F::ONE; 1 << p.len()];
  for (i, r) in p.iter().enumerate() {
    let stride = 1 << i;
    for (b, v) in t.iter_mut().enumerate() {
      *v *= if b & stride != 0 { *r } else { F::ONE - r };
    }
  }
  t
}

fn eval_entries<F: PrimeField>(entries: &[(usize, usize, F)], ex: &[F], ey: &[F]) -> F {
  entries
    .iter()
    .fold(F::ZERO, |acc, &(r, c, v)| acc + v * ex[r] * ey[c])
}

/// `a + w·b` for canonical `a`, `b`; the result is canonical (exact cancellations dropped).
fn merge_add<F: PrimeField>(a: &[(usize, usize, F)], b: &[(usize, usize, F)], w: F) -> Entries<F> {
  let mut out = Vec::with_capacity(a.len() + b.len());
  let (mut i, mut j) = (0, 0);
  while i < a.len() || j < b.len() {
    let take_a = j >= b.len() || (i < a.len() && (a[i].0, a[i].1) < (b[j].0, b[j].1));
    let take_b = i >= a.len() || (j < b.len() && (b[j].0, b[j].1) < (a[i].0, a[i].1));
    let e = if take_a {
      i += 1;
      a[i - 1]
    } else if take_b {
      j += 1;
      (b[j - 1].0, b[j - 1].1, w * b[j - 1].2)
    } else {
      i += 1;
      j += 1;
      (a[i - 1].0, a[i - 1].1, a[i - 1].2 + w * b[j - 1].2)
    };
    if !bool::from(e.2.is_zero()) {
      out.push(e);
    }
  }
  out
}

/// Explicit folded matrices `M_{λ,j} = Σ_k λ_k M_{k,j}` (canonical), with the λ they encode.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldedMatrices<F: PrimeField> {
  mats: Vec<Entries<F>>,
  lambda: Vec<F>,
}

impl<F: PrimeField> FoldedMatrices<F> {
  /// λ = 0, all matrices zero.
  pub fn zero(t: usize, k: usize) -> Self {
    Self {
      mats: vec![Vec::new(); t],
      lambda: vec![F::ZERO; k],
    }
  }

  /// Builds `Σ_k λ_k M_k` directly from λ.
  pub fn from_lambda(shapes: &[CcsShape<F>], lambda: &[F]) -> Self {
    let t = shapes.first().map_or(0, |s| s.matrices().len());
    let mut out = Self::zero(t, shapes.len());
    for (k, l) in lambda.iter().enumerate() {
      if !bool::from(l.is_zero()) {
        out.fold(shapes, *l, k);
      }
    }
    out
  }

  /// One fold step with weight `w` on the incoming member `k`: `M ← M + w·M_k`, `λ ← λ + w·e_k`
  /// (HFS v2 with μ = ν = 1 uses w = ρ; the first fold from μ = 0 uses w = 1).
  pub fn fold(&mut self, shapes: &[CcsShape<F>], w: F, k: usize) {
    for (j, m) in self.mats.iter_mut().enumerate() {
      let base = canonical_entries(&shapes[k].matrices()[j]);
      *m = merge_add(m, &base, w);
    }
    self.lambda[k] += w;
  }

  /// The λ these matrices encode.
  pub fn lambda(&self) -> &[F] {
    &self.lambda
  }

  /// Matrix j.
  pub fn matrix(&self, j: usize) -> &[(usize, usize, F)] {
    &self.mats[j]
  }

  /// Non-zeros of matrix j.
  pub fn nnz_of(&self, j: usize) -> usize {
    self.mats[j].len()
  }

  /// Non-zeros over all t matrices.
  pub fn nnz(&self) -> usize {
    self.mats.iter().map(Vec::len).sum()
  }

  /// `(M̃_{λ,j}(r_x, r_y))_j` evaluated on the explicit matrices.
  pub fn eval(&self, r_x: &[F], r_y: &[F]) -> Vec<F> {
    let (ex, ey) = (eq_table(r_x), eq_table(r_y));
    self
      .mats
      .iter()
      .map(|m| eval_entries(m, &ex, &ey))
      .collect()
  }

  /// Bytes of the explicit representation (entry = two u64 indices + one field element).
  pub fn bytes(&self) -> usize {
    self.nnz() * entry_bytes::<F>()
  }
}

fn entry_bytes<F: PrimeField>() -> usize {
  16 + F::Repr::default().as_ref().len()
}

/// The weighted-evaluation path: `(Σ_k λ_k M̃_{k,j}(r_x, r_y))_j` over the base matrices.
pub fn weighted_eval<F: PrimeField>(
  shapes: &[CcsShape<F>],
  lambda: &[F],
  r_x: &[F],
  r_y: &[F],
) -> Vec<F> {
  let t = shapes.first().map_or(0, |s| s.matrices().len());
  let (ex, ey) = (eq_table(r_x), eq_table(r_y));
  (0..t)
    .map(|j| {
      shapes
        .iter()
        .zip(lambda)
        .filter(|(_, l)| !bool::from(l.is_zero()))
        .fold(F::ZERO, |acc, (sh, l)| {
          acc + *l * eval_entries(&sh.matrices()[j], &ex, &ey)
        })
    })
    .collect()
}

/// Support growth and storage of the index-span representations of a family.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct SupportStats {
  /// Family size.
  pub k: usize,
  /// Matrices per member.
  pub t: usize,
  /// Rows and columns.
  pub m: usize,
  /// Columns.
  pub n: usize,
  /// Canonical non-zeros of each member (all t matrices).
  pub member_nnz: Vec<usize>,
  /// Σ over members.
  pub sum_nnz: usize,
  /// Largest member.
  pub max_nnz: usize,
  /// `Σ_j |∪_k supp(M_{k,j})|`: non-zeros of a folded matrix once λ is dense (no cancellation).
  pub union_nnz: usize,
  /// `union_nnz / max_nnz`: density growth of the explicit folded matrix over one member.
  pub union_over_max: f64,
  /// `union_nnz / sum_nnz`: overlap (1 = disjoint supports, 1/K = identical supports).
  pub union_over_sum: f64,
  /// Bytes of the K base matrices (fixed preprocessing, both paths).
  pub base_bytes: usize,
  /// Bytes of an explicit folded matrix with dense λ (extra state of the explicit path).
  pub folded_bytes: usize,
  /// Bytes of λ (state of the weighted path / Span public index).
  pub lambda_bytes: usize,
}

/// Measures the supports of `shapes`.
pub fn support_stats<F: PrimeField>(shapes: &[CcsShape<F>]) -> SupportStats {
  let t = shapes.first().map_or(0, |s| s.matrices().len());
  let member_nnz: Vec<usize> = shapes
    .iter()
    .map(|s| {
      s.matrices()
        .iter()
        .map(|m| canonical_entries(m).len())
        .sum()
    })
    .collect();
  let mut union_nnz = 0;
  for j in 0..t {
    let mut pos: Vec<(usize, usize)> = shapes
      .iter()
      .flat_map(|s| {
        canonical_entries(&s.matrices()[j])
          .into_iter()
          .map(|e| (e.0, e.1))
      })
      .collect();
    pos.sort_unstable();
    pos.dedup();
    union_nnz += pos.len();
  }
  let sum_nnz: usize = member_nnz.iter().sum();
  let max_nnz = member_nnz.iter().copied().max().unwrap_or(0);
  let eb = entry_bytes::<F>();
  SupportStats {
    k: shapes.len(),
    t,
    m: shapes.first().map_or(0, |s| s.m()),
    n: shapes.first().map_or(0, |s| s.n()),
    member_nnz,
    sum_nnz,
    max_nnz,
    union_nnz,
    union_over_max: union_nnz as f64 / max_nnz.max(1) as f64,
    union_over_sum: union_nnz as f64 / sum_nnz.max(1) as f64,
    base_bytes: sum_nnz * eb,
    folded_bytes: union_nnz * eb,
    lambda_bytes: shapes.len() * F::Repr::default().as_ref().len(),
  }
}
