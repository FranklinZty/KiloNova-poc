//! Canonical byte encoding of a CCS. `decode(encode(c)) == c`, and `decode` rejects every
//! byte string that is not the canonical encoding of a valid CCS.
//!
//! Layout (integers are u64 little-endian, field elements are `F::Repr`):
//! `"KNCCS" 0x01 | m | num_w | num_io | t | q | q × (coeff | len | len × index) |
//!  t × (nnz | nnz × (row | col | value))`.
use crate::{Ccs, CcsError, SparseMatrix, Template};
use ff::PrimeField;

const MAGIC: &[u8; 6] = b"KNCCS\x01";

fn put_u64(out: &mut Vec<u8>, v: usize) {
  out.extend_from_slice(&(v as u64).to_le_bytes());
}

fn put_fe<F: PrimeField>(out: &mut Vec<u8>, v: &F) {
  out.extend_from_slice(v.to_repr().as_ref());
}

pub fn encode<F: PrimeField>(ccs: &Ccs<F>) -> Vec<u8> {
  let mut out = MAGIC.to_vec();
  for v in [ccs.m, ccs.num_w, ccs.num_io, ccs.template.t, ccs.q()] {
    put_u64(&mut out, v);
  }
  for (c, s) in ccs.template.coeffs.iter().zip(&ccs.template.multisets) {
    put_fe(&mut out, c);
    put_u64(&mut out, s.len());
    for &j in s {
      put_u64(&mut out, j);
    }
  }
  for mat in &ccs.matrices {
    put_u64(&mut out, mat.nnz());
    for (r, c, v) in mat.entries() {
      put_u64(&mut out, *r);
      put_u64(&mut out, *c);
      put_fe(&mut out, v);
    }
  }
  out
}

struct Reader<'a> {
  buf: &'a [u8],
  pos: usize,
}

impl Reader<'_> {
  fn take(&mut self, n: usize) -> Result<&[u8], CcsError> {
    let end = self
      .pos
      .checked_add(n)
      .filter(|&e| e <= self.buf.len())
      .ok_or_else(|| CcsError::NonCanonical(format!("truncated at byte {}", self.pos)))?;
    let s = &self.buf[self.pos..end];
    self.pos = end;
    Ok(s)
  }

  fn u64(&mut self) -> Result<usize, CcsError> {
    let b: [u8; 8] = self.take(8)?.try_into().unwrap();
    usize::try_from(u64::from_le_bytes(b))
      .map_err(|_| CcsError::NonCanonical("integer does not fit usize".into()))
  }

  /// A length that must be backed by at least `unit` bytes per item, so a forged length
  /// cannot trigger a huge allocation.
  fn len(&mut self, unit: usize) -> Result<usize, CcsError> {
    let n = self.u64()?;
    if n.saturating_mul(unit) > self.buf.len() - self.pos {
      return Err(CcsError::NonCanonical(format!(
        "length {n} exceeds the input"
      )));
    }
    Ok(n)
  }

  fn fe<F: PrimeField>(&mut self) -> Result<F, CcsError> {
    let mut repr = F::Repr::default();
    let n = repr.as_ref().len();
    repr.as_mut().copy_from_slice(self.take(n)?);
    Option::from(F::from_repr(repr))
      .ok_or_else(|| CcsError::NonCanonical("field element is not reduced".into()))
  }
}

pub fn decode<F: PrimeField>(bytes: &[u8]) -> Result<Ccs<F>, CcsError> {
  let fe_len = F::Repr::default().as_ref().len();
  let mut r = Reader { buf: bytes, pos: 0 };
  if r.take(MAGIC.len())? != MAGIC {
    return Err(CcsError::NonCanonical("bad magic or version".into()));
  }
  let (m, num_w, num_io, t) = (r.u64()?, r.u64()?, r.u64()?, r.u64()?);
  let q = r.len(fe_len + 8)?;
  let n = num_w
    .checked_add(1 + num_io)
    .ok_or_else(|| CcsError::NonCanonical("column count overflows".into()))?;
  let mut coeffs = Vec::with_capacity(q);
  let mut multisets = Vec::with_capacity(q);
  for _ in 0..q {
    coeffs.push(r.fe::<F>()?);
    let len = r.len(8)?;
    multisets.push((0..len).map(|_| r.u64()).collect::<Result<Vec<_>, _>>()?);
  }
  let template = Template {
    t,
    multisets,
    coeffs,
  };
  template.validate()?;
  let mut matrices = Vec::with_capacity(t);
  for _ in 0..t {
    let nnz = r.len(16 + fe_len)?;
    let entries = (0..nnz)
      .map(|_| Ok((r.u64()?, r.u64()?, r.fe::<F>()?)))
      .collect::<Result<Vec<_>, CcsError>>()?;
    matrices.push(SparseMatrix::from_canonical(m, n, entries)?);
  }
  if r.pos != bytes.len() {
    return Err(CcsError::NonCanonical(format!(
      "{} trailing bytes",
      bytes.len() - r.pos
    )));
  }
  Ccs::new(m, num_w, num_io, template, matrices)
}
