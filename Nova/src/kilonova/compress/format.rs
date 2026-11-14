//! Canonical proof format v1, its byte account, and the public material file.
//!
//! Proof file (`docs/protocol-spec.md` §12.4):
//!
//! ```text
//! "KNCP" | version u16 | kind u8 | variant u8 | sections u16 = 9
//! 9 × (tag u8 | len u32 LE | payload)       tags 1..9 in order, all present
//! ```
//!
//! Field elements are 32-byte canonical little-endian representations, points 32-byte
//! compressed encodings, integers little endian. Sections 1–7 have no internal length prefixes:
//! every length follows from the public material. Sections 8 (IPA) and 9 (Spartan) are the
//! inherited serde objects in bincode legacy encoding. [`decode`] checks every section length
//! against the material, rejects non-canonical elements and invalid points, requires every
//! payload to be consumed exactly, and finally requires `encode(decode(bytes)) == bytes`.
use super::{
  CfSnark, CompressError, CompressedProof, FinalStatement, FinalVariant, FinalVerifierKey,
  MaterialHeader, ProofHead, ProofKind, COMPRESS_VERSION, E1, E2, F1,
};
use crate::{
  kilonova::{
    family::{decode_member, encode_member},
    hfs::{CcsShape, CcsTemplate, HfsParams, HfsProof, IncomingInstance, RunningInstance},
    hfs::Variant,
    ivc::PublicParams,
    pcd::{NodeStatement, TaskCtx, TreeParams},
  },
  provider::ipa_pc::InnerProductArgument,
  r1cs::RelaxedR1CSInstance,
  traits::Engine,
  Commitment,
};
use ff::PrimeField;
use serde::{de::DeserializeOwned, Serialize};
use std::io::{Read, Write};

/// Magic of the proof file.
pub const PROOF_MAGIC: &[u8; 4] = b"KNCP";
/// Magic of the public material file.
pub const MATERIAL_MAGIC: &[u8; 4] = b"KNVM";
/// Number of sections of a v1 proof.
pub const NUM_SECTIONS: usize = 9;
/// Section names, in tag order (tag = index + 1).
pub const SECTIONS: [&str; NUM_SECTIONS] = [
  "binding",
  "statement",
  "running",
  "incoming",
  "cf_instance",
  "fold_proof",
  "index_opening",
  "witness_opening",
  "cf_snark",
];
/// Bytes of the file header.
pub const HEADER_BYTES: usize = 4 + 2 + 1 + 1 + 2;
/// Bytes of a section's framing (tag + length).
pub const FRAMING_BYTES: usize = 1 + 4;

fn bincode_bytes<T: Serialize>(v: &T) -> Vec<u8> {
  bincode::serde::encode_to_vec(v, bincode::config::legacy()).expect("bincode encoding")
}

fn bincode_exact<T: DeserializeOwned>(b: &[u8], what: &str) -> Result<T, CompressError> {
  let (v, used): (T, usize) = bincode::serde::decode_from_slice(b, bincode::config::legacy())
    .map_err(|e| CompressError::Format(format!("{what}: {e}")))?;
  if used != b.len() {
    return Err(CompressError::Format(format!("{what}: trailing bytes")));
  }
  Ok(v)
}

/// Canonical byte writer.
#[derive(Default)]
pub struct Writer {
  pub(crate) buf: Vec<u8>,
}

impl Writer {
  fn u8(&mut self, x: u8) {
    self.buf.push(x);
  }
  fn u16(&mut self, x: u16) {
    self.buf.extend_from_slice(&x.to_le_bytes());
  }
  fn u64(&mut self, x: u64) {
    self.buf.extend_from_slice(&x.to_le_bytes());
  }
  /// A field element (32-byte canonical repr).
  pub fn scalar<F: PrimeField>(&mut self, x: &F) {
    self.buf.extend_from_slice(x.to_repr().as_ref());
  }
  fn scalars<F: PrimeField>(&mut self, xs: &[F]) {
    xs.iter().for_each(|x| self.scalar(x));
  }
  /// A point (32-byte compressed encoding).
  pub fn point<E: Engine>(&mut self, c: &Commitment<E>) {
    let b = bincode_bytes(c);
    debug_assert_eq!(b.len(), 32);
    self.buf.extend_from_slice(&b);
  }
}

/// Strict byte reader.
pub struct Reader<'a> {
  bytes: &'a [u8],
  pos: usize,
}

impl<'a> Reader<'a> {
  fn new(bytes: &'a [u8]) -> Self {
    Self { bytes, pos: 0 }
  }
  fn take(&mut self, n: usize) -> Result<&'a [u8], CompressError> {
    let end = self
      .pos
      .checked_add(n)
      .filter(|&e| e <= self.bytes.len())
      .ok_or_else(|| CompressError::Format("truncated".into()))?;
    let out = &self.bytes[self.pos..end];
    self.pos = end;
    Ok(out)
  }
  fn done(&self, what: &str) -> Result<(), CompressError> {
    if self.pos == self.bytes.len() {
      Ok(())
    } else {
      Err(CompressError::Format(format!("{what}: trailing bytes")))
    }
  }
  fn u8(&mut self) -> Result<u8, CompressError> {
    Ok(self.take(1)?[0])
  }
  fn u16(&mut self) -> Result<u16, CompressError> {
    Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
  }
  fn u32(&mut self) -> Result<u32, CompressError> {
    Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
  }
  fn u64(&mut self) -> Result<u64, CompressError> {
    Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
  }
  /// A canonical field element.
  pub fn scalar<F: PrimeField>(&mut self) -> Result<F, CompressError> {
    let mut repr = F::Repr::default();
    let n = repr.as_ref().len();
    repr.as_mut().copy_from_slice(self.take(n)?);
    Option::from(F::from_repr(repr))
      .ok_or_else(|| CompressError::Format("non-canonical field element".into()))
  }
  fn scalars<F: PrimeField>(&mut self, n: usize) -> Result<Vec<F>, CompressError> {
    (0..n).map(|_| self.scalar()).collect()
  }
  /// A valid compressed point.
  pub fn point<E: Engine>(&mut self) -> Result<Commitment<E>, CompressError> {
    bincode_exact(self.take(32)?, "point")
  }
}

/// Dimensions every section length follows from (all from the verifier's material).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Dims {
  /// State arity (chain) / result length (tree).
  pub arity: usize,
  /// Public io of the primary relation.
  pub num_io: usize,
  /// Row variables.
  pub s: usize,
  /// Column variables.
  pub s_prime: usize,
  /// Matrices per member.
  pub t: usize,
  /// Family size.
  pub k: usize,
  /// X-round polynomial degree.
  pub deg_x: usize,
  /// CycleFold public inputs.
  pub n_cf: usize,
  /// CycleFold padded size (constraints = variables).
  pub n_cf_rows: usize,
}

impl Dims {
  fn of<V: FinalVariant>(vk: &FinalVerifierKey<V>) -> Self {
    let hfs: &HfsParams<E1> = vk.hfs();
    Self {
      arity: vk.arity(),
      num_io: hfs.num_io(),
      s: hfs.s(),
      s_prime: hfs.s_prime(),
      t: hfs.t(),
      k: hfs.k(),
      deg_x: hfs.template().deg_x(),
      n_cf: vk.cyclefold_shape().num_io,
      n_cf_rows: vk.cyclefold_shape().num_cons,
    }
  }

  fn statement_bytes(&self, kind: ProofKind) -> usize {
    match kind {
      ProofKind::Chain => 8 + 64 * self.arity + 32,
      ProofKind::Tree => 32 + 4 * 8 + 32 * self.arity + 32,
    }
  }

  fn running_bytes<V: FinalVariant>(&self) -> usize {
    32 + V::index_bytes(self.t, self.k) + 32 * (1 + self.num_io + self.s + self.s_prime + self.t + 1)
  }

  fn fold_bytes(&self) -> usize {
    32 * (self.s * (self.deg_x + 1) + 2 * self.t + 3 * self.s_prime + 2 * (self.t + 1))
  }

  fn ipa_bytes(rounds: usize) -> usize {
    2 * (8 + 32 * rounds) + 32
  }

  /// Bytes of the Spartan proof for a padded CycleFold shape of `n` rows (= variables).
  pub fn spartan_bytes(n: usize) -> usize {
    let nx = n.trailing_zeros() as usize;
    let ny = nx + 1;
    (8 + nx * (8 + 3 * 32)) // outer sum-check, degree 3
      + 3 * 32 // claims_outer
      + 32 // eval_E
      + (8 + ny * (8 + 2 * 32)) // inner sum-check, degree 2
      + 32 // eval_W
      + (8 + nx * (8 + 2 * 32)) // batch sum-check, degree 2
      + (8 + 2 * 32) // evals_batch
      + Self::ipa_bytes(nx) // eval_arg
  }

  /// Expected payload length of every section.
  pub fn section_bytes<V: FinalVariant>(&self, kind: ProofKind) -> [usize; NUM_SECTIONS] {
    [
      64,
      self.statement_bytes(kind),
      self.running_bytes::<V>(),
      8 + 32 + 32 * self.num_io,
      32 * (3 + self.n_cf),
      self.fold_bytes(),
      32 * V::revealed_len(self.k),
      Self::ipa_bytes(self.s_prime),
      Self::spartan_bytes(self.n_cf_rows),
    ]
  }

  /// Expected total proof length.
  pub fn proof_bytes<V: FinalVariant>(&self, kind: ProofKind) -> usize {
    HEADER_BYTES + NUM_SECTIONS * FRAMING_BYTES + self.section_bytes::<V>(kind).iter().sum::<usize>()
  }
}

fn section(out: &mut Vec<u8>, tag: u8, payload: &[u8]) {
  out.push(tag);
  out.extend_from_slice(&(payload.len() as u32).to_le_bytes());
  out.extend_from_slice(payload);
}

fn payload_head<V: FinalVariant>(h: &ProofHead<V>) -> [Vec<u8>; 7] {
  let mut b = Writer::default();
  b.scalar(&h.pp_digest);
  b.scalar(&h.family_digest);

  let mut st = Writer::default();
  match &h.statement {
    FinalStatement::Chain { n, z0, zn, trace } => {
      st.u64(*n);
      st.scalars(z0);
      st.scalars(zn);
      st.scalar(trace);
    }
    FinalStatement::Tree { ctx, a, stmt } => {
      st.scalar(&ctx.task_id);
      st.u64(ctx.num_leaves);
      st.u64(*a);
      st.u64(stmt.lo);
      st.u64(stmt.hi);
      st.scalars(&stmt.result);
      st.scalar(&stmt.tree_hash);
    }
  }

  let mut ru = Writer::default();
  let u = &h.running;
  ru.point::<E1>(&u.comm_w);
  V::write_index(&mut ru, &u.index);
  ru.scalar(&u.u);
  ru.scalars(&u.io);
  ru.scalars(&u.r_x);
  ru.scalars(&u.r_y);
  ru.scalars(&u.v);

  let mut inc = Writer::default();
  inc.u64(h.incoming.k as u64);
  inc.point::<E1>(&h.incoming.comm_w);
  inc.scalars(&h.incoming.io);

  let mut cf = Writer::default();
  cf.point::<E2>(&h.cf.comm_W);
  cf.point::<E2>(&h.cf.comm_E);
  cf.scalar(&h.cf.u);
  cf.scalars(&h.cf.X);

  let mut fo = Writer::default();
  for v in h
    .fold
    .sc_x
    .iter()
    .chain(&h.fold.sigma)
    .chain(&h.fold.tau)
    .chain(&h.fold.sc_y)
    .chain(&h.fold.eps)
    .chain(&h.fold.theta)
  {
    fo.scalars(v);
  }

  let mut la = Writer::default();
  la.scalars(&h.lambda);
  [b.buf, st.buf, ru.buf, inc.buf, cf.buf, fo.buf, la.buf]
}

fn file_header(kind: ProofKind, variant: u8) -> Vec<u8> {
  let mut w = Writer::default();
  w.buf.extend_from_slice(PROOF_MAGIC);
  w.u16(COMPRESS_VERSION);
  w.u8(kind.code());
  w.u8(variant);
  w.u16(NUM_SECTIONS as u16);
  w.buf
}

/// Header and sections 1–7 (what the compression transcript binds before the openings).
pub fn encode_head<V: FinalVariant>(h: &ProofHead<V>) -> Vec<u8> {
  let mut out = file_header(h.kind, V::CODE);
  for (i, p) in payload_head(h).iter().enumerate() {
    section(&mut out, (i + 1) as u8, p);
  }
  out
}

/// The canonical proof bytes.
pub fn encode<V: FinalVariant>(p: &CompressedProof<V>) -> Vec<u8> {
  let mut out = encode_head(&p.head);
  section(&mut out, 8, &bincode_bytes(&p.w_open));
  section(&mut out, 9, &bincode_bytes(&p.cf_snark));
  out
}

/// Decodes a proof file for the verifier's material (layer Format on any deviation).
pub fn decode<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  bytes: &[u8],
) -> Result<CompressedProof<V>, CompressError> {
  let fmt = |m: String| CompressError::Format(m);
  let d = Dims::of(vk);
  let kind = vk.kind();
  let mut r = Reader::new(bytes);
  if r.take(4)? != PROOF_MAGIC {
    return Err(fmt("magic".into()));
  }
  let version = r.u16()?;
  if version != COMPRESS_VERSION {
    return Err(fmt(format!("version {version}")));
  }
  let (k_code, v_code, n_sec) = (r.u8()?, r.u8()?, r.u16()?);
  if k_code != kind.code() || v_code != V::CODE || n_sec as usize != NUM_SECTIONS {
    return Err(fmt(format!(
      "kind {k_code} variant {v_code} sections {n_sec}; expected {} {} {NUM_SECTIONS}",
      kind.code(),
      V::CODE
    )));
  }
  let expected = d.section_bytes::<V>(kind);
  let mut payloads = Vec::with_capacity(NUM_SECTIONS);
  for (i, &len) in expected.iter().enumerate() {
    let tag = r.u8()?;
    let got = r.u32()? as usize;
    if tag as usize != i + 1 {
      return Err(fmt(format!("section {} has tag {tag}", i + 1)));
    }
    if got != len {
      return Err(fmt(format!(
        "section {} ({}) has length {got}, expected {len}",
        i + 1,
        SECTIONS[i]
      )));
    }
    payloads.push(r.take(len)?);
  }
  r.done("proof")?;

  let mut b = Reader::new(payloads[0]);
  let (pp_digest, family_digest) = (b.scalar()?, b.scalar()?);
  b.done("binding")?;

  let mut st = Reader::new(payloads[1]);
  let statement = match kind {
    ProofKind::Chain => FinalStatement::Chain {
      n: st.u64()?,
      z0: st.scalars(d.arity)?,
      zn: st.scalars(d.arity)?,
      trace: st.scalar()?,
    },
    ProofKind::Tree => {
      let task_id = st.scalar()?;
      let num_leaves = st.u64()?;
      let a = st.u64()?;
      let (lo, hi) = (st.u64()?, st.u64()?);
      FinalStatement::Tree {
        ctx: TaskCtx {
          task_id,
          num_leaves,
        },
        a,
        stmt: NodeStatement {
          lo,
          hi,
          result: st.scalars(d.arity)?,
          tree_hash: st.scalar()?,
        },
      }
    }
  };
  st.done("statement")?;

  let mut ru = Reader::new(payloads[2]);
  let running = RunningInstance::<E1, V> {
    comm_w: ru.point::<E1>()?,
    index: V::read_index(&mut ru, d.t, d.k)?,
    u: ru.scalar()?,
    io: ru.scalars(d.num_io)?,
    r_x: ru.scalars(d.s)?,
    r_y: ru.scalars(d.s_prime)?,
    v: ru.scalars(d.t + 1)?,
  };
  ru.done("running")?;

  let mut inc = Reader::new(payloads[3]);
  let k = inc.u64()?;
  if k >= d.k as u64 {
    return Err(fmt(format!("incoming predicate {k} >= K = {}", d.k)));
  }
  let incoming = IncomingInstance::<E1> {
    k: k as usize,
    comm_w: inc.point::<E1>()?,
    io: inc.scalars(d.num_io)?,
  };
  inc.done("incoming")?;

  let mut cf = Reader::new(payloads[4]);
  let cf_u = RelaxedR1CSInstance::<E2> {
    comm_W: cf.point::<E2>()?,
    comm_E: cf.point::<E2>()?,
    u: cf.scalar()?,
    X: cf.scalars(d.n_cf)?,
  };
  cf.done("cf_instance")?;

  let mut fo = Reader::new(payloads[5]);
  let mut rows = |n: usize, w: usize| -> Result<Vec<Vec<F1>>, CompressError> {
    (0..n).map(|_| fo.scalars(w)).collect()
  };
  let fold = HfsProof::<E1> {
    sc_x: rows(d.s, d.deg_x + 1)?,
    sigma: rows(1, d.t)?,
    tau: rows(1, d.t)?,
    sc_y: rows(d.s_prime, 3)?,
    eps: rows(1, d.t + 1)?,
    theta: rows(1, d.t + 1)?,
  };
  fo.done("fold_proof")?;

  let mut la = Reader::new(payloads[6]);
  let lambda = la.scalars(V::revealed_len(d.k))?;
  la.done("index_opening")?;

  let w_open: InnerProductArgument<E1> = bincode_exact(payloads[7], "witness_opening")?;
  let cf_snark: CfSnark = bincode_exact(payloads[8], "cf_snark")?;

  let p = CompressedProof {
    head: ProofHead {
      kind,
      pp_digest,
      family_digest,
      statement,
      running,
      incoming,
      cf: cf_u,
      fold,
      lambda,
    },
    w_open,
    cf_snark,
  };
  if encode(&p) != bytes {
    return Err(fmt("not the canonical encoding".into()));
  }
  Ok(p)
}

// ---------------------------------------------------------------------------------------------
// Byte account
// ---------------------------------------------------------------------------------------------

/// One line of the proof-size account.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AccountItem {
  /// Section name ("header", "framing" or one of [`SECTIONS`]).
  pub section: String,
  /// Item within the section.
  pub item: String,
  /// Bytes.
  pub bytes: usize,
  /// Field elements and points (32 bytes each) in this item.
  pub elements: usize,
  /// The size as a function of the parameters.
  pub formula: String,
}

/// The item-by-item account of a proof, from the message format.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProofAccount {
  /// The items, in file order.
  pub items: Vec<AccountItem>,
  /// Σ bytes.
  pub total: usize,
  /// Bytes per section (header and framing first).
  pub by_section: Vec<(String, usize)>,
}

/// The account of `p` against the verifier's dimensions. `total` equals `encode(p).len()`
/// (asserted by the tests), and every item is computed from the format, not by measuring the
/// encoding (except the Spartan sub-items, measured field by field and checked against
/// [`Dims::spartan_bytes`]).
pub fn account<V: FinalVariant>(
  vk: &FinalVerifierKey<V>,
  p: &CompressedProof<V>,
) -> Result<ProofAccount, CompressError> {
  let d = Dims::of(vk);
  let mut items = Vec::new();
  let mut add = |section: &str, item: &str, bytes: usize, elements: usize, formula: String| {
    items.push(AccountItem {
      section: section.into(),
      item: item.into(),
      bytes,
      elements,
      formula,
    })
  };
  add(
    "header",
    "magic, version, kind, variant, section count",
    HEADER_BYTES,
    0,
    "10".into(),
  );
  add(
    "framing",
    "9 × (tag u8, length u32)",
    NUM_SECTIONS * FRAMING_BYTES,
    0,
    "45".into(),
  );
  add("binding", "pp_digest", 32, 1, "32".into());
  add("binding", "family_digest", 32, 1, "32".into());
  let a = d.arity;
  match p.head.kind {
    ProofKind::Chain => {
      add("statement", "n", 8, 0, "8".into());
      add("statement", "z_0", 32 * a, a, format!("32·arity ({a})"));
      add("statement", "z_n", 32 * a, a, format!("32·arity ({a})"));
      add("statement", "trace", 32, 1, "32".into());
    }
    ProofKind::Tree => {
      add("statement", "task_id", 32, 1, "32".into());
      add("statement", "L, a, lo, hi", 32, 0, "4·8".into());
      add("statement", "R", 32 * a, a, format!("32·arity ({a})"));
      add("statement", "tree hash", 32, 1, "32".into());
    }
  }
  add("running", "comm_W", 32, 1, "32".into());
  let ib = V::index_bytes(d.t, d.k);
  add(
    "running",
    if V::DIRECT { "comm_M[t]" } else { "lambda[K]" },
    ib,
    ib / 32,
    if V::DIRECT {
      format!("32·t ({})", d.t)
    } else {
      format!("32·K ({})", d.k)
    },
  );
  add("running", "u", 32, 1, "32".into());
  add("running", "io", 32 * d.num_io, d.num_io, format!("32·num_io ({})", d.num_io));
  add("running", "r_x", 32 * d.s, d.s, format!("32·s ({})", d.s));
  add("running", "r_y", 32 * d.s_prime, d.s_prime, format!("32·s' ({})", d.s_prime));
  add("running", "v", 32 * (d.t + 1), d.t + 1, format!("32·(t+1) ({})", d.t + 1));
  add("incoming", "k", 8, 0, "8".into());
  add("incoming", "comm_W", 32, 1, "32".into());
  add("incoming", "io", 32 * d.num_io, d.num_io, format!("32·num_io ({})", d.num_io));
  add("cf_instance", "comm_W, comm_E", 64, 2, "64".into());
  add("cf_instance", "u", 32, 1, "32".into());
  add("cf_instance", "X", 32 * d.n_cf, d.n_cf, format!("32·n_cf ({})", d.n_cf));
  let sx = d.s * (d.deg_x + 1);
  add(
    "fold_proof",
    "sc_x",
    32 * sx,
    sx,
    format!("32·s·(deg_x+1) ({}·{})", d.s, d.deg_x + 1),
  );
  add("fold_proof", "sigma, tau", 64 * d.t, 2 * d.t, format!("2·32·t ({})", d.t));
  add(
    "fold_proof",
    "sc_y",
    96 * d.s_prime,
    3 * d.s_prime,
    format!("32·3·s' ({})", d.s_prime),
  );
  add(
    "fold_proof",
    "eps, theta",
    64 * (d.t + 1),
    2 * (d.t + 1),
    format!("2·32·(t+1) ({})", d.t + 1),
  );
  let lr = V::revealed_len(d.k);
  add(
    "index_opening",
    "lambda*",
    32 * lr,
    lr,
    if V::DIRECT {
      format!("32·K ({})", d.k)
    } else {
      "0 (Span: lambda* is in U*)".into()
    },
  );
  let sp = d.s_prime;
  add("witness_opening", "IPA L_vec", 8 + 32 * sp, sp, format!("8 + 32·s' ({sp})"));
  add("witness_opening", "IPA R_vec", 8 + 32 * sp, sp, format!("8 + 32·s' ({sp})"));
  add("witness_opening", "IPA a_hat", 32, 1, "32".into());
  let fields = p.cf_snark.field_bytes().map_err(CompressError::from)?;
  let nx = d.n_cf_rows.trailing_zeros() as usize;
  for (name, b) in fields {
    let (f, e) = match name {
      "sc_proof_outer" => (format!("8 + log n_cf_rows·(8 + 3·32) ({nx})"), 3 * nx),
      "claims_outer" => ("3·32".into(), 3),
      "eval_E" | "eval_W" => ("32".into(), 1),
      "sc_proof_inner" => (format!("8 + (log n_cf_rows + 1)·(8 + 2·32) ({nx})"), 2 * (nx + 1)),
      "sc_proof_batch" => (format!("8 + log n_cf_rows·(8 + 2·32) ({nx})"), 2 * nx),
      "evals_batch" => ("8 + 2·32".into(), 2),
      "eval_arg" => (format!("2·(8 + 32·log n_cf_rows) + 32 ({nx})"), 2 * nx + 1),
      _ => ("?".into(), 0),
    };
    add("cf_snark", name, b, e, f);
  }
  let total = items.iter().map(|i| i.bytes).sum();
  let mut by_section: Vec<(String, usize)> = Vec::new();
  for i in &items {
    match by_section.last_mut() {
      Some((s, b)) if *s == i.section => *b += i.bytes,
      _ => by_section.push((i.section.clone(), i.bytes)),
    }
  }
  Ok(ProofAccount {
    items,
    total,
    by_section,
  })
}

// ---------------------------------------------------------------------------------------------
// Public material file
// ---------------------------------------------------------------------------------------------

/// Largest accepted material header and member encoding (a forged length cannot allocate more).
const MAX_HEADER_BYTES: u64 = 1 << 30;
const MAX_MEMBER_BYTES: u64 = 1 << 34;
const MAX_MEMBERS: u64 = 1 << 16;

fn write_material_raw(
  w: &mut impl Write,
  header: &MaterialHeader,
  template: &CcsTemplate<F1>,
  shapes: &[CcsShape<F1>],
) -> std::io::Result<u64> {
  let h = bincode_bytes(header);
  let mut total = 0u64;
  let mut put = |w: &mut dyn Write, b: &[u8]| -> std::io::Result<()> {
    total += b.len() as u64;
    w.write_all(b)
  };
  put(w, MATERIAL_MAGIC)?;
  put(w, &COMPRESS_VERSION.to_le_bytes())?;
  put(w, &(h.len() as u64).to_le_bytes())?;
  put(w, &h)?;
  put(w, &(shapes.len() as u64).to_le_bytes())?;
  for sh in shapes {
    let m = encode_member(template, sh);
    put(w, &(m.len() as u64).to_le_bytes())?;
    put(w, &m)?;
  }
  Ok(total)
}

/// Writes a chain's public material; returns its length in bytes.
pub fn write_material_chain<V: FinalVariant>(
  pp: &PublicParams<E1, E2, V>,
  w: &mut impl Write,
) -> std::io::Result<u64> {
  let f = pp.family();
  let header = MaterialHeader {
    version: COMPRESS_VERSION as u64,
    kind: ProofKind::Chain.code(),
    variant: <V as Variant<E1>>::NAME.into(),
    template: pp.template(),
    arity: f.arity() as u64,
    a: 0,
    k_leaf: 0,
    label: f.label().into(),
    ids: f.ids().to_vec(),
    selector: f.selector().to_vec(),
    cf_shape: pp.cyclefold_shape().clone(),
  };
  write_material_raw(w, &header, pp.hfs().template(), pp.hfs().shapes())
}

/// Writes a tree's public material; returns its length in bytes.
pub fn write_material_tree<V: FinalVariant>(
  pp: &TreeParams<E1, E2, V>,
  w: &mut impl Write,
) -> std::io::Result<u64> {
  let f = pp.family();
  let header = MaterialHeader {
    version: COMPRESS_VERSION as u64,
    kind: ProofKind::Tree.code(),
    variant: <V as Variant<E1>>::NAME.into(),
    template: pp.template(),
    arity: f.arity() as u64,
    a: pp.pcd_arity() as u64,
    k_leaf: pp.k_leaf() as u64,
    label: f.label().into(),
    ids: f.ids().to_vec(),
    selector: f.selector().to_vec(),
    cf_shape: pp.cyclefold_shape().clone(),
  };
  write_material_raw(w, &header, pp.hfs().template(), pp.hfs().shapes())
}

fn read_exact_vec(r: &mut impl Read, n: u64, what: &str) -> Result<Vec<u8>, CompressError> {
  let mut v = Vec::new();
  let got = r
    .take(n)
    .read_to_end(&mut v)
    .map_err(|e| CompressError::Material(format!("{what}: {e}")))?;
  if got as u64 != n {
    return Err(CompressError::Material(format!("{what}: truncated")));
  }
  Ok(v)
}

fn read_u64(r: &mut impl Read, what: &str) -> Result<u64, CompressError> {
  let b = read_exact_vec(r, 8, what)?;
  Ok(u64::from_le_bytes(b.try_into().unwrap()))
}

/// Reads a material file: header and the members' canonical encodings, each decoded strictly
/// (layer Material). Members are decoded one at a time; the encodings are not kept.
#[allow(clippy::type_complexity)]
pub fn read_material(
  r: &mut impl Read,
) -> Result<(MaterialHeader, Vec<(CcsTemplate<F1>, CcsShape<F1>)>), CompressError> {
  let bad = |m: String| CompressError::Material(m);
  if read_exact_vec(r, 4, "magic")? != MATERIAL_MAGIC {
    return Err(bad("magic".into()));
  }
  let v = read_exact_vec(r, 2, "version")?;
  if u16::from_le_bytes([v[0], v[1]]) != COMPRESS_VERSION {
    return Err(bad("version".into()));
  }
  let hl = read_u64(r, "header length")?;
  if hl > MAX_HEADER_BYTES {
    return Err(bad("header length".into()));
  }
  let header: MaterialHeader = bincode_exact(&read_exact_vec(r, hl, "header")?, "header")
    .map_err(|e| bad(format!("{e}")))?;
  let k = read_u64(r, "member count")?;
  if k == 0 || k > MAX_MEMBERS {
    return Err(bad(format!("{k} members")));
  }
  let mut members = Vec::with_capacity(k as usize);
  for i in 0..k {
    let len = read_u64(r, "member length")?;
    if len > MAX_MEMBER_BYTES {
      return Err(bad(format!("member {i} length")));
    }
    let bytes = read_exact_vec(r, len, "member")?;
    members.push(decode_member::<F1>(&bytes).map_err(|e| bad(format!("member {i}: {e}")))?);
  }
  let mut rest = [0u8; 1];
  if r
    .read(&mut rest)
    .map_err(|e| bad(format!("trailing: {e}")))?
    != 0
  {
    return Err(bad("trailing bytes".into()));
  }
  Ok((header, members))
}
