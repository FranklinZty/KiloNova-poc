//! Deterministic generators: random satisfiable CCS for any template, and the fifth-power
//! chain written natively (degree 5) and as the equivalent R1CS.
use crate::{
  builder::{eval_lc, Lc},
  Assignment, Ccs, CcsError, NativeCcsBuilder, SparseMatrix, Template, Var,
};
use ff::PrimeField;
use rand_core::RngCore;

/// A random satisfiable CCS with `s` random non-zeros per row in every matrix, and a random
/// assignment `(w, 1, io)`.
///
/// Satisfiability: the last term of the template must be a single matrix `L` that no other
/// term uses. Each row of `L` gets `s − 1` random entries plus one entry in the u column chosen
/// so the row sums to zero (u = 1). No effective constraint is made trivially zero.
pub fn random_satisfiable<F: PrimeField>(
  template: &Template<F>,
  m: usize,
  num_w: usize,
  num_io: usize,
  s: usize,
  rng: &mut impl RngCore,
) -> Result<(Ccs<F>, Assignment<F>), CcsError> {
  template.validate()?;
  let last = template.q() - 1;
  let l = match template.multisets[last].as_slice() {
    [l] => *l,
    _ => {
      return Err(CcsError::InvalidTemplate(
        "the last term must be a single matrix".into(),
      ))
    }
  };
  if template.multisets[..last].iter().any(|ms| ms.contains(&l)) {
    return Err(CcsError::InvalidTemplate(format!(
      "matrix {l} of the last term is used by another term"
    )));
  }
  let c_l = template.coeffs[last];
  let c_l_inv = Option::<F>::from(c_l.invert())
    .ok_or_else(|| CcsError::InvalidTemplate("last coefficient is zero".into()))?;

  let n = num_w + 1 + num_io;
  let w: Vec<F> = (0..num_w).map(|_| F::random(&mut *rng)).collect();
  let io: Vec<F> = (0..num_io).map(|_| F::random(&mut *rng)).collect();
  let a = Assignment { w, io };
  let z = a.z();
  let u_col = num_w;
  let col = |rng: &mut dyn RngCore| (rng.next_u64() as usize) % n;

  let mut triplets: Vec<Vec<(usize, usize, F)>> = vec![Vec::new(); template.t];
  for (j, tr) in triplets.iter_mut().enumerate() {
    let per_row = if j == l { s.saturating_sub(1) } else { s };
    for row in 0..m {
      for _ in 0..per_row {
        tr.push((row, col(&mut *rng), F::random(&mut *rng)));
      }
    }
  }
  // Row values of every matrix except L, and the partial value of L.
  let row_val = |tr: &[(usize, usize, F)], row: usize| -> F {
    tr.iter()
      .filter(|e| e.0 == row)
      .fold(F::ZERO, |acc, e| acc + e.2 * z[e.1])
  };
  for row in 0..m {
    let mut partial = c_l * row_val(&triplets[l], row);
    for (ms, c) in template.multisets[..last].iter().zip(&template.coeffs) {
      partial += ms
        .iter()
        .fold(*c, |acc, &j| acc * row_val(&triplets[j], row));
    }
    // c_L · x · u = −partial with u = 1.
    triplets[l].push((row, u_col, -partial * c_l_inv));
  }
  let matrices = triplets
    .into_iter()
    .map(|t| SparseMatrix::from_triplets(m, n, t))
    .collect::<Result<Vec<_>, _>>()?;
  let ccs = Ccs::new(m, num_w, num_io, template.clone(), matrices)?;
  Ok((ccs, a))
}

/// Constant of the fifth-power step `x_{i+1} = x_i^5 + K5`.
pub const K5: u64 = 7;

/// Native degree-5 chain of `steps ≥ 1` steps: io = (x_0, x_T), witness = x_1..x_{T−1}.
/// Each step is one row of `(M₀ z)^5 − M₁ z = 0` with `M₀` selecting `x_i` and `M₁` giving
/// `x_{i+1} − K5`. The multiset is `[0, 0, 0, 0, 0]`; no intermediate witness is allocated.
pub fn fifth_power_native<F: PrimeField>(
  steps: usize,
  x0: Option<F>,
) -> Result<(Ccs<F>, Option<Assignment<F>>), CcsError> {
  let mut b = NativeCcsBuilder::new(Template::power(5))?;
  let k = F::from(K5);
  let x_in = b.alloc_io(x0);
  let mut xs = vec![x_in];
  let mut cur = x0;
  for _ in 1..steps {
    cur = cur.map(|x| x.pow_vartime([5]) + k);
    xs.push(b.alloc_w(cur));
  }
  let x_out = b.alloc_io(cur.map(|x| x.pow_vartime([5]) + k));
  xs.push(x_out);
  for i in 0..steps {
    b.push_row(vec![
      vec![(xs[i], F::ONE)],
      vec![(xs[i + 1], F::ONE), (Var::One, -k)],
    ])?;
  }
  b.build()
}

/// The same chain as R1CS: per step `a = x·x`, `b = a·a`, `x' − K5 = b·x` (3 rows, 2 extra
/// witnesses).
pub fn fifth_power_r1cs<F: PrimeField>(
  steps: usize,
  x0: Option<F>,
) -> Result<(Ccs<F>, Option<Assignment<F>>), CcsError> {
  let mut b = NativeCcsBuilder::new(Template::r1cs())?;
  let k = F::from(K5);
  let one = |v: Var| -> Lc<F> { vec![(v, F::ONE)] };
  let mut x = b.alloc_io(x0);
  for step in 0..steps {
    let xv = b.value(x);
    let a = b.alloc_w(xv.map(|x| x.square()));
    let sq = b.value(a).map(|a| a.square());
    let bb = b.alloc_w(sq);
    let next_val = b.value(bb).zip(xv).map(|(bv, xv)| bv * xv + k);
    let next = if step + 1 == steps {
      b.alloc_io(next_val)
    } else {
      b.alloc_w(next_val)
    };
    b.push_row(vec![one(x), one(x), one(a)])?;
    b.push_row(vec![one(a), one(a), one(bb)])?;
    let c: Lc<F> = vec![(next, F::ONE), (Var::One, -k)];
    debug_assert!(eval_lc(&b, &c).is_some() || xv.is_none());
    b.push_row(vec![one(bb), one(x), c])?;
    x = next;
  }
  b.build()
}

/// Template of a [`wiring_pair`] family.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairTemplate {
  /// R1CS (t = 3, d = 2).
  R1cs,
  /// `power(5)`: `(M₀ z)^5 − M₁ z = 0` (t = 2, d = 5).
  Power5,
}

impl PairTemplate {
  pub fn name(self) -> &'static str {
    match self {
      PairTemplate::R1cs => "r1cs",
      PairTemplate::Power5 => "power5",
    }
  }

  pub fn template<F: PrimeField>(self) -> Template<F> {
    match self {
      PairTemplate::R1cs => Template::r1cs(),
      PairTemplate::Power5 => Template::power(5),
    }
  }
}

/// Predicate `k ∈ {0, 1}` of a two-member family whose members share the template and the
/// dimensions but differ in wiring (the P3 / B15 fixture). Coefficients include negative values,
/// and every value is a full-width field element, so products wrap. `reps ≥ 1` copies of the
/// gadget are chained (the output of copy r is the input of copy r + 1, as a witness); io is
/// `(x, y)`.
///
/// - R1CS, k = 0: `a = x·x`, `a·x = y + 3x − 11`. k = 1: `a = x·(−x)`, `(a + 2)·x = y − 7`.
/// - power(5), k = 0: `x⁵ = w + 3`, `(w + x)⁵ = y − x`. k = 1: `(2x − 1)⁵ = w`,
///   `(w − x)⁵ = y + 2x`.
///
/// Per copy: 2 rows. Witness: `reps` gadget values plus `reps − 1` chained outputs.
pub fn wiring_pair<F: PrimeField>(
  template: PairTemplate,
  k: usize,
  reps: usize,
  x: Option<F>,
) -> Result<(Ccs<F>, Option<Assignment<F>>), CcsError> {
  if k > 1 || reps == 0 {
    return Err(CcsError::Family(format!(
      "wiring_pair needs k in {{0, 1}} and reps >= 1 (got k = {k}, reps = {reps})"
    )));
  }
  let one = |v: Var| -> Lc<F> { vec![(v, F::ONE)] };
  let c = |v: u64| F::from(v);
  let p5 = |v: F| v.pow_vartime([5]);
  let mut b = NativeCcsBuilder::new(template.template())?;
  let mut xv = b.alloc_io(x);
  for r in 0..reps {
    let xval = b.value(xv);
    let last = r + 1 == reps;
    let out = |b: &mut NativeCcsBuilder<F>, v: Option<F>| {
      if last {
        b.alloc_io(v)
      } else {
        b.alloc_w(v)
      }
    };
    xv = match (template, k) {
      (PairTemplate::R1cs, 0) => {
        let a = b.alloc_w(xval.map(|x| x.square()));
        let y = out(&mut b, xval.map(|x| x.square() * x - x * c(3) + c(11)));
        b.push_row(vec![one(xv), one(xv), one(a)])?;
        b.push_row(vec![
          one(a),
          one(xv),
          vec![(y, F::ONE), (xv, c(3)), (Var::One, -c(11))],
        ])?;
        y
      }
      (PairTemplate::R1cs, _) => {
        let a = b.alloc_w(xval.map(|x| -x.square()));
        let y = out(&mut b, xval.map(|x| (c(2) - x.square()) * x + c(7)));
        b.push_row(vec![one(xv), vec![(xv, -F::ONE)], one(a)])?;
        b.push_row(vec![
          vec![(a, F::ONE), (Var::One, c(2))],
          one(xv),
          vec![(y, F::ONE), (Var::One, -c(7))],
        ])?;
        y
      }
      (PairTemplate::Power5, 0) => {
        let w = b.alloc_w(xval.map(|x| p5(x) - c(3)));
        let y = out(&mut b, xval.map(|x| p5(p5(x) - c(3) + x) + x));
        b.push_row(vec![one(xv), vec![(w, F::ONE), (Var::One, c(3))]])?;
        b.push_row(vec![
          vec![(w, F::ONE), (xv, F::ONE)],
          vec![(y, F::ONE), (xv, -F::ONE)],
        ])?;
        y
      }
      (PairTemplate::Power5, _) => {
        let w = b.alloc_w(xval.map(|x| p5(x.double() - F::ONE)));
        let y = out(
          &mut b,
          xval.map(|x| p5(p5(x.double() - F::ONE) - x) - x.double()),
        );
        b.push_row(vec![vec![(xv, c(2)), (Var::One, -F::ONE)], one(w)])?;
        b.push_row(vec![
          vec![(w, F::ONE), (xv, -F::ONE)],
          vec![(y, F::ONE), (xv, c(2))],
        ])?;
        y
      }
    };
  }
  b.build()
}
