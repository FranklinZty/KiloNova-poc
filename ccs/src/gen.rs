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
