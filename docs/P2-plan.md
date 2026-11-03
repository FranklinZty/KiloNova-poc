# P2 plan: native CCS construction and ACCS reference checker (2026-10-20)

PLAN.md §3 P2. Acceptance report: `docs/P2-report.md`.

## Context

P3 has to generalise the HFS from (t=3, d=2) to real CCS and fold over the native field (B15). It needs two things that do not exist yet: a way to **build** native high-degree CCS relations, and a **slow, independent oracle** that says whether an ACCS/CCCS instance–witness pair is in the relation. `folding/` has generic CCS algebra but uses arkworks/BLS12-381, the `(u ‖ io ‖ w)` layout and a reversed variable order, and has the B11/B12/B14 defects.

**Decision (PLAN.md asks for it to be recorded): write the checker from scratch.** Porting `folding/` would need an arkworks→ff conversion layer plus three bug fixes in code we do not trust. A minimal ff-generic checker is smaller, and being independent of both `folding/` and `kilonova/` is what an oracle needs. `folding/` is not touched. A `(u ‖ io ‖ w)` ↔ `(w ‖ u ‖ io)` adapter is still provided, so vectors from `folding/` can be imported.

## Design: new workspace crate `ccs/` (package `kn-ccs`)

Generic over `ff::PrimeField` only, with no curve, commitment or Nova dependency. Commitments enter the ACCS/CCCS checks through a caller-supplied closure, so P3 can plug in Pedersen.

| Module | Content |
|---|---|
| `matrix.rs` | `SparseMatrix<F>`: canonical form (row-major sorted, no duplicates, no explicit zeros), validated constructor from triplets (rejects out-of-range indices), mat-vec, dense view |
| `ccs.rs` | `Ccs<F>{m, num_w, num_io, matrices, multisets, coeffs}` with `n = num_w + 1 + num_io`, `t`, `q`, `d = max |S_k|`. Layout `z = (w ‖ u ‖ io)` (spec N2). `validate()`, `is_satisfied(z)` (row-wise, multisets with repeats), `residual(z)`. `Template` = (t, multisets, coeffs) fixed per family: `r1cs()`, `power(d)` (one matrix repeated d times), `product(d)` (d distinct matrices) |
| `builder.rs` | `NativeCcsBuilder`: allocate witness/io variables with optional values, push rows as one linear combination per matrix over `Var::{W, One, Io}`. `build()` maps variables to columns in the frozen layout and returns `(Ccs, Option<Assignment>)`. Witness generation is part of building. |
| `pad.rs` | `pad()` mirrors `R1CSShape::pad`: m' = next_pow2(max(num_w, m, num_io)), num_w = m = m', u/io columns renumbered; `pad_z`. `embed_zero_terms` (extend to a larger template with zero matrices) and `lift_degree` (multiply terms by the u-selector to reach a uniform degree; exact only for u = 1, which is stated). Overhead is reported. |
| `mle.rs` | `bits_le`, `eq_eval` (bit i ↔ point[i], spec N9), sparse evaluators `eval_matrix_mle(M, r_x, r_y)` and `eval_vec_mle(z, r_y)` with s = log2(next_pow2(m)) and s' = log2(next_pow2(n)), plus an **independent dense evaluator** (successive halving of the full table) used as the naive cross-check |
| `accs.rs` | `CccsInstance{comm_w, io}` + witness `w` (u = 1); `AccsInstance{comm_w, u, io, lambda, r_x, r_y, v[t+1]}` over a family of K CCS sharing a template and padded dimensions: `v_j = Σ_i λ_i M̃_{i,j}(r_x, r_y)` and `v_t = z̃(r_y)` with `z = (w ‖ u ‖ io)`. `check_cccs` and `check_accs` return a typed error naming the failed condition (dimension, commitment, claim j, z-claim). λ = e_k gives the single-predicate case. |
| `encode.rs` | Canonical byte encoding of `Ccs`. `decode` rejects non-canonical field elements (≥ p), unsorted or duplicate entries, explicit zeros, out-of-range indices, trailing bytes and invalid templates. |
| `gen.rs` | Deterministic (ChaCha) generators: random satisfiable CCS for any template with s non-zeros per row (the last single-matrix term is solved through the u column), fifth-power chain (native, degree 5, one row per step), and the equivalent R1CS chain built with the same builder |
| `layout.rs` | `(u ‖ io ‖ w)` ↔ `(w ‖ u ‖ io)` adapter for vectors and matrix columns |

Kilonova conventions cross-test (`Nova/src/kilonova/test_utils.rs`, dev-dependency on `kn-ccs`): take a real padded predicate shape from `GlobalStructure` and check that `eval_matrix_predicate` / `eval_z` equal `kn-ccs` evaluated on the same (projected) entries at random points. This pins bit order, layout and padding for P3. It compares in `E::Base` because that is where kilonova evaluates today (B15).

`kn-scenario ccs` (P1 harness): builds the fifth-power chain natively and as R1CS for T steps, checks both with the oracle, and records m, n, w, nnz, t, q, d plus the checker time in a `kn-run` record.

## Acceptance → tests

| PLAN.md P2 criterion | Test |
|---|---|
| d = 2, 3, 5, 8, 16: ≥100 deterministic random small instances each agree with naive evaluation | `tests/agreement.rs`: for both `power(d)` and `product(d)` templates over two fields (Pallas Fp and Fq), 100 seeds per d. Sparse mat-vec vs dense mat-vec satisfaction, sparse MLE vs dense-halving MLE for every `v_j` and `v_t`, `check_accs` accepts. One tampered witness entry per instance → rejected by both paths. |
| Fifth power uses a repeated multiset, no intermediate witnesses; difference from equivalent R1CS reported | `fifth_power_*`: asserts multiset `[0,0,0,0,0]`, m = T, w = T + 1, versus R1CS m = 3T, w = 3T + 1. Exact nnz both ways, printed and recorded by `kn-scenario ccs`. |
| Tampered witnesses, out-of-range indices, wrong dimensions, non-canonical encodings rejected; all-zero matrices and boundary sizes tested | `tests/rejection.rs` |
| Semantics preserved across embedding and padding; overhead measured | `tests/embedding.rs`: satisfied ⇔ satisfied (and tampered stays unsatisfied) through `pad`, `embed_zero_terms`, `lift_degree`; the honest ACCS of a padded instance passes `check_accs` (padding renumbers the u/io columns, so claims are not compared point by point across padding); overhead (m, n, nnz, t, q) reported |

Definition of done: fmt, clippy on `ccs/`, the kilonova suite unchanged, `cargo test -p kn-ccs --release`, and `kn-run scenario ccs` records.

Out of scope: protocol changes (P3), Nova integration beyond the conventions test, and fixing `folding/`.
