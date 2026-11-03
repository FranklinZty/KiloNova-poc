# P2 acceptance report: native CCS construction and ACCS reference checker

Date: 2026-10-20. Plan: `docs/P2-plan.md`. Base: `de3bd5d` (P1) plus the uncommitted P2 changes, so the records say `implementation_dirty: true`.

## 1. Goal

PLAN.md §3 P2: real support for high-degree constraints, plus a slow correctness oracle that is independent of the protocol code. P3 needs both: to generalise the HFS beyond (t=3, d=2), and to check every fold over the native field once B15 is fixed.

## 2. Scope implemented

**Decision recorded (PLAN.md asks for it): the checker was written from scratch rather than ported from `folding/`.** `folding/` uses arkworks/BLS12-381 and the `(u ‖ io ‖ w)` layout, and has the B11/B12/B14 defects. A port would have needed a field-conversion layer plus three fixes in code we do not trust. `folding/` is untouched; a layout adapter is provided instead.

| Item | Where |
|---|---|
| Workspace crate `kn-ccs`, generic over `ff::PrimeField`, deps `ff`, `rand_core`, `rand_chacha` only. No dependency on Nova or `kilonova/`. | `ccs/` |
| `SparseMatrix` in canonical form; validated triplet constructor; strict canonical constructor for decoding | `ccs/src/matrix.rs` |
| `Ccs` + `Template` (t, multisets with repeats, coefficients); `z = (w ‖ u ‖ io)`; `residual`, `is_satisfied`. Templates `r1cs()`, `power(d)` (repeated multiset), `product(d)`. | `ccs/src/ccs.rs` |
| `NativeCcsBuilder` (rows written per template matrix over `Var::{W, One, Io}`; the witness is generated with the shape) | `ccs/src/builder.rs` |
| MLE evaluators with kilonova's conventions (sparse), and an independent dense evaluator by successive halving | `ccs/src/mle.rs` |
| Reference relations `check_cccs` and `check_accs` over a K-member `Family` (λ-weighted claims, z-claim), with typed errors that name the failed condition | `ccs/src/accs.rs` |
| `pad` (same rule as `R1CSShape::pad`), `pad_z`, `embed_zero_terms`, `lift_degree`, `overhead` | `ccs/src/pad.rs` |
| Canonical encoding; the decoder rejects non-reduced field elements, unsorted or duplicate entries, explicit zeros, out-of-range indices, forged lengths, bad magic and trailing bytes | `ccs/src/encode.rs` |
| Deterministic generators: random satisfiable CCS for any template; fifth-power chain natively and as R1CS | `ccs/src/gen.rs` |
| `(u ‖ io ‖ w)` ↔ `(w ‖ u ‖ io)` adapter | `ccs/src/layout.rs` |
| Kilonova conventions cross-test (Nova dev-dependency on `kn-ccs`) | `Nova/src/kilonova/test_utils.rs::test_kn_ccs_matches_kilonova_conventions` |
| `kn-scenario ccs`: fifth-power chain, native vs R1CS, both checked by the oracle, recorded by `kn-run` | `tools/kn-run/src/bin/kn-scenario.rs` |

No protocol, transcript or circuit code changed. B15 is untouched.

## 3. Test configuration

Apple M4, 16 GiB, Darwin 25.6.0, rustc 1.92.0, `--release`, one rayon thread for `kn-run` records. Development machine; no performance claims.

## 4. Results

```bash
cargo fmt --all --check                                                         # clean
cargo clippy -p kn-ccs -p kn-run -p nova-snark --release --all-targets -- -W clippy::all -A clippy::len_without_is_empty   # clean
cargo test -p kn-ccs --release                                                  # 20 passed
cargo test -p kn-run --release -- --test-threads=1                              # 10 passed
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1           # 29 passed, 5 ignored (P1: 28 + the conventions test)
target/release/kn-run selfcheck --quick                                         # 8 checks, 0 failed (harness unchanged)
results/raw/p2-ccs.jsonl                                                        # 16 records, all success
```

| PLAN.md P2 criterion | Evidence | Result |
|---|---|---|
| d = 2, 3, 5, 8, 16: ≥100 deterministic random small instances each agree with naive evaluation | `ccs/tests/agreement.rs`: 100 seeds × 5 degrees × {`power(d)`, `product(d)`} × {Pallas Fp, Fq} = 2,000 instances, plus 100 R1CS. In every instance the sparse residual equals the naive dense residual (and is zero), every sparse matrix and z MLE equals the dense halving evaluator, `check_cccs`/`check_accs` accept, and perturbing any `v[j]` is reported as `Claim { j }`. In 61–69 of every 100 instances a witness entry read by the solved matrix exists; tampering it makes both paths reject and breaks the commitment. λ-weighted family claims match for K = 1, 2, 4, 16. | ✅ |
| Fifth power uses a repeated multiset and no intermediate witnesses; difference from equivalent R1CS reported | multiset `[0,0,0,0,0]`, t = 2, q = 2, d = 5. Per T steps: native m = T, w = T − 1, nnz = 3T; R1CS m = 3T, w = 3T − 1, nnz = 10T (asserted for T = 1, 2, 16, 64 and recorded for T up to 1024; R1CS/native = 3.0× rows, ≈3.0× witness, 3.33× non-zeros). Same public input and output. | ✅ |
| Tampered witnesses, out-of-range indices, wrong dimensions and non-canonical encodings rejected; all-zero matrices and boundary sizes tested | `ccs/tests/rejection.rs` (9 tests): every malformed ACCS field gives its named error (Dimension, Commitment, Claim{t} for u/io, Claim{0} for λ/r_x); unsatisfied CCCS; mismatched family; 9 encoding attacks; all-zero matrices satisfied by any z; m = 1 / n = 1 / m = 0. | ✅ |
| Semantics preserved across embedding and padding; overhead measured | `ccs/tests/embedding.rs`: 100 instances each for `pad`, `embed_zero_terms` (R1CS into a t = 5, q = 3, d = 5 template) and `lift_degree` (R1CS to d = 5). Satisfied stays satisfied, tampered stays unsatisfied, residuals are identical row by row. Padding adds no non-zeros and grows Σ m·n by 2.84× over the 100 instances. Embedding adds no non-zeros. Lifting adds m non-zeros (one u-selector per row). | ✅ |
| (Extra) Same conventions as kilonova | 20 random R1CS shapes with num_io = 2: `kn_ccs::pad` equals `R1CSShape::pad` entry for entry; `s_max`, `s_prime_max` equal `num_vars(m)`, `num_vars(n)`; `eval_matrix_predicate` and `eval_z` equal the kn-ccs evaluators at random points | ✅ |

Determinism: `kn-run scenario ccs steps=1024 --seed 101` gave input `7dc650f0…` and result `8c5be20b…` in three separate invocations (two scratch runs and the recorded one). Seeds 202 and 303 give different digests.

Oracle cost at T = 1024 (dev machine, for orientation only): native check 0.18–0.22 ms, R1CS check 0.34–0.45 ms.

## 5. Known limitations

- The `power`, `product` and random templates are synthetic. The only semantic high-degree relation is the fifth-power chain. Poseidon (W2) is P8/P9 work.
- `lift_degree` preserves the relation only for u = 1 (fresh instances). A test shows the residual changes for u = 2. Any family embedding used for relaxed (folded) instances must use zero-term embedding instead, or be re-derived in P3/P4.
- The commitment in `check_accs`/`check_cccs` is a caller-supplied closure. The tests use a toy linear form, so commitment *binding* is not tested here; P3 plugs in Pedersen.
- The cross-test compares evaluations over `E::Base` on projected entries, because that is where kilonova evaluates today (B15). After P3 it must compare over the native field.
- The first `kn-scenario` exec after a build took about 100 ms (T=1, seed 101); the others took 2.7 ms. This is the known macOS first-launch effect (P1 report).

## 6. Entry conditions for P3

- P3.0 (D1 decision spike) can start. P2 provides the oracle and the conventions it must keep.
- P3 must call `kn_ccs::accs::check_accs` on every fold output in its 100-step alternating test (PLAN.md P3 acceptance), with a Pedersen `commit` closure, over the instance's native field.
- When the HFS is generalised to (t, q, d), `kn_ccs::Template` is the reference description of the template.
