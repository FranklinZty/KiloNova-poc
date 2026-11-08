# Baseline status and blocker register (P0 smoke-test report)

Date: 2026-10-05. Code: P0 changes on top of the repository state of 2026-09-22.

## 1. Environment of these measurements

| Item | Value |
|---|---|
| Machine | Cloud Linux VM, 2 vCPU, 7 GiB RAM, no swap (Claude workspace). **Not** the 16 GB macOS laptop from `docs/P0-plan.md` §1.2 |
| Toolchain | rustc 1.97.0 (2026-07-07). The repo pins 1.92.0 in `rust-toolchain.toml` (the toolchain measured in P0-plan), but **that pin was not exercised here** because the VM could not download it. Re-run the commands below on 1.92.0. |
| Build | `--release`; workspace limited to `Nova/` for the runs (NIFS-circuit unchanged and not rebuilt) |
| Command | `cargo test -p nova-snark --release --lib kilonova -- --test-threads=1` |

## 2. Before and after P0

| Measurement | Before P0 | After P0 |
|---|---|---|
| `setup` fixed point, K=3 toy predicates | Iteration 1: primary 26,897 constraints → **secondary 44,227,419 constraints, 148,969,504 non-zeros**. No fixed point exists, so the process is killed (SIGKILL on 7 GiB; ≈30 GB working set on the 16 GB Mac). | **Converges in 2 iterations**: iteration 1 primary 27,230 / secondary 66,283; iteration 2 primary 72,760 / secondary 72,951 (both padded to 2^17 = 131,072). Exactness check passes. |
| `test_ivc_nontrivial_nonuniform_bootstrap` (1 step) | killed | **passes**: 73 s wall, 3.3 GiB peak RSS (direct). The span variant passes in 39 s. |
| 2-step and 3-step IVC tests (direct and span) | killed | **fail fast** in `prove_step`: `UnSat("HFS zero-check failed: incoming instance is not satisfied over E::Base (B15)")`. Marked `#[ignore = "known issue B15 …"]`. |
| kilonova test suite | 16–19 pass, 6 killed | **25 pass, 5 ignored** (4 × B15 plus 1 perf harness), 181 s |
| clippy (rustc 1.97) on `kilonova/` | several findings in test code | clean; remaining findings are in inherited Nova modules (`frontend/gadgets/num.rs`, `frontend/test_shape_cs.rs`, `spartan/ppsnark.rs`, `spartan/polys/multilinear.rs`, `lib.rs`), which are newer-toolchain lints left untouched |
| `cargo fmt --check` | — | clean |

The before-P0 sizes come from the P0 setup instrumentation (`CountingCS` dry run plus a per-iteration `eprintln!` in test builds) applied to the unmodified gadget.

## 3. Root cause of the memory explosion (B1/B3, corrected)

`docs/P0-plan.md` attributed B1 mainly to the bucket tables (B2). Measurement shows the dominant cause is different. The augmented circuit **re-evaluated σ, τ, ε, θ in-circuit from the other curve's full witness** (`eval_matrix_folded` O(K·nnz) six times, plus `eval_z` O(s′·z_len) twice), and allocated that witness as circuit input. Each circuit therefore holds at least twice the other's witness (|P| ≥ 2|S|, |S| ≥ 2|P|), so no fixed point exists for any predicate set. The native verifier never needed these recomputations. The claims only have to be bound by the transcript (B16) and deferred to the decider.

The P0 fix makes the gadget succinct. The bucket-table change (`new_for_setup` without tables) is kept as a minor memory saving. Converting the buckets to CSR (P0-plan option A, item 2) was **not needed** at these sizes and is deferred.

## 4. Blocker register (B1–B17)

| # | Blocker | Disposition |
|---|---|---|
| B1 | Recursion layer unverified (OOM) | **Fixed** (root cause F1 above). The 1-step chain verifies. Multi-step blocked by B15. |
| B2 | Bucket tables built in every fixed-point iteration | **Fixed**: `new_for_setup` builds no tables |
| B3 | Circuit size feedback through `eval_z` / `eval_matrix_folded` | **Fixed**: the recomputations were removed from the gadget |
| B4 | U1 and ι′ not in the transcript | **Fixed** at all 4 sites, with domain tags. `test_nifs_rejects_substituted_running_instance` fails on the old code and passes on the new. |
| B5 | In-circuit M not bound to commit(λ) (G1) | **Closed by design**: decider check (`docs/claim-check-map.md` §3) |
| B6 | No CompressedSNARK; verify needs witnesses (G2) | Deferred to **P7** |
| B7 | No in-circuit φ; trace supplied to verifier (G3/G4) | Deferred to **P4/P6** |
| B8 | NIFS unit tests only fold predicates with identical coefficients | Deferred to **P3** (needs B15 fixed; a non-trivial-coefficient case is now the B15 evidence test) |
| B9 | `test_cross_predicate_fold_sat` drops sigmas and never calls is_sat | Deferred to **P3** (rewrite with a real cross-predicate NIFS once B15 is fixed) |
| B10 | Test fixtures use empty matrices, `pp_digest = 42` and zero witnesses | Partly addressed: the setup and bootstrap tests now run real augmented circuits. Fixture rewrite in **P3**. |
| B11 | `folding/` serial MLE path uses `data[i]` | `folding/` demoted; fix only if it is used as the P2 oracle |
| B12 | `folding/` silent `zip` truncation and ark-poly invariant violation | As B11 |
| B13 | 5,620 build artifacts tracked in `folding/target` | `.gitignore` fixed. `git rm -r --cached folding/target` **left to the user**, as decided. |
| B14 | `folding/` variable order differs from kilonova | As B11; adapter in P2 |
| **B15** | **HFS over E::Base for R1CS over E::Scalar** (`field_switch` is not a homomorphism) | **Open, critical path.** Evidence: `test_known_issue_b15_scalar_r1cs_not_foldable_over_base`, plus the fast-fail message in `prove_step`. Fix in **P3** (HFS over the native field) and **P5** (CycleFold-style group-operation delegation, or non-native field verification), decided by the P3.0 spike. |
| B16 (new) | σ,τ not absorbed before δ; ε,θ not absorbed before ρ (prover could choose them after seeing the challenge) | **Fixed** (native and gadget, both variants); `test_nifs_rho_binds_y_claims` |
| B17 (new) | Commitment keys sized from unpadded shapes; `RecursiveSNARK::new` panicked (`ck.len() >= v.len()`) | **Fixed**: keys sized from padded shapes and `num_vars_max` |
| **B18** (new, found 2026-11-03 in P3.0) | Inherited Nova tests fail, and did so before P0 (P0 touched none of `provider/`, `nova/`, `spartan/`, `r1cs/`, `traits/` or the lock file): `nova::tests::test_ivc_{nondet,nontrivial}_with_compression` and `test_ivc_nontrivial_with_spark_compression` panic at `provider/pedersen.rs:340` (commitment key shorter than the padded vector, like B17); `test_pp_digest` has a stale pinned digest. Uniform `RecursiveSNARK` tests pass. | **Open.** Not on the B15 path. Must be fixed before P7 (compression reuses Spartan/IPA) and before Nova is used as a P8 baseline. |

## 5. Tests added in P0

| Test | Purpose |
|---|---|
| `kilonova::tests::test_setup_fixed_point_converges` | Records per-iteration sizes (`--nocapture`) and asserts convergence |
| `kilonova::nifs::tests::test_nifs_rejects_substituted_running_instance` | B4 |
| `kilonova::nifs::tests::test_nifs_rho_binds_y_claims` | B16 |
| `kilonova::nifs::tests::test_known_issue_b15_scalar_r1cs_not_foldable_over_base` | B15 evidence; flip when fixed |
| `kilonova::test_utils::tests::test_transcript_native_matches_gadget_{direct,span}` | Native and gadget transcripts agree, including ρ (P0.3 cross-implementation vector test) |

## 6. Reproduce

```bash
# whole suite (≈3 min on 2 vCPU; needs ≤ 4 GiB)
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1
# fixed-point sizes
cargo test -p nova-snark --release --lib kilonova::tests::test_setup_fixed_point_converges -- --nocapture
# show the B15 failure
cargo test -p nova-snark --release --lib kilonova::tests::test_ivc_nontrivial_nonuniform_smoke -- --ignored --test-threads=1
```
