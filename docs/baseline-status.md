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
| B7 | No in-circuit φ; trace supplied to verifier (G3/G4) | Deferred to **P4/P6**. P5 (v2 recursion): the trace is a Poseidon chain computed in-circuit over each circuit's constant id (N15 closed for v2); the verifier still receives the schedule (G3) and there is no φ (G4). |
| B8 | NIFS unit tests only fold predicates with identical coefficients | **Closed in P3 for the v2 HFS**: `hfs::tests::test_chain_100_{r1cs,power5}_{direct,span}` fold two predicates with different wiring, negative coefficients and wrapping values for 100 alternating steps, every step accepted by the verifier, the decider and the kn-ccs oracle. The v1 unit tests are unchanged. |
| B9 | `test_cross_predicate_fold_sat` drops sigmas and never calls is_sat | **Superseded in P3** by the v2 cross-predicate tests (real NIFS, decider and oracle on every fold: the chain tests, `test_mu_nu_combinations`, `proptest_random_ccs_fold`). The v1 test itself is unchanged (v1 is frozen until P5). |
| B10 | Test fixtures use empty matrices, `pp_digest = 42` and zero witnesses | **Closed for v2 in P3**: v2 tests use `kn_ccs::gen::wiring_pair` and `random_satisfiable` (real matrices, full-field witnesses) and the real structure digest. v1 unit fixtures unchanged. |
| B11 | `folding/` serial MLE path uses `data[i]` | `folding/` demoted; fix only if it is used as the P2 oracle |
| B12 | `folding/` silent `zip` truncation and ark-poly invariant violation | As B11 |
| B13 | 5,620 build artifacts tracked in `folding/target` | `.gitignore` fixed. `git rm -r --cached folding/target` **left to the user**, as decided. |
| B14 | `folding/` variable order differs from kilonova | As B11; adapter in P2 |
| **B15** | **HFS over E::Base for R1CS over E::Scalar** (`field_switch` is not a homomorphism) | **Fixed for native folding (P3, HFS v2) and for recursion (P5, `kilonova::ivc`, D1 = (a)).** v2 (`Nova/src/kilonova/hfs/`, spec §8) folds over `E::Scalar` with no projection; the recursive layer (spec §9) verifies it in-circuit over `E1::Scalar` and delegates the E1 group operations to a CycleFold circuit. Multi-step chains verify: `ivc::tests::test_ivc_v2_nonuniform_{smoke,}_{direct,span}` run the 4 traces that are ignored in v1, and the K = 2/4, T = 1/16/64 chains pass (`docs/P5-report.md`). The **v1 path is unchanged and still B15-broken by construction** (historical): `test_known_issue_b15_scalar_r1cs_not_foldable_over_base` still asserts that v1 rejects the class, and the 4 v1 multi-step tests stay `#[ignore = "known issue B15 (v1 path only …)"]` with a pointer to their v2 ports. |
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

## 5b. Tests added in P3 (HFS v2, `docs/P3-report.md`)

| Test | Purpose |
|---|---|
| `kilonova::hfs::tests::test_chain_100_{r1cs,power5}_{direct,span}` | B8/B10: 100 alternating cross-predicate folds, oracle on every step |
| `kilonova::hfs::tests::test_b15_instance_class_folds_in_v2` | B15 fixed for native folding |
| `kilonova::hfs::tests::test_mu_nu_combinations`, `proptest_random_ccs_fold` | μ/ν combinations; random templates |
| `kilonova::hfs::tests::test_rejects_mismatched_shapes` | explicit rejection of counts, lengths and degrees |
| `kilonova::hfs::tests::test_negative_matrix`, `proptest_single_tamper_rejected`, `test_noncanonical_field_element_rejected` | tamper cases with their detection layer |
| `kilonova::hfs::tests::test_vectors_v2_*`, `test_commitment_absorption_matches_ro2`, `test_challenges_agree_bytewise` | frozen v2 vectors |

## 5c. Tests added in P5 (recursion on HFS v2 + CycleFold, `docs/P5-report.md`)

| Test | Purpose |
|---|---|
| `kilonova::ivc::tests::test_cyclefold_circuit`, `test_cyclefold_rejects_wide_rho` | CycleFold circuit: honest RLCs (incl. identity inputs), wrong output / ρ / k / ρ ≥ 2^128 rejected |
| `kilonova::ivc::tests::test_cyclefold_fold_native_matches_gadget` | n-input relaxed-R1CS fold: gadget = native, accumulator stays satisfied |
| `kilonova::ivc::tests::test_transcript_native_matches_gadget_v2_{direct,span}` | HFS v2 gadget: same challenges and folded scalars as `hfs::NIFS::verify` (R1CS and power5), tampering rejected, gate |
| `kilonova::ivc::tests::test_ivc_chain_k2_{direct,span}`, `test_ivc_chain_k4_t16_direct`, `test_ivc_chain_t64_direct` (ignored, run explicitly), `test_ivc_chain_span_long` (ignored) | valid chains, verified at spot steps with the kn-ccs oracle |
| `kilonova::ivc::tests::test_ivc_v2_nonuniform_{smoke_,}{direct,span}` | the 4 v1 B15-ignored traces on v2 |
| `kilonova::ivc::tests::test_ivc_rejects_*` | wrong initial state, skipped step, wrong/repeated counter, swapped steps, wrong predicate, broken state link, unbound hint, bad CycleFold witness, tampered accumulators, each with its layer |
| `kilonova::ivc::tests::test_constraint_breakdown`, `test_primary_circuit_is_succinct` | per-component counts (disjoint, sum = CountingCS total), succinctness |
| `kilonova::ivc::tests::test_ivc_native_pow5_application`, `test_ivc_r1cs_template_rejects_pow5_rows` | native degree-5 application in the loop |

## 6. Reproduce

```bash
# whole suite (≈3 min on 2 vCPU; needs ≤ 4 GiB)
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1
# fixed-point sizes
cargo test -p nova-snark --release --lib kilonova::tests::test_setup_fixed_point_converges -- --nocapture
# show the B15 failure of the historical v1 path
cargo test -p nova-snark --release --lib kilonova::tests::test_ivc_nontrivial_nonuniform_smoke -- --ignored --test-threads=1
# the same trace on the v2 recursion (P5)
cargo test -p nova-snark --release --lib kilonova::ivc::tests::test_ivc_v2_nonuniform -- --test-threads=1
```
