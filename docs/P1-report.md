# P1 acceptance report: minimal experiment harness

Date: 2026-10-07. Plan: `docs/P1-plan.md`. Base commit: `72f9596` (P0) plus the uncommitted P1 changes. The records therefore say `implementation_dirty: true`. Fill `versions.lock` `p1_commit` after committing.

## 1. Goal

PLAN.md §3 P1: every later report uses the same measurement conventions from day one. That means one process per run, measured wall time and child peak RSS, provenance (git revision, lock hashes, toolchain, machine), a status for every run, and append-only JSONL records. It also needs a `CountingCS`-based constraint report for the augmented circuits. The full bench-runner (workload generator, adapters, config validator) stays in P8.

## 2. Scope implemented

| Item | Where |
|---|---|
| `SetupReport` (fixed-point history; raw and padded shapes on both curves) via `PublicParams::setup_with_report`, Direct and Span. `setup` delegates to it. `PublicParams`, its digest and serialization are unchanged. | `Nova/src/kilonova/mod.rs`, `span/mod.rs` |
| `CountingSummary` + `predicate_constraint_counts` (application predicate alone, m_app/w_app) for both variants. `CountingCS` stays crate-private. | same |
| `ExamplePredicates` (K=3) moved from a private test fixture to `test_utils`, implementing both `PredicateSet` traits. The span tests keep their own 2-predicate fixtures. | `Nova/src/kilonova/test_utils.rs` |
| `kn-run` runner: `scenario`, `test`, `selfcheck`. Uses `wait4` rusage, timeout via SIGKILL, `RLIMIT_AS` memory cap (Linux), status classification, raw logs, append-only JSONL. | `tools/kn-run/src/{lib,proc,env,record}.rs`, `src/bin/kn-run.rs` |
| `kn-scenario` child: `noop`, `sleep`, `alloc`, `fail`, `constraints`, `bootstrap`, `chain` (direct or span) | `tools/kn-run/src/bin/kn-scenario.rs` |
| Record schema: 71 fields, every one always present, plus `null_reasons` | `results/schema.json` (matched to `record::FIELDS` by a test) |
| Housekeeping: `rev =` pins for the git dependencies (same commits as before), `folding` excluded from the root workspace (it could not resolve on its own), and `versions.lock` updated (p0_commit, lock hashes, members) | `Cargo.toml`, `NIFS-circuit/Cargo.toml`, `folding/Cargo.toml`, `versions.lock` |

No protocol, transcript or circuit logic changed. B15 is untouched.

## 3. Test configuration

| Item | Value |
|---|---|
| Machine | Apple M4 MacBook Air, 10 logical CPUs, 16 GiB, Darwin 25.6.0 (`machine_id 25b9a5997ef0f955`). Development machine only, never a formal timing host. |
| Toolchain | rustc 1.92.0 (the pinned `rust-toolchain.toml`; the P0 cloud run was not on the pin) |
| Build | `--release`; child `RAYON_NUM_THREADS=1` |

## 4. Results

```bash
cargo fmt --all --check                                                    # clean
cargo clippy -p kn-run -p nova-snark --release --all-targets -- -W clippy::all -A clippy::len_without_is_empty
                                                                           # clean (the allowed lint is the inherited spartan/polys/multilinear.rs finding)
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1      # 28 passed, 5 ignored (4 × B15, 1 perf harness), 228 s
cargo test -p kn-run --release -- --test-threads=1                         # 10 passed (1 unit, 9 integration)
target/release/kn-run selfcheck                                            # 16 checks, 0 failed; 16 records in results/raw/p1-selfcheck.jsonl
```

Acceptance against PLAN.md §3 P1:

| Criterion | Evidence (`results/raw/p1-selfcheck.jsonl`) | Result |
|---|---|---|
| Same seed and configuration give the same semantic inputs and results | `constraints direct` ×2: equal config_hash, input_digest `659c2a99…` and result_digest `77bba777…`. `bootstrap direct seed=101` ×2: input `6a045494…`, result `47e57960…`. Seed 202 gives a different input digest (`858e0f5f…`). | ✅ |
| Actual thread counts, matrix and witness sizes recorded | `threads` = 1 comes from the child's `rayon::current_num_threads()`. m_app=3, n_app=5, w_app=3, m_aug=72,760, n_aug=72,882, padded 2^17 on both curves, N_total=5,855,909 (direct). Span: m_aug=69,012. All are measured by synthesis, never taken from the request. | ✅ |
| Every record has a status; failures never dropped | `fail` → failure (panic text kept), `sleep 5 s` with a 1 s timeout → timeout (wall 1,014 ms, SIGKILL), unknown scenario → failure, `chain steps=2` → failure "prove_step 2 failed: … (B15)" with its partial `setup_ms` kept, `kn-run test` on a missing name → failure. All 16 records pass `record::validate` (every field present, every null has a reason). | ✅ |
| Timing boundaries validated with an empty run and a known-size buffer | `noop`: 2.7 ms wall, 1.9 MiB RSS. `sleep 200`: in-process 205.0 ms, runner wall 210.1 ms. `alloc` 128 MiB → ΔRSS 128.0 MiB; 512 MiB → 512.1 MiB. | ✅ |

Development-machine reference values (single run each, 1 thread; **not** performance results):

| Run | setup_ms | recursive_ms | verify_warm_ms | peak RSS | checkpoint bytes |
|---|---|---|---|---|---|
| constraints direct | 87,481 / 86,157 | — | — | 1.77 / 2.25 GiB | — |
| constraints span | 76,996 | — | — | 2.37 GiB | — |
| bootstrap direct (1 step), seeds 101, 101, 202 | ≈84–86 k | 7,765–10,009 | 8,307–9,035 | 2.5–2.8 GiB | 20,975,272 |

The setup sizes agree with P0 (`docs/baseline-status.md` §2): 2 iterations, with primary 27,230 → 72,760 and secondary 66,283 → 72,951.

## 5. Known limitations

- **OOM classification is untested on macOS.** `RLIMIT_AS` is not enforced there, so selfcheck skips that check and says so. On Linux, selfcheck runs `alloc 1 GiB` under a 256 MiB cap and expects `oom`. That has not been run yet; it must be run on the P3 Linux VM or the P9 host.
- `oom` is also inferred from a SIGKILL the runner did not send, or from an allocation-failure message on stderr. On macOS, jetsam kills look the same.
- Peak RSS varies by about 25% between identical runs (1.77 vs 2.25 GiB for `constraints direct`). Single runs are not comparable, so P9's repetition rules apply.
- The first exec of a freshly built binary on macOS took 0.6–1 s. Selfcheck records a warm-up `noop` (`warmup: true`) before the baseline. `wall_ms` always includes process start-up; the in-process phase timers do not.
- `wall_ms` resolution is the poll interval: 1 ms for the first 100 ms, then 10 ms.
- `witness_ms`, `compression_ms`, `verify_cold_ms`, `public_state_bytes`, `proof_bytes`, `statement_bytes` and `vk_bytes` are null with reasons until P5/P7. `checkpoint_bytes` is the bincode size of the private `RecursiveSNARK`, witnesses included.
- The protocol scenarios cover only the K=3 example family. Parametric workloads (W1–W4) belong to P8.
- `folding/Cargo.lock` was rewritten by cargo 1.92 to lockfile v4 with the same commits. The folding crate itself was not rebuilt.

## 6. Open issues and entry conditions for the next periods

- B15 remains the critical-path blocker (P3.0). The harness already records `chain` T ≥ 2 as a B15 failure; that record must flip to success when B15 is fixed.
- P2/P3 reports must produce their numbers through `kn-run` (new scenarios in `kn-scenario.rs`, new fields only by bumping `RECORD_VERSION` and `results/schema.json`).
- Run `kn-run selfcheck` on Linux once to close the OOM check.
- No independent review of this evidence has taken place yet (PLAN.md §2); schedule a review pass.
