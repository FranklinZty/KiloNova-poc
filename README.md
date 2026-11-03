# KiloNova

This is a proof-of-concept implementation of KiloNova for academic use.
Please do NOT use this in the production environment.

# Introduction

KILONOVA is a preprocessing recursive SNARK for fixed sets of non-uniform predicates. By introducing holographic folding schemes and index-span folding, it enables efficient multi-predicate PCD with constant-size recursive states. This repository contains the proof-of-concept implementation of KILONOVA and its core cryptographic components for scalable recursive proofs. **The PoC does not provide zero knowledge** (see `docs/protocol-spec.md` §4).

<div align="center">
  <img src="./kilonova.png" width="600">
</div>

# Development Progress

Status as of 2026-10-05. Details are in `PLAN.md` and `docs/baseline-status.md`.

## Holographic Folding Schemes

1. Multi-folding for CCS instances: algebraic PoC in `folding/` (reference only). ✅
2. Non-uniform (indexed) folding for R1CS, Direct and Span variants: implemented in `Nova/src/kilonova/`, with transcript v1 binding all inputs and helper claims. ✅ for small positive-coefficient instances. ⚠️ General R1CS is blocked by known issue B15 (folding runs over the wrong field).
3. Index commitment folding. ✅

## Preprocessing Recursive SNARK

1. Succinct in-circuit HFS verifier; setup converges (2 iterations for K=3). ✅
2. Index-span folding (Span variant). ✅
3. Multi-step non-uniform IVC. ⛔ Blocked by B15; the 1-step bootstrap verifies.
4. Compressed SNARK / independent final verifier. ⏳ (P7)
5. Native high-degree CCS: builder and reference checker in `ccs/` (P2) ✅; folding and proving over CCS ⏳ (P3)

## Build & test

```bash
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1
```

## Experiment harness (P1)

`tools/kn-run` runs one named scenario or one test in a fresh process and appends one JSON record per run to `results/raw/<experiment>.jsonl`. The record layout is `results/schema.json` (PLAN.md §8), and the plan and acceptance report are `docs/P1-plan.md` and `docs/P1-report.md`.

```bash
cargo build -p kn-run --release
target/release/kn-run selfcheck                       # P1 acceptance checks (~30 min; --quick skips proving)
target/release/kn-run scenario constraints variant=direct --experiment demo
target/release/kn-run scenario bootstrap variant=span --seed 202
target/release/kn-run test kilonova::tests::test_setup_fixed_point_converges
```

Scenarios: `noop`, `sleep ms=N`, `alloc bytes=N`, `fail` (harness calibration), plus `constraints`, `bootstrap` and `chain steps=T` with `variant=direct|span` on the K=3 example family. `chain` with T ≥ 2 currently fails on B15, and that failure is recorded.

Conventions:

- Every run gets a record with a status: `success`, `failure`, `timeout` (killed by `--timeout-s`, default 1800) or `oom`. A field that does not apply is `null` with an entry in `null_reasons`; it is never 0.
- `wall_ms` and `peak_rss_bytes` are measured by the runner (spawn to reap, `wait4` `ru_maxrss`), so `wall_ms` includes process start-up. On macOS the first exec of a freshly built binary takes about 0.6–1 s, so discard or warm up the first run. `setup_ms`, `recursive_ms` (`RecursiveSNARK::new` plus all `prove_step` calls) and `verify_warm_ms` are in-process timers around exactly that call. `witness_ms` is null because witness generation is inside `recursive_ms`.
- `threads` is the child's actual rayon thread count. `--threads` sets `RAYON_NUM_THREADS` (default 1, the PLAN.md §5.1 main setting).
- `input_digest` and `result_digest` hash the semantic inputs and outputs (seeded z0 and trace; pp digest, shape sizes, outputs). Two runs of the same configuration must agree on both, and on `config_hash`.
- `--mem-cap-mb` is enforced with `RLIMIT_AS` on Linux only; records say `mem_cap_enforced`.
- Raw child stdout/stderr are kept in `results/raw/logs/<run_id>.{out,err}`. Records are append-only.
- Laptop numbers are development data only. Formal runs happen on the dedicated host (PLAN.md §5.2).

## CCS reference oracle (P2)

`ccs/` (crate `kn-ccs`) builds native CCS relations, including high-degree ones written with repeated multisets, and checks ACCS/CCCS instance–witness pairs. It is a slow, independent oracle for P3: generic over `ff::PrimeField`, with no dependency on `kilonova/`, and with the same conventions (`z = (w ‖ u ‖ io)`, little-endian MLE bits, Nova-style padding). Plan and report: `docs/P2-plan.md`, `docs/P2-report.md`.

```bash
cargo test -p kn-ccs --release
target/release/kn-run scenario ccs steps=1024 --seed 101     # fifth-power chain: native CCS vs R1CS
```
