# P1 plan: minimal experiment harness (2026-10-07)

Approved detailed plan for PLAN.md §3 P1. The acceptance report is `docs/P1-report.md`.


## Context

P0 is done (2026-10-05). PLAN.md §3 P1 says every later report must use the same measurement conventions from day one: a process-isolated runner (`kn-run`) that records wall time, child peak RSS, git revision, `versions.lock` hash and a status (success/failure/timeout/OOM) as append-only JSONL in `results/raw/`, plus a `CountingCS`-based constraint report for the augmented circuits. P1 is off the critical path (P3 → P5 → P7), so it stays small: no workload generator, adapters or config validator (those move to P8). Multi-step IVC still fails on B15. The harness must record that as a failure rather than hide it.

What exists today:
- `CountingCS` (`Nova/src/kilonova/mod.rs:151`) is `pub(crate)` and is only used inside `setup` for the secondary dry run. Per-iteration sizes are printed with `eprintln!` under `#[cfg(test)]` only (`mod.rs:425`), and the `history: Vec<SetupIterationSizes>` is discarded.
- `GlobalStructure::build` (`relation.rs:83`) pads the shapes, so raw sizes exist only during `setup`.
- `ExamplePredicates` (K=3) is duplicated as a private test fixture in `kilonova/mod.rs:950` and `span/mod.rs:797`. Each copy implements its own module's `PredicateSet` trait.
- `test_utils` is `#[doc(hidden)] pub` and not cfg(test). The bench already uses it.
- `transcript::HFS_TRANSCRIPT_VERSION = 1` is public.
- `libc`, `serde_json`, `sha2`, `rand_chacha` and `bincode` are already in `Cargo.lock`, so adding a crate pulls in no new third-party packages.

## Design

### 1. Nova library additions (small and additive; no protocol or transcript change)

- **`SetupReport`** (new, in `kilonova/mod.rs`, re-exported for span): `iterations: Vec<SetupIterationSizes>`, per-predicate raw `(num_cons, num_vars, num_io, nnz)` from the final iteration's shapes, padded dims taken from `structure_*.predicates[i].shape`, secondary raw and padded, `num_vars_max`, `s_max`, `s_prime_max`.
- `PublicParams::setup_with_report(...) -> Result<(Self, SetupReport), NovaError>` in both `kilonova/mod.rs` and `span/mod.rs`. The existing `setup` delegates to it and drops the report, so callers are unchanged. **`PublicParams` gets no new field**, so the pp digest and serialization stay unchanged.
- `pub fn predicate_constraint_counts<F, PS>(ps, id) -> CountingSummary`: synthesizes **only** the predicate (`arity` allocated inputs) into `CountingCS`. This gives m_app/w_app separately from m_aug.
- `CountingCS` stays `pub(crate)`. A public `CountingSummary { num_constraints, num_aux, num_inputs, nnz }` (serde) is exposed instead.
- Move `ExamplePredicates` into `test_utils` as a public fixture that implements both `kilonova::PredicateSet` and `span::PredicateSet`. Delete the two private copies and point the existing tests at the shared one. Behaviour stays identical.
- New unit test `test_setup_report_consistent`: iterations == 2 for K=3, raw ≤ padded, padded is a power of two and equals the structure, the report's last iteration equals the converged sizes, and the predicate-only counts are below the augmented counts.

### 2. New workspace crate `tools/kn-run` (package `kn-run`, two binaries)

Add `"tools/kn-run"` to the root `Cargo.toml` members. Deps: `nova-snark` (path), `serde`, `serde_json`, `sha2`, `libc`, `ff`, `rand_chacha`, `bincode`, `rayon`. Build with `-p kn-run`, so the NIFS-circuit git deps are not needed.

**`kn-scenario` (child process).** Runs one named scenario and prints exactly one `KN-RESULT {json}` line on stdout. The JSON holds semantic fields, phase timings measured with `Instant` around the named call only, `threads_actual = rayon::current_num_threads()`, `build_profile`, `input_digest` (sha256 of canonical scenario inputs) and `result_digest` (sha256 of semantic outputs: pp digest, shape sizes, z_i; never proof randomness).

| Scenario | Purpose | Fields filled |
|---|---|---|
| `noop` | empty-run baseline (spawn + RSS floor) | — |
| `sleep ms=N` | wall-time boundary | `sleep_ms` measured |
| `alloc bytes=N` | RSS boundary: allocate, touch every page, `black_box`, hold | `alloc_bytes` |
| `fail` | panics deliberately → exercises the failure path | — |
| `constraints variant=direct\|span` | `setup_with_report` + per-predicate `predicate_constraint_counts` | K, t, d, μ, ν, m_app/n_app/w_app per predicate, m_aug/n_aug raw and padded per curve, nnz, setup_iterations, setup_ms |
| `bootstrap variant=… seed=S` | setup → `RecursiveSNARK::new` (z0 and the first predicate derived from the seed via ChaCha) → verify | + recursive_ms, verify_warm_ms, checkpoint_bytes (bincode of `RecursiveSNARK`, private: it holds witnesses), verification_ok, outputs |
| `chain variant=… steps=T seed=S` | multi-step; **expected to fail on B15 today** | status=failure with the B15 message, kept as a record |

**`kn-run` (runner).** Has no dependency on nova code paths at runtime. Hand-rolled arg parsing (no clap).
- `kn-run scenario <name> [k=v…] [--seed N] [--threads N] [--timeout-s N] [--mem-cap-mb N] [--experiment ID] [--repetition N] [--warmup] [--out PATH]`
- `kn-run test <libtest path> [--include-ignored] [...]`: locates the `nova-snark` lib test binary via `cargo test -p nova-snark --release --lib --no-run --message-format=json`, then runs `<bin> <name> --exact --test-threads=1`. It parses the libtest summary and records **failure if 0 or more than 1 test ran**.
- `kn-run selfcheck`: the acceptance checks below. Writes to `results/raw/p1-selfcheck.jsonl` and exits non-zero on any failed criterion.
- Process control: `Command` with stdout/stderr redirected to `results/raw/logs/<run_id>.{out,err}`. The runner polls `libc::wait4(pid, WNOHANG, &rusage)` (1 ms poll for the first 100 ms, then 10 ms) in a single thread, which avoids pid-reuse races. On the deadline it sends `kill(SIGKILL)` → `timeout`. `ru_maxrss` is normalised to bytes (bytes on macOS, KiB on Linux). Child env: `RAYON_NUM_THREADS=threads` (default 1, per §5.1).
- Status: `success` (exit 0 and a `KN-RESULT` line present) · `timeout` (killed by the runner) · `oom` (SIGKILL not from the runner, a stderr `memory allocation of … failed`, or `RLIMIT_AS` hit) · `failure` (everything else, including other signals, a missing result line or a parse error, with `exit_code`/`signal`/`error_message` = the stderr tail). The memory cap is enforced with `setrlimit(RLIMIT_AS)` in `pre_exec` on Linux only. On macOS the record says `mem_cap_enforced=false`.
- Captured once per run: `git rev-parse HEAD` + dirty flag, sha256 of `versions.lock` and `Cargo.lock`, `rustc -V`, hostname/OS/arch/CPU model/cores/RAM (sysctl on macOS, /proc on Linux), and `machine_id` = short hash of those. `protocol_version`/`transcript_version` come from the child (`HFS_TRANSCRIPT_VERSION`).
- `run_id` = UTC timestamp + 8 random hex digits. `config_hash` = sha256 of canonical JSON of (scenario, args, seed, threads, timeout, mem cap). Records are appended with `O_APPEND` as one line each and are never rewritten.

### 3. `results/schema.json`

A JSON Schema (draft 2020-12) with every PLAN §8 field, plus `record_version`, `wall_ms`, `threads_requested`, `threads_actual`, `result_digest`, `implementation_dirty`, `cargo_lock_hash`, `exit_code`, `signal`, `mem_cap_bytes`, `mem_cap_enforced`, `log_stdout`, `log_stderr`, `null_reasons` (field → why it is null, e.g. `compression_ms: "P7: no compression yet"`) and `details` (a nested per-curve/per-predicate breakdown). Every key is always present. Fields that do not apply are `null`, never 0, and get an entry in `null_reasons`. A runner test checks that emitted records have exactly the schema's property set and that every null has a reason.

### 4. Acceptance → how it is checked (`kn-run selfcheck` + crate tests)

| PLAN acceptance item | Check |
|---|---|
| Same seed and config → same semantic inputs and results | `constraints direct` ×2 and `bootstrap direct seed=101` ×2: equal `config_hash`, `input_digest`, `result_digest`. Seed 202 gives a different `input_digest`. |
| Actual threads/sizes recorded | `threads_actual` from the child; m/n/nnz from synthesis, never from the request |
| Every record has a status; failures never dropped | `fail` → failure; `sleep ms=5000 --timeout-s 1` → timeout; `chain steps=2` → failure (B15); `kn-run test` with a non-matching name → failure. A record is written in every case. |
| Timing boundaries validated | `noop` baseline; `sleep ms=200`: wall ∈ [200, 350] ms and child `sleep_ms` within ±5 ms; `alloc bytes=128MiB,512MiB`: Δpeak_rss vs noop ∈ [0.95N, 1.10N + 8 MiB] |

Fast integration tests in `tools/kn-run/tests/runner.rs` use `CARGO_BIN_EXE_kn-run`/`kn-scenario` and `CARGO_TARGET_TMPDIR`, covering noop, sleep, alloc, fail, timeout and schema conformance. They do not touch nova proving, so they also run in debug.

### 5. Docs and housekeeping

- `docs/P1-plan.md`: this detailed plan, written into the repo first (mirroring `docs/P0-plan.md`).
- `docs/P1-report.md`: the acceptance report (goal, scope, config, results with the selfcheck records, limitations, next-phase entry conditions).
- README "Experiment harness" section: commands, record conventions and timing boundaries (`wall_ms` includes process spawn; `setup_ms` etc. cover only the named call; `witness_ms` is null because it lies inside `recursive_ms` today).
- `versions.lock`: fill `p0_commit = 72f9596…`, update `root_sha256` (Cargo.lock gains the `kn-run` entry), add `tools/kn-run` to the members, and add the `rev =` pins to the git deps in `NIFS-circuit/Cargo.toml` and `folding/Cargo.toml` matching the locked revisions (the P1 TODO).
- PLAN.md §10 status: P1 → done, citing the report. AGENTS.md repo-structure line for `tools/` and `results/`.

## Critical files

- `Nova/src/kilonova/mod.rs`, `Nova/src/kilonova/span/mod.rs` (setup_with_report, counts), `Nova/src/kilonova/test_utils.rs` (shared ExamplePredicates)
- new `tools/kn-run/{Cargo.toml, src/bin/kn-run.rs, src/bin/kn-scenario.rs, src/{record,proc,env}.rs, tests/runner.rs}`
- new `results/schema.json`, `docs/P1-plan.md`, `docs/P1-report.md`; edits to `Cargo.toml`, `versions.lock`, `README.md`, `PLAN.md`, `AGENTS.md`, `NIFS-circuit/Cargo.toml`, `folding/Cargo.toml`

## Verification

```bash
cargo fmt --check
cargo clippy -p kn-run -p nova-snark --release --lib --bins   # kilonova + kn-run clean
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1   # expect 26 pass, 5 ignored
cargo test -p kn-run --release -- --test-threads=1
cargo build -p kn-run --release
target/release/kn-run selfcheck          # all criteria PASS, records in results/raw/p1-selfcheck.jsonl
target/release/kn-run scenario constraints variant=span
target/release/kn-run test kilonova::tests::test_setup_fixed_point_converges
```

Out of scope: no commit unless asked. B15 is untouched. Nothing here is a performance claim; it is laptop data, labelled as dev-machine data.
