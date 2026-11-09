# P5 report: real non-uniform recursive chain on HFS v2 with CycleFold (2026-11-09)

PLAN.md §3 P5. Plan: `docs/P5-plan.md`. Spec: `docs/protocol-spec.md` §9. Claim map: `docs/claim-check-map.md` §6. Branch `p5-recursion` (from P3 commit `4e8665b`). D1 = (a), Nova fork + CycleFold (decided 2026-11-09).

**Status: P5 done for the scope below, with stated limitations.** No independent review yet (PLAN.md §2). Nothing here is a performance or security claim; all timings are from the 16 GB development laptop (Apple M4, fanless) and are for orientation only.

## 1. Goal and scope

Goal: bind the execution trace, the index representation and the accumulator inside the recursive circuit, on the native-field HFS v2, so that multi-step non-uniform recursion works (B15).

Implemented (`Nova/src/kilonova/ivc/`, v1 recursion untouched):

| Item | Code | Notes |
|---|---|---|
| CycleFold circuit over `E2::Scalar = E1::Base` | `cyclefold.rs` | one shared 128-bit ρ; `W_out = W_run + ρ·W_inc`; Direct: `M_out[j] = M_run[j] + ρ·ι_k[j]` with **ι_k selected in-circuit** from a one-hot k (saves 2t public inputs); on-curve checks; `(0,0)` ⇔ identity so no infinity flag is public. 20 inputs (Direct, t = 3), 7 (Span), 28 (t = 5). |
| n-input Nova fold gadget | `gadgets.rs::AllocatedRelaxedR1CSInstanceN::fold_with_r1cs` | generalises `nova/circuit/r1cs.rs::fold_with_r1cs` to any number of bignat inputs; absorbs the running instance (the fresh CycleFold instance does not hash it); r's bignat built from its bits (no extra range check). Native twin `cyclefold::cf_fold_{prove,verify}`. |
| HFS v2 verifier gadget | `gadgets.rs::verify_hfs` | transcript v2 in-circuit (`E1::RO2Circuit`), identical to `hfs::NIFS::verify`; every equality gated by `1 − is_base`; E1 points as range-checked 4 × 64-bit limbs with derived infinity flag; folded points are hints bound through the CycleFold instance's public inputs. Succinct. |
| Primary augmented circuit per predicate | `circuit.rs` | link hash in/out, HFS gadget, CycleFold fold, base case, in-circuit Poseidon trace chain with the circuit's constant id, `z_{i+1} = F_k(z_i)`; one public output. |
| Native `RecursiveSNARK` v2 | `mod.rs` | `PublicParams::setup` (CycleFold shape, fixed point on (s, s′), CountingCS pre-check, padded family, keys from padded shapes, pp digest), `new`, `prove_step`, `verify` (link hash, `hfs::decide`, CycleFold relaxed R1CS, last incoming CCS), `IvcError::layer()`. **Direct and Span.** |
| Native degree-5 application in the loop | `shape.rs` | template `R1csPow5` (t = 5): constraints annotated `KN_NATIVE_POW5` become one native `(D z)^5 = E z` row. |
| Constraint breakdown | `breakdown.rs` | per-namespace attribution, disjoint, sums to the CountingCS total |
| Fixture | `fixtures.rs::ChainPredicates` | arity 2, K ≤ 4, different wiring, negative coefficients; optional native x⁵ member |
| kn-run scenario | `kn-scenario ivc` | sizes, iterations, breakdown, per-step prove times, spot verifies, final verify, checkpoint bytes |

### Minimal P4 scope done here (and what is not)

Done: N15 replaced for v2 by an in-circuit Poseidon chain `trace_{i+1} = H(TAG_TRACE, trace_i, k)` where k is a **constant of predicate k's circuit**; the family digest (`hfs_digest`: template, all K padded shapes, key labels/sizes, hence ι) and `pp_digest` (adds the CycleFold shape digest and key size, arity, K, variant, template, IVC version) enter every link hash, and `hfs_digest` enters every HFS transcript; the folded instance's predicate `k_prev` is range-checked (one-hot) and is the single value that selects ι (CycleFold), e_k (Span) and the transcript absorption.

Not done (P4 remainder): G3 (the verifier takes the schedule `ids` and recomputes the trace; it does not recover it from the proof), G4/φ (no in-circuit predicate selection; the claim is "this specific trace"), the `PredicateFamily` type with stable ids and matrix encoding, the folded-matrix vs weighted-evaluation cross-check, support-growth measurements, and the P4 K ∈ {1, 2, 4, 16} acceptance.

## 2. Configuration

Pallas (E1) / Vesta (E2), Pedersen, Poseidon (U24, `Strength::Standard`), challenges 128 bits, hashes 250 bits, non-ZK, uncompressed. Rust 1.92.0, `--release`, `--test-threads=1`. Fixture `ChainPredicates`, z₀ seeded, schedule: every member once, then seeded.

## 3. Results

### 3.1 Sizes (CountingCS; identical across seeds)

Primary circuit, predicate 0 (`test_constraint_breakdown`, `kn-scenario ivc` → `details.constraint_breakdown`):

| Component | Direct K=2 | Direct K=4 | Span K=2 | Span K=4 |
|---|---|---|---|---|
| application (F_k) | 4 | 4 | 4 | 4 |
| HFS sum-check rounds (34 rounds: checks, interpolation, round squeezes) | 37,026 | 37,026 | 37,026 | 37,026 |
| HFS transcript (statement absorption, γ, 17 × α, δ, ρ) | 24,652 | 24,652 | 23,098 | 23,098 |
| HFS claims (powers, eq, end checks, scalar fold) | 150 | 150 | 150 | 150 |
| span / index (ι selection for absorption; Span: λ fold) | 27 | 27 | 4 | 8 |
| hashing (link hash in + out, trace chain) | 14,113 | 14,113 | 7,897 | 9,451 |
| non-native / hints (limb allocation, range checks, flags, one-hot) | 2,582 | 2,584 | 1,034 | 1,036 |
| CycleFold fold (n-input fold, on-curve checks) | 42,134 | 42,134 | 16,695 | 16,695 |
| control (base case, selections, counters) | 338 | 338 | 184 | 188 |
| **total primary** | **121,026** | **121,028** | **86,092** | **87,656** |
| CycleFold circuit (raw → padded) | 5,102 → 8,192 | 5,104 → 8,192 | 1,375 → 2,048 | 1,375 → 2,048 |
| CycleFold public inputs | 20 | 20 | 7 | 7 |

The components are disjoint and sum to the total (asserted). The HFS gadget does not depend on K beyond the one-hot terms; K = 4 costs 2 constraints more than K = 2 for Direct. The P3.0 memo estimated ≈ 121.8k primary + ≈ 4.9k CycleFold for Direct; measured 121,026 + 5,102. With the native power-5 template (t = 5, d = 5): 145,168 primary rows, CycleFold 7,584 (28 inputs).

Optimisation targets visible here (not done; they change transcript v2 or the layout): the 17 separate α squeezes (≈ 18.3k), and the bignat fold of the 20 CycleFold inputs (≈ 38k).

### 3.2 Setup

Every configuration converges in **3 iterations** (`(s, s′)`: (1, 1) → (16, 16) → (17, 17) for R1CS; padded m = 121,026, num_w = 121,020, s = s′ = 17), well inside `MAX_SETUP_ITERATIONS = 12`; no cap changed. Setup 25–30 s (Direct), 18–21 s (Span), 30 s (pow5).

### 3.3 Chains (`results/raw/p5-ivc.jsonl`, 22 records, all `status = success`, `verification_ok = true`)

Command: `target/release/kn-run scenario ivc K={2,4} steps={1,16,64} variant=direct verify_every=8 --seed {101,202,303} --experiment p5-ivc`, plus Span (K=2/4 T=16, K=2 T=64, seed 101) and `template=pow5` (K=2 T=16, seed 101).

| Config | prove_step median | final verify | peak RSS | checkpoint |
|---|---|---|---|---|
| Direct K=2, T=1/16/64 (3 seeds) | 1.69–1.72 s (base step 0.51 s) | 4.8 s (T=1) / 6.8–7.0 s (T=16) / 11.3–11.5 s (T=64) | 0.91–0.93 GiB | 8.3 MB |
| Direct K=4, T=1/16/64 (3 seeds) | 2.05–2.07 s | 8.9–10.0 / 10.9–11.0 / 15.4–15.5 s | 1.41–1.64 GiB | 8.3 MB |
| Span K=2 T=16 / T=64; K=4 T=16 | 1.45 s / 1.45 s; 1.76 s | 5.7 / 10.3 s; 9.1 s | 0.71 / 0.71; 1.19 GiB | 5.6–5.7 MB |
| Direct pow5 K=2 T=16 | 4.18 s (s = 18) | 7.9 s | 1.08 GiB | 9.8 MB |

Every spot verification (every 8th step, every 16th for Span T=64) passed. The final-verify time grows with T although the work is constant in T; this laptop is fanless and the T=64 runs are the longest, so this is most likely thermal, not algorithmic; it is not investigated. Records after the Direct seed-101 block carry `implementation_dirty = true` because `versions.lock`/`configs/common.toml` were being edited (no code change; committed in `f7caa83`).

### 3.4 Tests (`cargo test -p nova-snark --release --lib kilonova::ivc -- --test-threads=1`)

| Acceptance item | Test | Detection layer |
|---|---|---|
| K = 2, T = 1 and 16 (Direct, Span) | `test_ivc_chain_k2_direct`, `test_ivc_chain_k2_span` | — (kn-ccs oracle on every verified step) |
| K = 4, T = 16 | `test_ivc_chain_k4_t16_direct` | — |
| K = 2/4, T = 64 | `test_ivc_chain_t64_direct` (`#[ignore]`, run explicitly), `test_ivc_chain_span_long` (`#[ignore]`: K=4 T=16, K=2/4 T=64 Span) + kn-run records | — |
| Wrong initial state | `test_ivc_rejects_wrong_claims` | LinkHash |
| Skipped step | same (proof claimed for the schedule without step 3, n − 1) | LinkHash |
| Wrong counter | same (n + 1) ; repeated counter by the prover: `test_ivc_rejects_repeated_counter` | LinkHash ; LastIncoming (in-circuit hash check fails, propagates) |
| Swapped steps | `test_ivc_rejects_wrong_claims` | LinkHash |
| Wrong predicate choice | same (inner step: LinkHash; last step: Input, the last instance belongs to another predicate); prover folds an instance as the wrong predicate: `test_ivc_rejects_wrong_incoming_predicate` | LinkHash / Input ; LastIncoming |
| Broken state link | `test_ivc_rejects_broken_state_link` (tampered at the last and at an inner step) | LastIncoming (inner tampering propagates through the next in-circuit HFS verifiers) |
| Hint not bound / CycleFold | `test_ivc_rejects_unbound_hint`, `test_ivc_rejects_bad_cyclefold_witness` | CycleFold or LinkHash ; CycleFold |
| Tampered final accumulators | `test_ivc_rejects_tampered_accumulators` | Decider (W, λ), CycleFold (cfW), LinkHash (U) |
| Native = gadget transcript | `test_transcript_native_matches_gadget_v2_{direct,span}` (R1CS and power5; challenges γ, α, r_x, δ, r_y, ρ and folded u, io, v, λ equal; tampered round message, τ, Y round, predicate id → unsatisfied; gate off in the base case) | — |
| CycleFold circuit | `test_cyclefold_circuit` (K ∈ {2, 3, 4}, t ∈ {0, 3, 5}, identity inputs; wrong W_out, ρ, k, M_out rejected), `test_cyclefold_rejects_wide_rho` | — |
| n-input fold | `test_cyclefold_fold_native_matches_gadget` | — |
| Breakdown, succinctness | `test_constraint_breakdown`, `test_primary_circuit_is_succinct` | — |
| Native d = 5 in the loop | `test_ivc_native_pow5_application` (one D and one E entry for member 0, none for member 1; chain [0,1,0,0,1,0] verified with the oracle), `test_ivc_r1cs_template_rejects_pow5_rows` | Setup |
| v1 B15 tests ported | `test_ivc_v2_nonuniform_smoke_{direct,span}`, `test_ivc_v2_nonuniform_{direct,span}` (traces [0,2], [0,1,2] Direct and [0,1], [0,1,0] Span, ExamplePredicates K = 3, every step verified) | — |

"The final check authenticates the whole chain": `verify` checks only the final link hash and the three final relations; the tamper tests inject the fault at an inner step and are caught there, never by a host-side per-step check.

Suite results: §5.

## 4. Known limitations

- Uncompressed: `verify` reads the final witnesses (G2). P7.
- G3/G4 open (§1). The schedule is the prover's; the verifier checks "this specific trace".
- Non-canonical limb encodings (spec §9.7): limbs are range-checked, not checked < p; at most 4 encodings per coordinate, same point; affects only which RO-derived challenge is used.
- `scalar_mul` incomplete-addition corner cases as in Nova.
- The application in the d = 5 test is tiny (one native row); the HFS for a family padded to the recursive circuit dominates every cost. Realistic high-degree workloads are P8/P9.
- No knowledge-soundness proof for the composed scheme; tests are not a proof.
- v1 recursion (`kilonova::RecursiveSNARK`) is kept and still B15-broken; `test_known_issue_b15_scalar_r1cs_not_foldable_over_base` deliberately still asserts v1's failure.
- B18 (inherited Nova compression tests) untouched (handled on `b18-nova-tests`).

## 5. Definition-of-done commands

```bash
cargo fmt --all --check
cargo clippy -p nova-snark -p kn-ccs -p kn-run --release --all-targets -- -W clippy::all -A clippy::len_without_is_empty
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1
cargo test -p kn-ccs --release
cargo test -p kn-run --release -- --test-threads=1
cargo test -p nova-snark --release --lib -- kilonova::ivc::tests::test_ivc_chain_t64_direct kilonova::ivc::tests::test_ivc_chain_span_long --ignored --test-threads=1
```

Results (2026-11-09, this laptop): fmt clean; clippy clean (only the inherited allowed lint); kilonova suite **76 passed, 7 ignored, 0 failed** in 867 s (P3 baseline 53 passed / 5 ignored; the 7 ignored are the 4 v1 B15 tests, the v1 perf harness and the 2 long P5 chain tests); kn-ccs **21 passed**; kn-run **10 passed**; the 2 long ignored tests run explicitly: **2 passed** in 763 s (Direct K=2/4 T=64; Span K=4 T=16, K=2/4 T=64).

## 6. Entry conditions for later periods

- **P4 remainder:** trace recovery (G3), in-circuit φ (G4), `PredicateFamily`, K ∈ {1, 2, 4, 16} span checks. The recursive layer already carries `k` as a circuit constant and binds `hfs_digest`.
- **P6:** binary PCD needs μ = 2 running inputs in the gadget (the native HFS supports μ, ν; the gadget is μ = ν = 1) and two CycleFold accumulators or a merged one.
- **P7:** compression of the running ACCS (reference decider) and of the CycleFold relaxed R1CS (needs B18 fixed).
- **P8/P9:** same-library baselines on this layer; formal runs on the Linux host.
