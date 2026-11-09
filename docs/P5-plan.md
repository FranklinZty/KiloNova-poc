# P5 plan: real non-uniform recursive chain on HFS v2 with CycleFold (2026-11-09)

PLAN.md §3 P5. Decision: D1 = (a), Nova fork + CycleFold (`docs/P3.0-decision.md`, decided 2026-11-09). Acceptance report: `docs/P5-report.md`.

## Context and entry state

- P3 delivered the native-field HFS v2 (`Nova/src/kilonova/hfs/`): any CCS template, μ running + ν incoming, Direct and Span, succinct verifier, decider, transcript v2 (Poseidon over `E::Scalar` = `E::RO2`; E1 points absorbed as 4 × 64-bit limbs per coordinate plus the infinity flag). No recursion.
- The v1 recursion (`kilonova/mod.rs` `PublicParams`/`RecursiveSNARK`, `circuit/`, `span/`) folds over the wrong field (B15). It stays compiling and its tests stay as historical evidence; P5 does **not** modify it.
- P4 is not done. P5 does only the P4 items that its own acceptance needs (§5 below) and lists the rest as P4 remaining.

## 1. Architecture (option (a))

Curves: E1 = Pallas (relation and HFS over `E1::Scalar`, commitments on Pallas with coordinates in `E1::Base`), E2 = Vesta (`E2::Scalar = E1::Base`, `E2::Base = E1::Scalar`).

| Object | Field | Committed on | Folded by |
|---|---|---|---|
| Primary augmented circuit of predicate k (one per k, all padded to common dimensions) | `E1::Scalar` | E1 (Pedersen) | HFS v2 (Direct or Span), verified **natively** inside the next primary circuit |
| CycleFold circuit (one fixed shape) | `E2::Scalar = E1::Base` | E2 (Pedersen) | Nova relaxed-R1CS NIFS, verified inside the primary circuit (E2 points are native there; the instance's public inputs are `E2::Scalar` values, non-native, carried as 4 × 64-bit bignats) |

There is no secondary augmented circuit and no secondary fixed point. The only fixed point is between the primary circuits' own dimensions and the number of sum-check rounds of their HFS verifier.

New module `Nova/src/kilonova/ivc/` (v1 untouched):

| File | Content |
|---|---|
| `ivc/mod.rs` | `PublicParams` (setup with fixed point and report, digests, keys), `RecursiveSNARK` (`new`, `prove_step`, `verify`), `IvcError` with a detection layer, the `IvcVariant` trait (Direct, Span) |
| `ivc/cyclefold.rs` | CycleFold circuit, its native witness generation, native n-input relaxed-R1CS NIFS (`prove`/`verify`) |
| `ivc/gadgets.rs` | E1 points as non-native limbs (`NnPoint`), the in-circuit **n-input** Nova fold of a CycleFold instance (generalises `nova/circuit/r1cs.rs::fold_with_r1cs`), the in-circuit **HFS v2 verifier** gadget (sum-check, claims, transcript v2) |
| `ivc/circuit.rs` | Primary augmented circuit per predicate |
| `ivc/shape.rs` | Shape builder: R1CS from the frontend, plus native high-degree rows for the combined template (§6) |
| `ivc/tests.rs` | Unit, chain, rejection, breakdown tests |

### 1.1 CycleFold circuit

Over `E2::Scalar`. Public inputs, in this order (one shared 128-bit ρ):

- Direct (t matrices): `ρ, k, W_run.(x,y), W_inc.(x,y), W_out.(x,y), then for j < t: M_run[j].(x,y), M_out[j].(x,y)` → 8 + 4t inputs (20 for R1CS, t = 3).
- Span: `ρ, W_run.(x,y), W_inc.(x,y), W_out.(x,y)` → 7 inputs.

Constraints: ρ decomposed into 128 bits (so ρ < 2^128); each input point gets an allocated infinity bit `b` with `b·x = 0`, `b·y = 0` and the on-curve check unless `b` (so `(0,0)` ⇔ infinity, which is unique because `(0,0)` is not on Pallas); `W_out = W_run + ρ·W_inc` and `M_out[j] = M_run[j] + ρ·ι_k[j]` with Nova's ECC gadgets. **ι_k is selected inside the circuit** from the K constants by a one-hot decomposition of k (`Σ b_i = 1`, `Σ i·b_i = k`), so ι is not a public input (saves 2t inputs, i.e. 6 × 1,911 constraints in the primary circuit, at O(K·t) cost here). The circuit is fixed for the family, because ι depends only on (K, t) and the index key label.

Why the infinity flag is not an input: it is determined by (x, y) as above, and the primary circuit derives it the same way from the limbs (`flag = [Σ limbs = 0]`).

### 1.2 n-input fold gadget

`AllocatedRelaxedR1CSInstanceN<E2>`: `W, E` (native points), `u` (native num), `X[n]` (bignats). `fold_with_r1cs(params, u_new{W, X[n] bignats}, T)`: challenge `r` from `E2::ROCircuit` over `(tag, params, U (W, E, u, X limbs), u_new (W, X limbs), T)`; `W ← W + r·W_new`, `E ← E + r·T`, `u ← u + r`, `X_i ← (X_i + r·X_new_i) mod |E2::Scalar|`. Unlike Nova's 2-input version the running U is absorbed, because the fresh CycleFold instance does not hash U. Native twin: `cyclefold::nifs_prove/nifs_verify` with the same absorption order; a test pins native = gadget.

### 1.3 Primary augmented circuit (predicate k hard-coded)

Witness (non-deterministic advice): `pp_digest, hfs_digest, i, z_0, z_i, trace_i`, running `U_i` (comm_W and comm_M as limbs, or λ; u, io, r_x, r_y, v), incoming `u_i = (k_prev, comm_W limbs, io)`, the HFS proof, hints `comm_W_out, comm_M_out[t]` (Direct), running CycleFold `cfU_i`, new CycleFold `comm_W` and cross term `T`. No other circuit's witness and no matrix (succinct).

1. `is_base = (i == 0)`.
2. Link hash `h_in = H(TAG_LINK, pp_digest, hfs_digest, i, z_0, z_i, trace_i, U_i, cfU_i)` (Poseidon over E1::Scalar, `NUM_HASH_BITS`). Enforce `u_i.io[0] = h_in` unless `is_base`.
3. HFS v2 verifier gadget on `(U_i, u_i, proof)`, identical transcript to `hfs::NIFS::verify`; every equality (round sums, end checks) is multiplied by `(1 − is_base)`. Outputs ρ (bits), `r_x′, r_y′`, and the folded scalars `u′ = u + ρ`, `io′ = io + ρ·io_inc`, `v′ = ε + ρθ`, Span `λ′ = λ + ρ·e_{k_prev}`; the folded points are the hints.
4. CycleFold instance inputs built in-circuit from ρ, `k_prev` and the limbs of `U_i.comm_W, u_i.comm_W`, hints and `U_i.comm_M`; fold it into `cfU_i` (gadget §1.2).
5. Outputs `U_{i+1} = is_base ? U_default : U′`, `cfU_{i+1} = is_base ? cfU_default : cfU′`.
6. Schedule (minimal P4): `trace_in = is_base ? 0 : trace_i`, `trace_{i+1} = H(TAG_TRACE, trace_in, k)` with **k a circuit constant**.
7. `z_{i+1} = F_k(is_base ? z_0 : z_i)`, `i+1`.
8. Single public output `h_out = H(TAG_LINK, pp_digest, hfs_digest, i+1, z_0, z_{i+1}, trace_{i+1}, U_{i+1}, cfU_{i+1})`.

Range checks: limbs of the incoming comm_W and of all hint points are range-checked (64 bits each), because they enter `mult_mod`; the running points are bound by the link hash to range-checked outputs of the previous step. `k_prev ∈ [0, K)` is enforced by a one-hot decomposition (also used by Span and the ι absorption).

### 1.4 Native `RecursiveSNARK` and verifier

State after n steps: `(U_n, W_n)` running ACCS, `(u_n, w_n)` last incoming CCCS of predicate `k_{n−1}`, `(cfU_n, cfW_n)` CycleFold accumulator, `z_n`, `trace_n`. `new(k_0)` runs the base step; `prove_step(k)` runs `hfs::NIFS::prove(U_n, u_n)`, the CycleFold witness, the CycleFold NIFS, and synthesizes the primary circuit k.

`verify(pp, n, z_0, ids)`: (1) `n ≥ 1`, `ids.len() = n`, `ids[n−1] = u_n.k`; (2) recompute `trace_n` from `ids` and check `u_n.io[0] = H(…, n, z_0, z_n, trace_n, U_n, cfU_n)`; (3) `hfs::decide(U_n, W_n)` (comm_W and comm_M openings and all claims; the tests also run the kn-ccs oracle); (4) `cfU_n` relaxed-R1CS satisfied by `cfW_n` (with commitment openings); (5) `u_n` satisfies predicate `ids[n−1]`'s CCS and `comm_W` opens. Nothing else is checked on the host: every earlier step is authenticated only through the recursion.

## 2. Setup

1. Index commitments ι (only K, t and the key label), CycleFold shape (fixed), padded with `R1CSShape::pad`, CycleFold key sized from the padded shape.
2. Fixed point on `(s, s′)`: synthesize all K primary circuits (first with `CountingCS`, rejecting more than `MAX_SETUP_CONSTRAINTS`), pad to common `(m, num_w)`, recompute `s = ⌈log m⌉, s′ = ⌈log(num_w + 2)⌉`; stop when unchanged, fail after `MAX_SETUP_ITERATIONS` (caps unchanged). Re-synthesize at the final dimensions and require identical shapes (exactness check, as v1).
3. `HfsParams::new(template, shapes)` sizes the primary key from the padded shapes. `pp_digest` covers the HFS digest (template, all K shapes, key labels/sizes), the CycleFold shape digest and key size, arity, K, variant and the IVC version tag.
4. `SetupReport`: iteration history, raw/padded sizes, CycleFold sizes.

## 3. Minimal P4 scope inside P5

Done in P5 (needed for P5 acceptance):

- N15 replaced: in-circuit Poseidon trace chain `trace_{i+1} = H(TAG_TRACE, trace_i, k)`, k hard-coded per predicate circuit; the native verifier recomputes it from the claimed schedule and the link hash binds it.
- Family digest bound: `hfs_digest` and `pp_digest` enter every link hash; `hfs_digest` also enters every HFS transcript.
- `k_prev` (the predicate of the folded incoming instance) is range-checked and is the value that selects ι (CycleFold), e_k (Span) and the transcript absorption.

Not done (P4 remaining): G3 trace recovery (the verifier still takes the schedule `ids` as input; it does not recover it from the proof), in-circuit φ (the schedule is the prover's choice, authenticated after the fact: the claim is "this specific trace"), the `PredicateFamily` type with stable ids and matrix encoding, the folded-matrix vs weighted-evaluation cross-check, support growth measurements, and the P4 K ∈ {1, 2, 4, 16} acceptance.

## 4. Acceptance mapping

| PLAN.md P5 item | Evidence (test / run) |
|---|---|
| K = 2, 4 and T = 1, 16, 64 valid chains | `ivc::tests::test_ivc_chain_k2_t{1,16}_{direct,span}` (default suite, spot-verify every 4th step); `test_ivc_chain_k4_t16_direct`, `test_ivc_chain_k{2,4}_t64_direct` `#[ignore]`d (long) and run explicitly; `kn-run` scenario `ivc` records (K ∈ {2,4}, T ∈ {1,16,64}, seeds 101/202/303 as feasible) in `results/raw/p5-ivc.jsonl` |
| Wrong initial state, skipped step, repeated/wrong counter, swapped steps, wrong predicate choice, broken state link | `ivc::tests::test_ivc_rejects_*`, each asserting `IvcError::layer()` (verifier-side claims and prover-side tampering via test-only hooks) |
| Per-component constraint counts without double counting | `ivc::tests::test_constraint_breakdown` (CountingCS deltas per component that sum to the total) + kn-run `ivc` records |
| Final check authenticates the whole chain | `verify` only checks final accumulators; tamper tests in the middle of a chain must be caught by it |
| v1 B15 tests ported | `test_ivc_v2_nonuniform_{smoke,trace}_{direct,span}` = the 4 v1 traces on v2; v1 tests stay ignored with a pointer; `test_known_issue_b15_*` annotated; B15 updated in `docs/baseline-status.md` |
| Setup converges within the caps | `test_ivc_setup_converges` (iterations recorded in report + kn-run) |
| Succinct gadget (regression for F1) | fixed point test + `test_primary_circuit_is_succinct` (primary size independent of K-many shape sizes beyond the one-hot terms) |
| Native = gadget transcript | `test_transcript_native_matches_gadget_v2_{direct,span}`; `test_cyclefold_fold_native_matches_gadget` |
| CycleFold circuit | `test_cyclefold_circuit_{satisfied,rejects_wrong_output,rejects_wrong_rho,selects_iota}` |
| Native d = 5 application | §6 |

## 5. Priorities (if time runs out, stop in this order and report honestly)

1. D1 record + this plan. 2. CycleFold circuit + n-input fold gadget with tests. 3. Primary circuit + native `RecursiveSNARK` Direct, K = 2 multi-step chains. 4. Rejection tests, constraint breakdown, kn-run records. 5. K = 4, T = 64. 6. Span. 7. Native d = 5 application.

## 6. Native high-degree application (d = 5)

The frontend emits R1CS only. Plan: a combined template with t = 5, `[A,B]·1, [C]·(−1), [D,D,D,D,D]·1, [E]·(−1)`. The shape builder (`ivc/shape.rs`) records constraints whose annotation is the marker `KN_NATIVE_POW5` as rows of D (the `a` linear combination) and E (the `c` combination) instead of A/B/C, so `y = x^5` is one native degree-5 row with no intermediate multiplication witnesses. The recursive verifier stays R1CS rows (D = E = 0 there). The HFS v2 gadget and the CycleFold circuit are generic in t and the template, so the same code runs with deg_x = 6 and t = 5. A test checks that the application rows are not lowered (row count and D/E nnz) and runs a chain through the loop with the kn-ccs oracle.

## 7. Risks

- Constraint count of the primary circuit (memo estimate ≈ 122k, padded to 2^17): if a component is far larger, record it, do not cut checks.
- Non-canonical limb encodings (limbs of an integer ≥ p) are not excluded; they give the prover a few transcript variants per point, not a different instance. Documented as a known limitation.
- Long chains on the 16 GB laptop: `--release --test-threads=1`, `#[ignore]` for T = 64, records via kn-run.
