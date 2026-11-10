# P4 report: fixed predicate family, in-circuit selection φ, index-span (2026-11-10)

PLAN.md §3 P4. Plan: `docs/P4-plan.md`. Spec: `docs/protocol-spec.md` §9.8 (recursion, IVC version 2) and §10 (family, index-span). Claim map: `docs/claim-check-map.md` §6–§7. Branch `p4-family` (from `p5-recursion` tip `1b47d39`); commits in §6.

**Status: P4 done for the scope below, with stated limitations (§5).** No independent review yet (PLAN.md §2). Nothing here is a performance or security claim; all timings are from the 16 GB development laptop (Apple M4, fanless, 10 cores) and are for orientation only.

## 1. Goal and scope

Goal: make non-uniformity an authenticated protocol state instead of a branch in the host program. P5 had already done the trace-chain part (N15 closed for v2, digests in every link hash). P4 closes the rest:

| Item | Code | Notes |
|---|---|---|
| `PredicateFamily` | `Nova/src/kilonova/family/mod.rs` | stable member ids, shared interface (arity, num_io), one template, identical padded dimensions, selector (φ) descriptor; canonical member encoding byte-identical to `kn_ccs::encode`; family digest (SHA3-256 → 250-bit element) over version, label, arity, num_io, selector, ids, per-member SHA3 digests, key labels and sizes; `check_digest`, `check_member`, `position` |
| Family digest bound | `HfsParams::from_family`, `ivc::PublicParams::setup`/`setup_pinned` | the family digest **is** the digest absorbed by every HFS v2 transcript (native and in-circuit) and the link hash's digest slot; `pp_digest` covers it. `HfsParams::new` and the frozen v2 vectors are unchanged. |
| φ (G4) | `ivc/program.rs` (`PredicateProgram`, `Scheduled<P>`), `ivc/circuit.rs` | every primary circuit evaluates φ on its input state and enforces `φ(i, z_i) = k` |
| Trace recovery (G3) | `ivc/mod.rs` | `verify(pp, n, z_0) → ChainOutput { z_n, trace, last_id }` takes no schedule; `verify_schedule` compares the recovered trace (layer `Trace`) |
| IVC version 2 | `ivc/mod.rs` | new link/trace tags; the prover API follows φ (`new(pp, prog, z_0)`, `prove_step(pp, prog)`) |
| Index-span paths | `family/mod.rs` | explicit folded matrices (`FoldedMatrices`, step by step or from λ), weighted evaluation (`weighted_eval`), `support_stats` |
| K ≤ 16 fixture | `ivc/fixtures.rs` | `ChainPredicates` members 4–15 (generated wiring), reordered / substituted variants, `program()`; `example_program()` for the v1 K = 3 fixture |
| kn-run | `kn-scenario family` (new), `kn-scenario ivc` (ported) | `results/raw/p4-family.jsonl` |

### Design decisions (from the plan)

- **φ placement**: φ is a function of the public state `(i, z_i)`, evaluated in the circuit of the selected predicate; the pc lives in the application state (SuperNova-style). The deterministic-schedule example `Scheduled<P>` stores the schedule as base-2^b digits in a program register; φ reads the low digit (unique 253-bit decomposition) and each F_k shifts the register with one constraint. The P5 tests keep their meaning: their old explicit schedules are encoded in z_0 and are now *forced* by the circuits.
- **Claim** (spec §9.8): an accepted `verify(pp, n, z_0)` shows that a φ-valid execution of n steps from z_0 exists with the returned trace hash; for deterministic programs (all fixtures) this is **"this specific trace"**.
- **G4** is "No in-circuit φ; id is a host constant" (`docs/claim-check-map.md` §3, N13; `docs/P0-plan.md`). It is closed by φ. (PLAN.md §10's release gate also called G4 is unrelated.)

## 2. Configuration

Pallas (E1) / Vesta (E2), Pedersen, Poseidon (`Strength::Standard`), challenges 128 bits, hashes 250 bits, non-ZK, uncompressed. Rust 1.92.0, `--release`, `--test-threads=1`.

## 3. Results

### 3.1 Acceptance (PLAN.md P4) → evidence

Unit/integration tests (`cargo test -p nova-snark --release --lib kilonova -- --test-threads=1`), each rejection asserting its detection layer (`hfs::Layer` or `IvcLayer`):

| PLAN.md P4 acceptance | Test / record | Detection layer |
|---|---|---|
| K = 1, 2, 4, 16: step-by-step matrix evaluation = span-weighted evaluation | `family::tests::test_span_paths_agree_k{1,2,4,16}` (Direct and Span; T = 8/16/16/32; after every fold: explicit step-by-step = explicit from λ = `weighted_eval` = the protocol's `v_j` = kn-ccs `eval_matrix_mle` on the explicit matrix; tracked λ = witness λ; `decide` and kn-ccs `check_accs` accept; final support = union of supports) | — |
| … also the kn-ccs oracle (`check_accs`) | same tests; and every verified step of every recursive chain test (P5 behaviour kept) | — |
| Forged ids | `ivc::tests::test_p4_rejects_forged_ids` (forged trace hash; last instance relabelled as another member; id ≥ K); `family::tests::test_family_rejects_unknown_or_duplicate_ids` | LinkHash; LastIncoming; Input — Input |
| Reordered family | `family::tests::test_family_digest_binds_order_and_matrices` (Input); `family::tests::test_hfs_rejects_other_family` (HFS fold under the reordered family → Verifier/Decider); `ivc::tests::test_p4_rejects_reordered_and_substituted_family` (`setup_pinned` → Setup; a proof made under the reordered pp → LinkHash under the original pp) | Input / Verifier–Decider / Setup / LinkHash |
| Substituted matrix | same three tests (one coefficient changed under the same id) | Input / Verifier–Decider / LinkHash |
| Non-one-hot new input | `family::tests::test_non_one_hot_incoming_rejected` (id ≥ K → Input; witness λ folded with e_0 + e_1 → Decider: IndexCommitment / SpanIndex); `ivc::tests::test_p4_one_hot_gadget_rejects_forged_bits` (two hot bits, none, mismatching bit, k ≥ K → unsatisfied); `ivc::tests::test_p4_cyclefold_rejects_non_unit_iota` (M_out = M_run + ρ(ι_0 + ι_1) → CycleFold circuit unsatisfied) | Input / Decider / Gadget / CycleFold circuit |
| Tampered span | `family::tests::test_tampered_span_rejected` (public λ → SpanIndex; public and witness λ → Claim; folding the tampered pair → Verifier; Direct witness λ → IndexCommitment); `ivc::tests::test_p4_rejects_tampered_span` (Span chain: public λ → LinkHash; witness λ → Decider; both → LinkHash) | Decider / Verifier / LinkHash |
| Host schedule disagreeing with φ | prover side: `ivc::tests::test_p4_rejects_schedule_disagreeing_with_phi` (host runs a predicate φ did not select at the base step, an inner step, the last step); verifier side: `test_ivc_rejects_wrong_claims` (`verify_schedule` with swapped steps, wrong predicate, wrong last predicate, wrong length → Trace; z_0 with another program register → LinkHash) | LastIncoming (all three prover cases); Trace / LinkHash |
| ≥ 2 predicates really change the wiring | `ivc::tests::test_p4_members_change_wiring` (the 16 application circuits have pairwise different sparsity patterns); kn-ccs `wiring_pair` members 0/1 in every span test | — |
| Template embedding | `family::tests::test_zero_term_embedding_folds` (§3.5) | Decider + oracle |
| φ native = in-circuit | `ivc::tests::test_phi_scheduled_program` (K ∈ {1, 2, 3, 4, 16}: native φ = in-circuit φ, step F_k = native, register ≥ 2^L unsatisfiable, out-of-range digit selects nothing) | — |
| Canonical encoding | `family::tests::test_encoding_matches_kn_ccs` (byte-identical to `kn_ccs::encode`, decodes back, independent of entry order and split duplicates) | — |
| P5 recursion with family/φ: K = 2, 4; T = 1, 16 | `test_ivc_chain_k2_direct` (T = 1, 16), `test_ivc_chain_k2_span` (T = 1, 16), `test_ivc_chain_k4_t16_direct`; every check is `verify(pp, n, z_0)` without a schedule plus `verify_schedule`; recovered trace and z_n compared with the native run; kn-ccs oracle | — |
| … T = 64 (long, run explicitly) | `test_ivc_chain_t64_direct` (K = 2, 4), `test_ivc_chain_span_long` (K = 4 T = 16, K = 2/4 T = 64) | — |
| … rejection suite | all P5 `test_ivc_rejects_*` ported (state link, counter, wrong incoming predicate, unbound hint, CycleFold witness, tampered accumulators incl. comm_M) | as P5 |
| … one K = 16 chain | `test_ivc_chain_k16` (`#[ignore]`, run explicitly, T = 16, every member once) and the kn-run record (§3.3) | — |
| v1 B15 traces | `test_ivc_v2_nonuniform_{smoke_,}{direct,span}` on `example_program()` (K = 3) | — |
| Setup iterations; constraint delta of φ and family digest | `test_constraint_breakdown` (new category `selection`) and kn-run records (§3.2) | — |
| kn-scenario + `results/raw/p4-family.jsonl` | `kn-scenario family` (synthetic and recursive family), `kn-scenario ivc` (chains): 30 records, all `status = success`, `verification_ok = true`, `implementation_dirty = false` (commit `41d3724`) | — |

### 3.2 Constraint delta (CountingCS breakdown, predicate 0)

| Component | P5 Direct K=2 | P4 Direct K=2 | P4 Direct K=16 | P5 Span K=2 | P4 Span K=2 | P5 Span K=4 | P4 Span K=4 |
|---|---|---|---|---|---|---|---|
| application (P4 adds the register shift) | 4 | 5 | 5 | 4 | 5 | 4 | 5 |
| **selection (φ)** | — | **255** | **254** | — | **255** | — | **254** |
| hashing (link in/out, trace) | 14,113 | 14,113 | 14,113 | 7,897 | 9,451 | 9,451 | 9,451 |
| control | 338 | 340 | 340 | 184 | 186 | 188 | 190 |
| non-native / hints | 2,582 | 2,582 | 2,596 | 1,034 | 1,034 | 1,036 | 1,036 |
| HFS and CycleFold components | — | unchanged | unchanged | — | unchanged | — | unchanged |
| **total primary** | **121,026** | **121,284 (+258)** | **121,297** | **86,092** | **87,904 (+1,812)** | **87,656** | **87,913 (+257)** |

- φ for `Scheduled` costs `L + 2` constraints (L = 253 bits for K = 2, 252 for K = 4 and 16) plus 1 for the register shift; the extra state element costs 2 control constraints (base-case selection).
- The **family digest costs 0 constraints**: it occupies the slot of the P5 structure digest (one advice element absorbed by the transcript and the link hashes).
- Span K = 2 also pays +1,554 hashing: the two extra absorbed elements (z_0 and z_i each grow by the program register) push its link hash over a Poseidon rate boundary (one more permutation per link hash). Direct and Span K = 4 do not cross one. This is a property of the example φ (register in the state), not of φ in general.
- CycleFold unchanged (Direct 5,102 raw → 8,192 padded at K = 2; 5,116 raw at K = 16).

Setup converges in **3 iterations** in every configuration (`(s, s′)`: (1, 1) → (16, 16) → (17, 17)), including K = 16 (m = 121,298, num_w = 121,292); caps unchanged.

### 3.3 Chains (`results/raw/p4-family.jsonl`, `kn-scenario ivc`, seed 101)

| Config | setup | prove_step median | final verify | peak RSS | checkpoint |
|---|---|---|---|---|---|
| Direct K=2 T=1 | 26.5 s | (base step only) | 4.9 s | 1.0 GiB | 8.3 MB |
| Direct K=2 T=16 | 26.1 s | 1.70 s | 5.3 s | 1.0 GiB | 8.3 MB |
| Direct K=4 T=16 | 36.5 s | 2.29 s | 9.9 s | 1.7 GiB | 8.3 MB |
| Span K=2 T=16 | 19.0 s | 1.49 s | 4.6 s | 0.8 GiB | 5.8 MB |
| **Direct K=16 T=16** | **54.6 s** | **2.95 s** (1.5 s at step 2 → 4.7 s at step 16) | **38.4 s** | **2.6 GiB** | 8.3 MB |

The verifier takes no schedule in any run; the recovered trace equals `H_trace*(schedule)` and z_n equals the native run. The K = 16 chain shows the K-dependent cost directly: the prover's tables and the decider's weighted evaluation range over every member with λ_k ≠ 0, so per-step proving grows with the number of distinct members folded so far, and the final decider (O(Σ_k nnz)) takes 38 s against 5 s at K = 2.

### 3.4 Support growth and the K-dependent density cost

Synthetic W1 families (`kn-scenario family source=synthetic`, R1CS, m = n = 1024, 3 non-zeros per row in A and B, 2 + 1 (u column) in C; one member ≈ 9,210 non-zeros = 442 KB at 48 B per entry; T = max(2K, 16) Span folds, every member first; seed 101, plus seeds 202/303 for K = 16 partial). Union of supports over one member (= size of the explicit folded matrix once λ is dense):

| K | shared | partial (½ of the rows shared) | low overlap |
|---|---|---|---|
| 1 | 1.00 | 1.00 | 1.00 |
| 2 | 1.00 | 1.42 | 1.89 |
| 4 | 1.00 | 2.30 | 3.65 |
| 8 | 1.00 | 4.03 | 7.15 |
| 16 | 1.00 | 7.40 (7.54, 7.50 for seeds 202, 303) | 14.03 |
| 32 | 1.00 | 14.25 | 27.38 |

In every run the explicit support reached the union exactly at step K (when the last new member was folded), and explicit = weighted = protocol claims held at every step. Bytes at K = 32: base matrices 14.1 MB (all patterns); explicit folded matrix 0.44 MB (shared), 6.3 MB (partial), 12.1 MB (low); λ 1 KB. Family digest ≈ 0.7 ms per member (streamed SHA3 over the canonical encoding).

The real recursive family (`source=ivc`: the K primary augmented circuits, Direct, R1CS; one member 2.76 M non-zeros = 132.5 MB):

| K | union / max | union / Σ | Σ base bytes | explicit bytes | family digest | weighted eval | explicit eval | setup | peak RSS |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 1.000 | 1.000 | 133 MB | 133 MB | 0.37 s | 0.23 s | 0.24 s | 38 s | 0.8 GiB |
| 2 | 1.085 | 0.543 | 265 MB | 144 MB | 0.77 s | 0.25 s | 0.18 s | 32 s | 1.2 GiB |
| 4 | 1.085 | 0.271 | 530 MB | 144 MB | 0.99 s | 0.43 s | 0.16 s | 33 s | 2.3 GiB |
| 8 | 1.085 | 0.136 | 1.06 GB | 144 MB | 2.14 s | 0.85 s | 0.16 s | 37 s | 2.7 GiB |
| 16 | 1.170 | 0.073 | 2.12 GB | 155 MB | 4.55 s | 1.54 s | 0.17 s | 53 s | 4.1 GiB |

Reading: the members of the recursive family share the verifier circuit, so the union stays within 1.17× of one member while the weighted path's work and the base storage grow linearly in K. The residual 8.5–17 % is consistent with column shifts: members allocate different numbers of application witnesses (`num_aux` differs by 1–2), so every variable allocated after F_k (the output link hash) gets a member-dependent column. Allocating the application last (or padding its witness to the family maximum) should remove it; not done. For low-overlap synthetic families the union grows ≈ K× (27× at K = 32). This is the K-dependent density cost written into spec §10.3–10.4: **any folded-index representation pays the union of supports (between max_k nnz and Σ_k nnz) once λ is dense, which happens after K distinct members; the weighted path pays Σ_k nnz work per evaluation, the explicit path pays the union in storage plus an O(nnz(M_k) + union) merge per fold.**

### 3.5 Template embedding (zero terms)

The only embedding used is P5's `R1csPow5` family (R1CS rows inside a t = 5, d = 5 template with zero D/E terms). `family::tests::test_zero_term_embedding_folds`: `kn_ccs::pad::embed_zero_terms` of an R1CS `wiring_pair` member has the R1csPow5 template and the same non-zeros; its residual equals the R1CS residual row by row on satisfied and tampered z, for u = 1 and u = 3; a mixed family {embedded R1CS member, native degree-5 member} folds for 12 steps with u ≠ 1 and every output passes `decide` and kn-ccs `check_accs`. `lift_degree` is not used (P2: exact only for u = 1). Real expansion cost: no extra non-zeros; the HFS proof for this family grows from 38 to 55 field elements (deg_x 3 → 6, t 3 → 5); Direct carries 2 more index commitments; in the recursion the primary circuit grows from 121,026 to 145,168 rows and CycleFold from 20 to 28 inputs (P5 measurement, `docs/P5-report.md` §3.1).

### 3.6 Suite results

Run on `p4-family` at `064c5f6` plus these docs (2026-11-10, development laptop):

| Command | Result |
|---|---|
| kilonova suite (`--release --lib kilonova -- --test-threads=1`) | **95 passed, 0 failed, 8 ignored** (1,294 s). P5 baseline was 76 / 7. The ignored ones are the 4 v1 B15 tests (historical), the v1 perf harness, and the 3 long chains below. |
| long chains, run explicitly (`--ignored`): `test_ivc_chain_t64_direct`, `test_ivc_chain_span_long`, `test_ivc_chain_k16` | **3 passed** (1,383 s) |
| `cargo test -p kn-ccs --release` | 21 passed |
| `cargo test -p kn-run --release -- --test-threads=1` | 10 passed |

## 4. What changed for callers

- `ivc::PublicParams::setup(program, tpl)` takes a `PredicateProgram` (a `PredicateSet` plus φ, label, stable ids, selector descriptor); `setup_pinned` additionally pins the family digest; `pp.family()` exposes ids, member digests and the digest.
- `RecursiveSNARK::new(pp, program, z_0)`, `prove_step(pp, program)`, `next_predicate(program)`; `verify(pp, n, z_0) → ChainOutput`; `verify_schedule(pp, n, z_0, ids)`.
- `kn-scenario ivc` accepts K ≤ 16 and encodes its seeded schedule in z_0; new `kn-scenario family`.

## 5. Known limitations and open items

- **Uncompressed** (G2, P7): `verify` reads the final witnesses; the decider is the weighted O(Σ_k nnz) path (38 s at K = 16 on this laptop).
- **φ reads only public state**; non-deterministic selection is not supported (spec §9.7). The only φ implemented is the explicit-schedule program `Scheduled<P>` (capacity ⌊253/b⌋ steps per register). A data-dependent φ (reading a pc written by F_k) fits the same trait but has no example or test.
- After a host deviation from φ, or with a malformed register, the honest program "halts" (`select` returns None) and the prover reports it at layer Input.
- The column-shift effect that makes the recursive family's union 1.085–1.17× instead of ≈ 1× (§3.4) is not optimised.
- The explicit folded-matrix path is a measurement and cross-check tool; neither prover nor decider uses it. Using it for the recursive family's decider (≈ 9× less evaluation work than the weighted path at K = 16) is a P7 decision.
- Span K = 2 pays one extra Poseidon permutation per link hash because the example φ enlarges the state (§3.2).
- No knowledge-soundness proof for the composed scheme; tests are not a proof. No independent review yet.
- v1 (`kilonova::{PublicParams, RecursiveSNARK}`, `nifs.rs`, `span/`) untouched (historical, B15); it still takes a trace and uses the algebraic digest. B18 untouched.
- Timings come from a fanless laptop and are orientation only.

## 6. Definition-of-done commands

```bash
cargo fmt --all --check
cargo clippy -p kn-ccs -p kn-run -p nova-snark --release --all-targets -- -W clippy::all -A clippy::len_without_is_empty
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1
cargo test -p nova-snark --release --lib -- kilonova::ivc::tests::test_ivc_chain_t64_direct kilonova::ivc::tests::test_ivc_chain_span_long kilonova::ivc::tests::test_ivc_chain_k16 --ignored --test-threads=1
cargo test -p kn-ccs --release
cargo test -p kn-run --release -- --test-threads=1
```

All clean or passing: `cargo fmt --all --check` clean; clippy clean (only the pre-existing workspace `resolver` warning); test totals as in §3.6.

## 7. Entry conditions for later periods

- **P6**: trees need μ = 2 running inputs in the gadget and a φ/trace rule for internal nodes (the trace chain becomes a tree hash).
- **P7**: decide which index path the decider uses (explicit union vs weighted over K members, §3.4); compress the running ACCS and the CycleFold accumulator.
- **P8/P9**: the E2 K scan can reuse `kn-scenario family` and `kn-scenario ivc` (K ≤ 16; larger K needs a larger fixture).
