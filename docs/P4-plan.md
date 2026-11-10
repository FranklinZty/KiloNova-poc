# P4 plan: fixed predicate family, in-circuit selection φ, index-span (2026-11-10)

PLAN.md §3 P4. Base: branch `p5-recursion` (tip `1b47d39`); work branch `p4-family`. Acceptance report: `docs/P4-report.md`. P5 already did the trace-chain part of P4 (`docs/P5-report.md` §1: in-circuit Poseidon trace chain over each circuit's constant id, N15 closed for v2; `hfs_digest`/`pp_digest` in every link hash). This plan covers the remainder.

## 0. What G3, G4 and N15 are (read from the docs, not guessed)

| Gap | Definition (source) | State at entry |
|---|---|---|
| G3 | "Predicate trace supplied to the verifier" (`docs/claim-check-map.md` §3; B7 in `docs/baseline-status.md`) | Open: `RecursiveSNARK::verify(pp, n, z0, ids)` recomputes the trace hash from the host's `ids`. |
| G4 | "No in-circuit φ; id is a host constant" (`docs/claim-check-map.md` §3; N13 in `docs/protocol-spec.md` §2; `docs/P0-plan.md` N13/G4: Construction 2 computes `idx' ← φ(z_loc, z⃗)` in the circuit) | Open: the schedule is the prover's choice; the circuit of predicate k only hashes its constant k into the trace. |
| N15 | Trace digest `(t + id + 1)² + id + 1` is not collision resistant | Closed for v2 in P5 (Poseidon chain). Kept closed; the v1 code is frozen and still uses the old digest (historical, B15). |

So G4 is exactly the in-circuit φ. Closing φ closes G4; G3 is closed by making `verify` recover the trace from the proof. (PLAN.md §10 also has a *release gate* called G4 for P9–P10; that is unrelated.)

## 1. Design

### 1.1 `PredicateFamily` (new `Nova/src/kilonova/family.rs`)

A family is the authenticated list of the K predicate shapes the HFS folds over (in the recursion: the K primary augmented circuits, each containing its application F_k and φ):

- `label` (family name), **stable member ids** (strings, unique; position k is the protocol id absorbed in the transcript and used for e_k / ι_k), the public interface (`arity` of the state, `num_io`), a **selector descriptor** (canonical bytes describing φ), the shared `CcsTemplate`, and K `CcsShape`s with identical padded dimensions.
- **Canonical matrix encoding**: byte-identical to `kn_ccs::encode::encode` (`"KNCCS\x01" | m | num_w | num_io | t | q | terms | t × (nnz | sorted (row, col, value))`, duplicates summed, zeros dropped). kn-ccs stays a dev-dependency (oracle) only; a test pins byte equality with `kn_ccs::encode` and round-trips through `kn_ccs::encode::decode`.
- **Family digest**: SHA3-256 → 250-bit field element (the existing `DigestComputer`) over `(FAMILY_VERSION, label, arity, num_io, selector, template, ids[K], member_digest[K], witness-key label/size, index-key label/size)`, where `member_digest[k] = SHA3-256(canonical encoding of member k)`. Streaming hash, so a 121k-row member is never materialised twice.
- `HfsParams::from_family(&family)`: same parameters as `HfsParams::new`, but the HFS digest (absorbed by every HFS v2 transcript, native and in-circuit) **is the family digest**. `HfsParams::new` and the frozen v2 test vectors are unchanged.
- Recursion: `ivc::PublicParams::setup(program, tpl)` builds the family from the synthesized primary circuits and the program's label/ids/selector; `pp_digest` covers the family digest; every link hash binds `pp_digest` and the family digest (the old `hfs_digest` slot now carries the family digest). `setup_pinned(program, tpl, expected_digest)` rejects a family whose digest differs (layer Setup).
- Rejection: reordering members or substituting a matrix changes the digest; `PredicateFamily::check_digest`/`check_member` reject at layer Input; a proof made under the modified family is rejected by the original parameters (the final link hash binds the digest, and every in-circuit HFS transcript absorbed it).

### 1.2 In-circuit predicate selection φ (G4) and trace recovery (G3)

Decision: **φ is a function of the public state, evaluated in-circuit, and the circuit of predicate k enforces φ(i, z_i) = k.** Concretely a new trait `ivc::PredicateProgram<F>: PredicateSet<F>` adds:

- `select(i, z) -> Option<usize>` (native φ) and `synthesize_select(cs, i, z) -> AllocatedNum` (in-circuit φ);
- `family_label()`, `member_id(k)` (stable ids) and `selector_descriptor()` (bound in the family digest).

The primary circuit of predicate k computes `sel = φ(i, z_in)` (with `z_in = z_0` and `i = 0` in the base case) and enforces `sel = k`. The next predicate is therefore not chosen by the host: the state `z_{i+1} = F_k(z_i)` produced by the current step determines `φ(i+1, z_{i+1})`, and the next step's circuit can only be the one whose constant equals it. This is the SuperNova program-counter design with the pc kept in the application state: a predicate that wants to choose its successor writes a pc register in z, and φ reads it. Compared with carrying a separate pc in the link hash it needs one φ evaluation per step and no special base case (pc₀ = φ(0, z₀)). Non-deterministic selection (φ reading private advice) is out of scope, because it would weaken the claim below.

The deterministic-schedule example: `ivc::program::Scheduled<P>` wraps any `PredicateSet` P and appends a **program register** `prog` to the state. `prog` holds the schedule as base-2^b digits (b = max(1, ⌈log₂ K⌉)), φ(i, z) = the low b bits of `prog` (in-circuit: a unique 253-bit decomposition, since `prog < 2^253 < p`), and every F_k sets `prog' = (prog − k)/2^b` (one constraint; exact because φ already forced the low digit to be k). A schedule of length T needs b·T ≤ 253 (K = 2: 253 steps; K = 4: 126; K = 16: 63). The P5 tests keep their meaning: they encode their old explicit schedule into `z_0` and the proof is now *forced* to follow it.

Verifier (G3): `RecursiveSNARK::verify(pp, n, z_0) -> ChainOutput { z_n, trace, last_id }` no longer takes `ids`. It reads the trace hash from the proof and checks it through the final link hash (the circuits computed it in-circuit from their constants, under φ). `verify_schedule(pp, n, z_0, expected_ids)` additionally compares the recovered trace with `H_trace*(expected_ids)` (new layer `Trace`); it is only a check on the recovered digest, never an input to verification. The prover API follows φ: `new(pp, program, z_0)` and `prove_step(pp, program)`; a hidden `prove_step_tampered(pp, program, Some(k), tamper)` lets tests force a disagreeing choice.

**Claim** (written into spec §9): for public `(pp, n, z_0)`, an accepted proof shows that there is a sequence of states z_0 … z_n and ids k_0 … k_{n−1} with `k_i = φ(i, z_i)` and `z_{i+1} = F_{k_i}(z_i)` (for some witness of F_{k_i}), and that the returned `trace = H_trace*(k_0, …, k_{n−1})`. When φ and every F_k are deterministic functions of the state (all fixtures here), the id sequence is unique given z_0, so the claim is "**this specific trace**", and the returned digest identifies it (Poseidon collision resistance). Without determinism it is "some φ-valid trace with this digest exists".

Version: the recursive layer becomes `IVC_VERSION = 2` with new tags `TAG_LINK = 0x4b4e_4956_4302_0001`, `TAG_TRACE = 0x4b4e_4956_4302_0002` (the link hash's digest slot changed meaning). HFS transcript v2 itself is unchanged (same layout; the absorbed digest value is the family digest when built with `from_family`); its vectors are untouched.

### 1.3 Index-span paths

New in `family.rs`:

- **Explicit folded-matrix path** `FoldedMatrices`: t canonical sparse matrices `M_{λ,j} = Σ_k λ_k M_{k,j}`, built from λ directly or step by step with the fold rule `M ← M + ρ·M_k` (running weight 1, incoming weight ρ, matching HFS v2 for μ = ν = 1); evaluated with eq tables.
- **Weighted-evaluation path** `weighted_eval(shapes, λ, r_x, r_y) = (Σ_k λ_k M̃_{k,j}(r_x, r_y))_j` over the fixed base matrices (what the decider does, written separately).
- Cross-checks (tests): explicit (step-by-step) = explicit (from λ) = weighted = the protocol's `v_j` = `decide` = kn-ccs `check_accs`, and kn-ccs `eval_matrix_mle` on the explicit matrix, for K = 1, 2, 4, 16, Direct and Span, over a native HFS chain with a seeded schedule; the λ tracked alongside equals the witness λ.
- **Support statistics** `SupportStats`: per-member nnz, the union of supports, nnz of the folded matrix after each step, the step at which λ becomes dense, and bytes of base matrices vs explicit folded matrices vs λ. Measured for a synthetic low-overlap family and for the real recursive family (K primary circuits) via `kn-scenario family`.
- Incoming input: e_k only (the incoming instance carries k; λ_inc = e_k is never transmitted); the running λ is updated by ρ and is not one-hot after the first fold.

### 1.4 Template embedding

All members share one template. The only embedding used is P5's `R1csPow5` family, where R1CS rows (the recursive verifier and R1CS members) sit in a t = 5 template with zero D/E: a zero-term embedding (exact for every u, unlike `lift_degree`, which is exact only for u = 1, P2). P4 adds a native test that folds a mixed family {zero-term-embedded R1CS member, native power-5 member} for several steps with u ≠ 1 and checks the decider and kn-ccs oracle, a check that `lift_degree` breaks for u ≠ 1, and reports the expansion cost (t, proof elements, primary rows).

## 2. Decisions

| Item | Decision |
|---|---|
| φ placement | in the circuit of the selected predicate, on (i, z_i); pc kept in the application state |
| Claim | "this specific trace" for deterministic programs (all fixtures); "some φ-valid trace with this digest" otherwise |
| `verify` | `verify(pp, n, z_0)` returns `(z_n, trace, last_id)`; optional `verify_schedule` compares |
| Family digest binding | replaces the HFS structure digest in the recursion (transcript digest slot and link hash slot); in `pp_digest` |
| G4 | closed by φ (G4 = "no in-circuit φ") |
| Matrix encoding | kn-ccs layout, byte-identical, cross-tested |
| v1 code | frozen (B15 evidence), not touched; B18 not touched |

## 3. Acceptance → evidence

| PLAN.md P4 acceptance | Test / record |
|---|---|
| K = 1, 2, 4, 16: step-by-step matrix evaluation = span-weighted evaluation (+ kn-ccs `check_accs`) | `family::tests::test_span_paths_agree_k{1,2,4,16}` (Direct and Span) |
| Forged ids rejected | `ivc::tests::test_p4_rejects_forged_ids` (trace / last id in the proof → LinkHash / LastIncoming); `family::tests::test_family_rejects_unknown_or_duplicate_ids` |
| Reordered family rejected | `family::tests::test_family_digest_binds_order_and_matrices` (Input), `family::tests::test_hfs_rejects_other_family` (HFS level), `ivc::tests::test_p4_rejects_reordered_and_substituted_family` (Setup, LinkHash) |
| Substituted matrix rejected | same three tests |
| Non-one-hot new input rejected | `family::tests::test_non_one_hot_incoming_rejected` (Decider), `ivc::tests::test_p4_one_hot_gadget_rejects_forged_bits` (circuit unsatisfied), CycleFold non-unit ι (`test_p4_cyclefold_rejects_non_unit_iota`) |
| Tampered span rejected | `family::tests::test_tampered_span_rejected` (Decider), `ivc::tests::test_p4_rejects_tampered_span` (Span: LinkHash; Direct comm_M: LinkHash / Decider) |
| Host schedule disagreeing with φ rejected | `ivc::tests::test_p4_rejects_schedule_disagreeing_with_phi` (verifier side: Trace; prover side: LastIncoming) |
| ≥ 2 predicates really change wiring | `ivc::tests::test_p4_members_change_wiring` (shapes differ outside constants) + kn-ccs `wiring_pair` members in the span tests |
| Template embedding (if used) | `family::tests::test_zero_term_embedding_folds` + expansion cost in the report |
| P5 recursion with family/φ: K = 2, 4; T = 1, 16; rejection suite; K = 16 if feasible | existing `ivc::tests` ported to φ; `test_ivc_chain_k16` (`#[ignore]`, run explicitly) + kn-run record |
| Setup iteration count; constraint delta of φ and family digest | `test_constraint_breakdown` (new category `selection`), report table |
| kn-scenario + `results/raw/p4-family.jsonl` | `kn-scenario family` (support growth / overhead vs K) and `kn-scenario ivc` (chains) |

## 4. Priorities (if time runs short)

1. `PredicateFamily` + digest + rejection tests. 2. φ/G3, `verify` without the schedule, P5 chains passing. 3. Span cross-check K = 1, 2, 4, 16. 4. G4 (= φ, item 2). 5. Support-growth/overhead records. 6. K = 16 chain.
