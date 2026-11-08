# P3 acceptance report: native-field HFS (transcript v2) with negative tests

Date: 2026-11-08. Plan: `docs/P3-plan.md`. Base: `eb0e213` (P3.0 spike), branch `p3-native-hfs` (not pushed). The records were taken at `be00567` (`implementation_dirty: false` in every record). The only later code change, `d35fd6b`, is `cargo fmt` whitespace in `kn-scenario.rs`.

Commits: `ae5c052` plan; `b149b1f` kn-ccs `wiring_pair` fixture; `8a76413` HFS v2 module, transcript v2, tests and vectors; `9a9c58b` `kn-scenario hfs`; `be00567` spec §8, claim map, blockers, README and AGENTS; `d35fd6b` fmt; `87ae576` records; and the final commit with this report, PLAN.md status, `versions.lock` and `configs/common.toml`.

## 1. Goal

PLAN.md §3 P3: a complete HFS without recursion, run over the native field of the folded relation, that lets different matrix indices enter the fold, with negative tests. This fixes B15 at the folding layer. Moving the recursion onto it is P5.

## 2. Scope implemented

**Assumption (D1 not yet confirmed by the maintainer).** Transcript v2 follows option (a) of `docs/P3.0-decision.md` (Nova fork plus CycleFold). The sponge is Poseidon over `E::Scalar` (`E::RO2`; for E1 = Pallas this is the field of the E1 circuit that will verify the HFS natively). Commitments, whose coordinates are non-native there, are absorbed as 4 × 64-bit limbs per coordinate plus the infinity flag. If option (b) is chosen, the transcript is re-frozen as v3. The algebra, tests and oracle do not depend on D1.

| Item | Where |
|---|---|
| New module, alongside v1: **native-field HFS v2**. It folds over `E::Scalar` with no `field_switch`. It is generic over the CCS template (t, q, d, multisets with repeats, coefficients) and over **μ running and ν incoming inputs (μ + ν ≥ 1)**. It has the Direct (committed λ, `comm_M[t]`) and Span (public λ) variants through one `Variant` trait. | `Nova/src/kilonova/hfs/{mod,structure,instance,sumcheck,nifs,decider}.rs` |
| Public parameters: template, K shapes, witness key, one index key of size t·K (disjoint generators per matrix), ι_k, structure digest. Bridge `CcsShape::from(&R1CSShape)`. | `hfs/structure.rs` |
| Native prover, succinct verifier (reads only instances, proof and parameters; never a witness or a matrix) and decider. Errors carry their detection layer (`HfsError::layer()` ∈ Input / Verifier / Decider). | `hfs/nifs.rs`, `hfs/decider.rs`, `hfs/mod.rs` |
| Transcript v2: `transcript::v2::{HFS_TRANSCRIPT_VERSION = 2, TAG_* = 0x4b4e_4846_5302_000{1..4}, absorb_commitment}`. The v1 constants are unchanged. | `Nova/src/kilonova/transcript.rs` |
| Spec §8 (objects, protocol for general (t, q, d, μ, ν), absorption order, detection layers, D1 assumption); claim-check-map §5; blocker register | `docs/protocol-spec.md`, `docs/claim-check-map.md`, `docs/baseline-status.md` |
| Frozen bincode test vectors (digest, all challenges, proof and folded instance of a (0,1) and a (1,1) fold) | `hfs/vectors/v2_{direct,span}_{r1cs,power5}.txt` |
| Fixture in the oracle crate: `gen::wiring_pair`, two predicates per template (R1CS, power(5)) with the same dimensions, different wiring, negative coefficients and full-field values, with `reps` chaining. The checker code is unchanged, and kn-ccs still does not depend on kilonova. | `ccs/src/gen.rs`, `ccs/tests/wiring_pair.rs` |
| `kn-scenario hfs` (template, variant, steps, reps, seed) | `tools/kn-run/src/bin/kn-scenario.rs` |
| v1 B15 evidence re-documented, not deleted: `test_known_issue_b15_scalar_r1cs_not_foldable_over_base` still asserts that **v1** rejects the counter-example, and the 4 ignored IVC tests carry an updated reason | `kilonova/nifs.rs`, `kilonova/mod.rs`, `kilonova/span/mod.rs` |

Not changed: v1 HFS (`nifs.rs`, `relation.rs`, `span/`), the gadgets, `RecursiveSNARK`, setup, inherited Nova modules, B18, `spike_p3.rs`. No new dependencies; `Cargo.lock` is unchanged.

Differences from the spike prototype: a Poseidon RO instead of Keccak; tags; a structure digest; μ/ν inputs (the base case is now a real (0, 1) fold instead of random points); input and shape validation; layered errors; one index key with disjoint slots instead of t labelled keys (so t is not limited to 8); and a decider that is independent of both the prover and kn-ccs.

## 3. Test configuration

Apple M4, 16 GiB, Darwin 25.6.0, rustc 1.92.0 (the pin), `--release`, `--test-threads=1`, and one rayon thread for the `kn-run` children. Development machine: no performance claims.

## 4. Results

```bash
cargo fmt --all --check                                                    # clean
cargo clippy -p nova-snark -p kn-ccs -p kn-run --release --all-targets -- -W clippy::all -A clippy::len_without_is_empty   # clean
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1      # 53 passed, 5 ignored, 198 s (before P3: 33 passed, 5 ignored; +20 hfs tests)
cargo test -p nova-snark --release --lib kilonova::hfs -- --test-threads=1 # 20 passed, 27 s
cargo test -p kn-ccs --release                                             # 21 passed (20 + wiring_pair)
cargo test -p kn-run --release -- --test-threads=1                         # 10 passed (unchanged)
results/raw/p3-hfs.jsonl                                                   # 28 records, all success, verification_ok = true
```

The 5 ignored tests are unchanged: 4 × B15 (v1 recursion) and 1 perf harness.

| PLAN.md P3 criterion | Evidence | Result |
|---|---|---|
| ≥ 2 predicates, same dimensions, different matrices, non-trivial (negative) coefficients and wrapping products, 100 alternating steps, the reference ACCS checker accepts **every** step (B8/B10) | `test_chain_100_{r1cs,power5}_{direct,span}`: K = 2 `wiring_pair`, random full-field x per step. Step 0 is a (0, 1) fold, steps 1–99 are (1, 1) folds alternating k. At **every** step the verifier output equals the prover output, the challenges are byte-identical, and `decide` and `kn_ccs::accs::check_accs` (Pedersen closure) plus the index opening accept. The final λ is dense (no entry 0 or 1). `test_chain_reps_both_templates` repeats this with reps = 3 and 8 (s up to 4, s′ up to 5). Also measured: 28 kn-run records, T up to 100. | ✅ R1CS and native d = 5, Direct and Span |
| B15 class folds | `test_b15_instance_class_folds_in_v2`: the exact `R1CSShape` of the v1 B15 test (via `CcsShape::from`), x = (2⁶³)⁴ + 7, then 9 random x; 10 folds, Direct and Span, verifier, decider and oracle. | ✅ native folding. v1 still fails, by design (recursion, P5) |
| Valid μ/ν combinations | `test_mu_nu_combinations`: (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2), (3,2) × {R1CS, power5} × {Direct, Span}. `proptest_random_ccs_fold`: 48 deterministic cases, each with μ, ν ∈ 0..2 (μ + ν ≥ 1), K ∈ 1..3, random m, num_w, num_io and templates R1CS, power(2..6), product(2..4) from `kn_ccs::gen::random_satisfiable`. | ✅ multi-input implemented, not only μ = ν = 1 |
| Mismatched input counts, lengths and degrees rejected explicitly | `test_rejects_mismatched_shapes`, all with `Layer::Input` and a named field: μ or ν off by one in either direction, μ = ν = 0, missing witnesses; io, r_x, r_y, v, comm_M and λ lengths; witness and λ lengths; predicate id = K; extra or missing round evaluations (degree d ± 1); a missing round; σ/τ/ε/θ counts; **a degree-3 proof against a degree-5 template** (rejected on `sc_x` evaluations); empty family, mixed dimensions, wrong number of matrices, invalid multisets and coefficients, out-of-range entries. | ✅ |
| Prover and verifier challenges agree byte for byte | `test_challenges_agree_bytewise` (bincode of `Challenges` and of the folded instance; every challenge < 2¹²⁸; proof and instance round-trip). Every positive fold in every test asserts the same. The vectors freeze the values. | ✅ |
| Tampering rejected, immediately or at a named terminal check; detection layer named | `test_negative_matrix`: **268 cases** over {Direct, Span} × {R1CS, power5}. **212 are rejected by the bare verifier and 56 by the decider**; each case asserts its layer and the decider/oracle verdicts agree (table below). `proptest_single_tamper_rejected`: 48 random single-scalar proof tampers, all rejected by the verifier. `test_noncanonical_field_element_rejected`: a scalar equal to the modulus in the proof bytes is rejected at deserialisation. | ✅ |
| Deferred claims must not escape the final check | Compensated ε, ε (z-claim) and θ tampering that keeps c_y: **the bare verifier accepts** (asserted), and the decider and the oracle reject (`Claim`). | ✅ |
| Fixed bincode vectors for NIFS, folded instance and transcript (v2) | `test_vectors_v2_{direct,span}_{r1cs,power5}` against `hfs/vectors/*.txt`; `test_commitment_absorption_matches_ro2` (limb encoding = `Commitment::absorb_in_ro2`; tag layout). | ✅ |
| Measurements via kn-run | 28 records, all success, below | ✅ |

### Negative tests by detection layer (`test_negative_matrix`, per variant and template)

| Tamper | Layer | Error (typical) |
|---|---|---|
| Any evaluation of any X or Y round | Verifier | `SumcheckRound` in the same round (evaluations 0, 1) or the next round, or `EndCheck` in the last round |
| σ_j, τ_j (+1, or two σ entries swapped) | Verifier | `EndCheck{X}` |
| ε_j, θ_j (+1) | Verifier | `EndCheck{Y}` |
| ε or θ changed with compensation so that c_y is unchanged | **Decider** (bare verifier accepts) | `Claim{0}` or `Claim{t−1}` |
| After the proof: incoming comm_W, io, swapped io, predicate id; running comm_W, index (comm_M / λ), u, io, r_x, r_y, reversed r_y (v1 point order), v | Verifier | `SumcheckRound{X, 0}` (the challenges change) |
| Y rounds swapped | Verifier | `SumcheckRound{Y, 0}` |
| Prover or verifier uses the v1 input tag, the other variant's input tag, or the v1 X-claims tag | Verifier | `SumcheckRound{X/Y, 0}` |
| Prover or verifier uses the v1 **Y-claims** tag | **Decider** | `Commitment`. Only ρ changes: the verifier accepts a valid fold under another ρ, and the verifier's instance does not open to the prover's witness. Named here because it is the one tag whose mismatch the bare verifier cannot see. |
| Honest proof over an inconsistent running comm_W, an inconsistent running index or an inconsistent incoming comm_W | **Decider** | `Commitment`, `IndexCommitment{0}` (Direct) or `SpanIndex` (Span) |
| Honest proof with a wrong running claim v, or an unsatisfied incoming witness | Verifier | `SumcheckRound{X, 0}` |
| Folded output: v, u, io, r_x, W, λ | **Decider** (and the oracle) | `Claim`, `Commitment`, `IndexCommitment` / `SpanIndex` |

### kn-run records (`results/raw/p3-hfs.jsonl`)

Commands: `target/release/kn-run scenario hfs template={r1cs,power5} variant={direct,span} steps={10,100} --seed {101,202,303} --experiment p3-hfs`, plus `reps=64 steps=10 --seed 101`. Per-step values are the medians over all steps of all seeds. Times are in-process, one thread, on the development machine, **for orientation only**.

| variant | workload | T | seeds | d | m | n | s/s′ | prove ms | verify ms | decide ms | oracle ms | NIFS proof bytes (step 0 / later) | instance bytes | params ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| direct | r1cs, reps 1 | 10 / 100 | 101, 202, 303 | 2 | 2 | 4 | 1/2 | 2.04 | 2.06–2.07 | 1.14 | 1.14 | 632 / 872 | 488 | 98 |
| direct | power5, reps 1 | 10 / 100 | 101, 202, 303 | 5 | 2 | 4 | 1/2 | 1.74–1.76 | 1.76–1.78 | 0.83–0.85 | 0.83–0.85 | 664 / 840 | 424 | 96 |
| span | r1cs, reps 1 | 10 / 100 | 101, 202, 303 | 2 | 2 | 4 | 1/2 | 1.28 | 1.30 | 0.26 | 0.26 | 632 / 872 | 456 | 97–98 |
| span | power5, reps 1 | 10 / 100 | 101, 202, 303 | 5 | 2 | 4 | 1/2 | 1.28–1.30 | 1.30–1.31 | 0.26–0.28 | 0.26–0.28 | 664 / 840 | 424 | 99–100 |
| direct | r1cs, reps 64 | 10 | 101 | 2 | 128 | 130 | 7/8 | 5.55 | 4.75 | 3.51 | 3.54 | 2,072 / 2,312 | 872 | 118 |
| direct | power5, reps 64 | 10 | 101 | 5 | 128 | 130 | 7/8 | 5.28 | 4.45 | 3.07 | 3.09 | 2,680 / 2,856 | 808 | 118 |
| span | r1cs, reps 64 | 10 | 101 | 2 | 128 | 130 | 7/8 | 4.77 | 3.95 | 2.54 | 2.57 | 2,072 / 2,312 | 840 | 121 |
| span | power5, reps 64 | 10 | 101 | 5 | 128 | 130 | 7/8 | 4.68 | 3.84 | 2.50 | 2.52 | 2,680 / 2,856 | 808 | 116 |

Peak RSS ≤ 6.8 MiB and wall time ≤ 0.8 s per record. The NIFS proof size depends on (s, s′, t, deg_x, μ, ν) and is the same for Direct and Span; step 0 is the (0, 1) fold, which has no σ/ε. The running instance is larger for Direct when t > K (R1CS: 3 commitments against K = 2 scalars). Direct's decider and verifier are slower because of the group operations on comm_M; the verifier's time is dominated by Poseidon at these sizes. "params ms" is `HfsParams::new` (Poseidon constants, Pedersen keys, digest).

Determinism: re-running `hfs template=power5 variant=direct steps=100 --seed 101` into a scratch file gave the same input digest `5c99d19c…` and result digest `aed2eefc…`. All 28 records have distinct input and result digests.

## 5. Known limitations

- **No recursion and no gadget.** v2 is native only. `RecursiveSNARK`, the augmented circuits and their gadgets still run v1, so **B15 is still open for recursion**, the 4 multi-step IVC tests stay ignored, and `test_known_issue_b15_*` cannot flip yet. PLAN.md §9 still forbids any claim of working multi-step recursion.
- **The D1 choice is assumed.** The transcript's sponge field and commitment encoding follow option (a), which has not been confirmed.
- **Not a security proof.** Knowledge soundness of the generalised (t, q, d, μ, ν) protocol is not written; the tests only exercise it. The ε/θ deferral and the ρ-only effect of the Y-claims tag mean the decider is a required part of soundness, not an optional extra check (claim-check-map §5).
- The decider evaluates matrix MLEs with per-entry bitwise eq products, O(nnz·(s + s′)·K). That is fine as a reference, not as a final verifier (P7).
- The prover is single-threaded and builds dense tables of size 2^s and 2^{s′}. Timings come from the development laptop and toy sizes (m ≤ 128), so they are not performance data.
- Predicate selection φ and the trace chain are P4. `wiring_pair` is a synthetic family, and the semantic high-degree workload is still only the fifth-power chain (P2).
- No independent review of this evidence has happened yet (PLAN.md §2).

## 6. Open issues

- P5: v2 gadget over `E1::Scalar` with E1 points as limbs and group operations as CycleFold hints; switch `RecursiveSNARK`; flip `test_known_issue_b15_*` and un-ignore the IVC tests; replace the v1 cross-checks (`test_transcript_native_matches_gadget_*`) with v2 ones. The in-circuit transcript must absorb exactly the §8.5 sequence (`absorb_commitment` = 9 elements per point).
- D1 confirmation. If (b) is chosen, re-freeze the transcript as v3.
- B18 (inherited Nova compression tests) is untouched here; another session is fixing it.
- The P2 conventions cross-test (`test_kn_ccs_matches_kilonova_conventions`) still compares v1 over `E::Base`. The native-field agreement for v2 is covered by the decider and oracle agreeing on every fold.

## 7. Entry conditions for P4 / P5

- **P4** can start on v2: `HfsParams` already has a family digest, shared template and dimensions, and dense λ spans. P4 adds `PredicateFamily` IDs, the explicit folded-matrix path against the weighted-evaluation path (the decider is the weighted path), and G3/G4.
- **P5** needs the D1 decision. v2's transcript (§8.5), vectors and `NIFS::verify` are the reference for the gadget. The gadget must reproduce `test_vectors_v2_*` challenge for challenge, and stay succinct (AGENTS.md invariant).
