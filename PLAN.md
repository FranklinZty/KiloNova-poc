# KiloNova Prototype Development and Experiment Plan

Version: 2026-10-05 (revision 2). Supersedes the 2026-09-21 plan, whose original Chinese text is kept in `docs/PLAN.zh.md`.

Status: P0 executed (see §0 and `docs/baseline-status.md`). P1 executed 2026-10-07 (`docs/P1-report.md`). P2–P10 not started. This file is a plan. Statements about the code are backed by the commands and tests named in the P0 reports. Nothing here is a performance or security claim.

## 0. What changed in this revision, and why

The 2026-09-21 plan assumed Sonobe as the code base and a protocol that had not yet been implemented. The repository is different. It is a fork of Microsoft Nova (`Nova/`, `nova-snark` v0.42.0), and it already contains an R1CS-specialised KiloNova with two-curve recursion, in two variants: Direct (committed index) and Span (public λ). `docs/P0-plan.md` rebased P0 onto this code base. Executing P0 then produced the following facts, which reshape the rest of the plan.

| # | Finding | Evidence | Effect on the plan |
|---|---|---|---|
| F1 | The recursion layer could never be set up. The in-circuit HFS verifier recomputed σ/τ/ε/θ from the other curve's full witness, so one fixed-point iteration turned a 26,897-constraint primary circuit into a 44,227,419-constraint secondary circuit. No fixed point exists, because each circuit allocates at least twice the other's witness. | `kilonova::tests::test_setup_fixed_point_converges` (before/after numbers in `docs/baseline-status.md` §2) | **Fixed in P0.** The gadget is now succinct and setup converges in 2 iterations (primary 72,760 and secondary 72,951 constraints, both padded to 2^17). |
| F2 | The NIFS transcript did not bind the running instance U₁ or its index ι′ (B4). It also did not bind σ,τ before δ, or ε,θ before ρ (B16, new). This was a knowledge-soundness gap, and the old gadget only masked it by recomputing those values. | `test_nifs_rejects_substituted_running_instance` fails on the old code and passes now; `test_nifs_rho_binds_y_claims` | **Fixed in P0.** Frozen as HFS transcript v1 with domain tags, identical in all four places (native and gadget, Direct and Span), and checked by `test_transcript_native_matches_gadget_{direct,span}`. |
| F3 | **The HFS runs over `E::Base` on witnesses projected from `E::Scalar`, but the R1CS lives over `E::Scalar` (B15, new).** The projection `field_switch` is not a field homomorphism, so any constraint with a negative coefficient or a wrapping product stops holding. | `test_known_issue_b15_scalar_r1cs_not_foldable_over_base`. The 2-step IVC test now fails fast with `HFS zero-check failed … (B15)`. | **Open, and it is the critical-path blocker.** Multi-step recursion cannot work until folding runs over each instance's native field. This needs a CycleFold-style split (§3, P3 and P5) or an equivalent. This is an architectural change, not a patch. |
| F4 | The commitment keys were sized from unpadded shapes, so the very first `RecursiveSNARK::new` panicked (B17, new). | `test_ivc_nontrivial_nonuniform_bootstrap` | **Fixed in P0.** The 1-step chain now verifies, in 73 s with 3.3 GiB peak RSS on a 2-vCPU, 7 GiB Linux VM. |
| F5 | The index-commitment binding G1 (`M` against `commit(λ)`) and the witness binding are decider checks by design, exactly like `comm_W` in Nova. They do not need to be in-circuit constraints. | `docs/claim-check-map.md` | G1 is closed as "deferred to the decider". The decider becomes the main correctness surface (P7). |

The consequences for feasibility:

1. **Base: stay on the Nova fork for now, but decide at the P3 gate (decision D1).** Fixing B15 means building CycleFold-style infrastructure here, or porting the HFS onto a library that already has CycleFold, CCS and HyperNova (Sonobe). A time-boxed 2-day spike for each option decides it (P3.0). The plan is written so that either choice keeps the P3–P10 acceptance criteria.
2. **The critical path is P3 → P5 → P7**, not P1. P1 shrinks to a minimal harness. The full bench-runner moves to just before P8/P9.
3. **High-degree CCS (deliverable 3) is a protocol generalisation, not a builder task.** The HFS code hard-codes t=3, d=2 and μ=ν=1. The `folding/` crate is generic over CCS and can serve as a slow reference oracle once its known defects (B11, B12, B14) are fixed.
4. **The 16 GB development laptop is not an experiment machine.** Formal runs (P9) need a fixed Linux host with ≥64 GB RAM.

## 1. Goals, sources and boundaries

The goal is to deliver an independently verifiable prototype of non-uniform recursive proofs for a fixed predicate family, and to establish through fair and reproducible experiments where it helps and where it does not. Experiments do not replace a security proof, and they do not guarantee acceptance at any venue.

Sources:

- Current paper: `/Users/franklinzty/LatexProjects/Paper-KiloNova/KiloNova.tex`.
- Review and revision material in the same directory: `review/s&p27.md`, `review/crypto26.md`, `review/sp27_revision_checklist.md`, `review/sp27rebuttal.md`.
- This repository at the P0 tag, plus `docs/protocol-spec.md` (normative), `docs/claim-check-map.md` and `docs/baseline-status.md`.
- The review checklist is only a map of risks. Old line numbers and tick marks do not replace a re-check of the current source, paper and protocol, and promises made in the rebuttal are not evidence of implementation.

Required deliverables:

1. Correct reference implementations of native R1CS/CCS, ACCS and holographic folding, **with folding over each instance's native field**.
2. A real non-uniform recursive chain over a fixed predicate family, and at least binary PCD. Public state and scheduling semantics must be constrained.
3. At least one native high-degree CCS workload that completes recursion and final verification. Converting R1CS to CCS does not count as native high degree.
4. An independent final verifier and a compressed proof bound to its public statement. Zero knowledge is explicitly not claimed.
5. Same-library ablations, same-library baselines, external baselines and a reproducible artifact.

Out of scope for the first version: a full zkVM, general memory consistency, dynamic circuit registration, a general CCS DSL, GPU support, arbitrary DAG schedulers, and any unproven ZK extension.

## 2. Organisation and common definition of done

The work is split into eleven sub-periods. Durations are working-day estimates for a developer familiar with Rust, the Nova/arkworks stacks and recursive proofs. They are not commitments. Re-deriving the protocol, fixing dependencies and writing security arguments can exceed them. After P3.0, re-schedule from measurements, and never let a deadline replace acceptance.

Each sub-period delivers a fixed commit/tag, an acceptance report and runnable test commands. The report states at least: goal, scope implemented, test configuration, results, known limitations, open issues and the entry conditions for the next period. Any protocol change bumps the protocol version and the test vectors. The transcript version lives in `Nova/src/kilonova/transcript.rs`.

Common definition of done:

- `cargo fmt --check`, clippy on the touched modules, and the unit and integration tests pass. Known third-party or inherited warnings are listed separately; P0 lists the remaining clippy findings in inherited Nova modules.
- Positive cases pass and the specified tamper cases are rejected. Nothing may pass by disabling checks, shortening security parameters or dropping recursion steps. Tests that document a known defect are marked `#[ignore = "known issue Bxx …"]` or named `test_known_issue_*`, and must be flipped when the defect is fixed.
- The native verifier and the gadget use the same canonical serialisation, transcript order, degree bounds and domain separation, enforced by cross-implementation tests like `test_transcript_native_matches_gadget_*`.
- Every performance number traces to a configuration, source revision, input digest and raw run log.
- Someone other than the implementer reviews the acceptance evidence. If nobody is available, schedule a separate review pass, and never claim an independent security audit.
- Standard test command (memory-safe on 16 GB): `cargo test -p nova-snark --release --lib kilonova -- --test-threads=1`.

## 3. Sub-periods and acceptance gates

### P0: Protocol and dependency freeze (done 2026-10-05; 3–5 days planned, about 5 used)

Goal: a single executable specification with no ambiguity between the paper's notation and the code.

Delivered: `docs/protocol-spec.md`, `docs/claim-check-map.md`, `docs/baseline-status.md`, `versions.lock`, `configs/common.toml` and `rust-toolchain.toml`. With user approval, P0 also delivered code fixes for F1, F2 and F4, plus the B15 evidence test.

Exit status: met, with B15 recorded as an open blocker. The acceptance items from the 09-21 plan map as follows:

- Every public field, private field and challenge has a unique producer and consumer: ✅ `docs/claim-check-map.md`.
- The start and end equations of both sum-checks derive from the same polynomial: ✅ The γ⁰…γ³ and δ⁰…δ⁶ assignments agree across `compute_sum_*`, `sumcheck_prove_*` and `compute_c*`. They differ from the revised paper's γ^{t+1}, which is an equivalent rescaling (N7 and N8 in the spec).
- The fold output feeds directly into the next ACCS round: ✅ natively and in the gadget, including ρ. Fixed serialisation vectors are deferred to P3, because the transcript changes again with B15.
- Key tests can be re-run, and missing capabilities are listed as gaps: ✅
- Open correctness or security issues are listed as blockers: ✅ B15, plus G2–G4, which move to P4/P6/P7.

### P1: Minimal experiment harness (done 2026-10-07; 2–3 days; depends on P0; may run alongside P3)

Delivered: `tools/kn-run` (`kn-run` runner + `kn-scenario` child), `results/schema.json`, `SetupReport`/`predicate_constraint_counts`, README section. Detailed plan `docs/P1-plan.md`, report `docs/P1-report.md`. Open: OOM classification is verified only on Linux, which has not been run yet.


Goal: every later report uses the same measurement conventions from day one, without building the full bench-runner yet.

Work: a `kn-run` binary or script that runs one named test or scenario in a fresh process and records wall time, peak RSS (via `getrusage` of the child), git revision, `versions.lock` hash and status (success/failure/timeout/OOM). It appends JSONL to `results/raw/`. Add a `CountingCS`-based constraint report for the augmented circuits; the type already exists in `kilonova/mod.rs`.

Deliverables: `tools/kn-run`, `results/schema.json` (the field list in §8), and a README section.

Acceptance:

- The same seed and configuration produce the same semantic inputs and results.
- Actual thread counts, matrix sizes and witness sizes are recorded, not just the requested values.
- Every record has a status, and failures are never silently dropped.
- Timing boundaries are validated with an empty run and a known-size buffer.

The full workload generator, adapters and config validator move to P8.

### P2: Native CCS construction and ACCS reference checker (5–8 days; depends on P0)

Goal: real support for high-degree constraints, plus a slow correctness oracle that is independent of the protocol code.

Work:

- `NativeCcsBuilder`: sparse matrices, multisets with repeated indices, fixed coefficient templates, public/private layout, padding and validity checks. It lives in a new crate or module in the workspace and uses the **same field types as `Nova/`** (ff/halo2curves), so no arkworks conversion is needed.
- R1CS, the fifth-power relation, and relations of configurable degree. Do not just call an R1CS-to-CCS conversion.
- An independent ACCS relation checker and a small explicit matrix/MLE evaluator. Two candidates: port `folding/`'s generic CCS checks after fixing B11 (wrong serial path), B12 (silent `zip` truncation) and B14 (reversed variable order); or write a minimal checker from scratch. Pick whichever is faster, and record the choice.
- Fix the layout adapter: `z = (w ‖ u ‖ io)` with the low-bit-first variable order (spec N2, N9). `folding/` uses `(u ‖ io ‖ w)` and must be adapted.

Deliverables: CCS builder, ACCS types, native witness generator and reference evaluation tests.

Acceptance:

- For d = 2, 3, 5, 8 and 16, at least 100 deterministic random small instances each agree with naive evaluation.
- The fifth-power constraint really uses a repeated multiset, with no intermediate multiplication witnesses added to reduce it to degree two. Report the difference from the equivalent R1CS.
- Tampered witnesses, out-of-range matrix indices, wrong dimensions and non-canonical encodings are rejected. Degenerate all-zero matrices and boundary sizes have tests.
- Semantics are preserved across CCS embedding and padding, and the overhead is measured.

### P3: KiloNova native folding over the correct field, with negative tests (10–16 days; depends on P2; P3.0 decides D1)

Goal: a complete HFS without recursion, run over the native field of the folded relation, that lets different matrix indices enter the fold.

- **P3.0 decision spike (2 days, hard time box).** Resolve B15 on paper and in a prototype:
  - (a) *Nova fork + CycleFold*: run the HFS for E₁-instances over E₁::Scalar inside the E₁ circuit (native sum-check). Delegate the ≤4 group scalar multiplications per fold (comm_W and the three comm_M) to a small E₂ "CycleFold" circuit, folded with plain Nova NIFS.
  - (b) *Port to Sonobe*: put the HFS on Sonobe's CCS/HyperNova/CycleFold stack at a pinned commit. First run its CCS, HyperNova, ProtoGalaxy and CycleFold tests.
  - Output: a one-page decision memo with measured smoke results, the expected constraint count per step, and the porting cost. The rest of the plan is unchanged by the choice. Only file paths and P8's "same-library" set differ.
- Make the HFS generic over the field of the folded relation. It must not project through `field_switch`. `test_known_issue_b15_*` must flip.
- Generalise from (t=3, d=2, μ=ν=1) to the CCS parameters P2 needs (t, q, d), first for μ=ν=1 and then for the multi-input interface the paper requires.
- Keep the Direct (committed λ) and Span (public λ) representations as ablation baselines.
- Freeze fixed bincode test vectors for `NIFS`, `FoldedInstance` and the transcript, as transcript v2.

Deliverables: native prover and verifier, fold-output checker, protocol vectors, and fuzz/property tests.

Acceptance:

- At least two predicates of the same dimensions but different matrices, with non-trivial coefficients, fold in alternation for 100 steps. That includes negative coefficients and wrapping products, so the B8 and B10 gaps are closed. The reference ACCS checker accepts the output of every step.
- Valid combinations of μ and ν are tested. Mismatched input counts, lengths and degrees are rejected explicitly.
- Prover and verifier challenges agree byte for byte. Tampering with sum-check coefficients, evaluations, commitments, field order, transcript tags or the running instance leads to rejection, either immediately or at an explicitly named terminal relation check.
- Negative-test reports name the detection layer. A deferred claim must not be required to fail in the bare folding verifier, but it must not escape the final check either.
- Tests are not a substitute for a knowledge-soundness proof. If the security specification still has an open gap, the blocker flag stays.

### P4: Fixed predicate family and index-span (5–8 days; depends on P3)

Goal: make non-uniformity an authenticated protocol state instead of a branch in the host program.

Work:

- `PredicateFamily` with stable predicate IDs, a family digest and the matrix encoding. In the first version, all predicates share a public interface, padded dimensions and a CCS template.
- An incoming predicate k uses the unit vector e_k. Update the span with the protocol challenge; the running instance's span is not forced to be one-hot.
- An explicit folded-matrix path and a weighted-evaluation path over the fixed base matrices, cross-checked against each other.
- Record the growth of the union of supports and the preprocessing and memory overhead. Do not assume a folded matrix keeps the original sparsity. λ becomes dense after a few steps, so this is an inherent K-dependent cost; it is written into the spec.
- **Close G3, G4 and N15.** Replace the algebraic trace digest `(t+id+1)²+id+1`, which is not collision resistant, with a Poseidon hash chain over predicate IDs computed in-circuit. Add the in-circuit predicate selection φ, so the schedule is constrained rather than supplied by the host. Make `verify` recover or check the trace from the proof instead of taking it as an argument.

Deliverables: family preprocessor, span types and gadget, and native non-uniform examples.

Acceptance:

- For K = 1, 2, 4 and 16, step-by-step matrix evaluation agrees with span-weighted evaluation.
- Forged IDs, reordered families, substituted matrices, non-one-hot new inputs and tampered spans are each rejected by the corresponding full check path.
- At least two predicates really change the wiring structure, not just public inputs or constants.
- If different templates must be embedded, provide semantics-preservation tests and the real expansion cost. Zero padding alone does not establish compatibility.

### P5: Real non-uniform recursive chain (10–15 days; depends on P4 and the P3.0 decision)

Goal: bind the execution trace, the index representation and the accumulator inside the recursive circuit.

Work:

- Implement the augmented circuits for the chosen D1 option, including the CycleFold-style auxiliary circuit if (a). The HFS verifier gadget must stay **succinct**: it uses only prover messages and public instances, never the other circuit's witness (a regression test guards the fixed point).
- Constrain the family digest, initial and current state, step count, current ID, predecessor instance and output instance to be consistent.
- The first version uses an explicit deterministic schedule. If external scheduling is supported, state whether the claim is "some valid trace exists" or "this specific trace", and implement the matching binding.
- Connect native high-degree applications to the augmented CCS. The recursive verification logic can be embedded as R1CS, but lowering all of the application's high-degree constraints and calling the result end-to-end high degree is not allowed.

Deliverables: `prove-chain`, `verify-reference`, per-component constraint counts for the recursive circuit, and two-predicate and multi-predicate chain examples.

Acceptance:

- Valid chains with K = 2 and 4 and T = 1, 16 and 64 all pass. At least one native d=5 application closes the recursive loop.
- A wrong initial state, skipped step, repeated or wrong counter, swapped steps, wrong predicate choice or broken state link is rejected.
- Report absolute constraint counts for the application, sum-check, hashing, span, witness group operations and the auxiliary-curve proof, without double counting.
- Chaining independent per-step proofs, or checking in the host, is not recursion. The final check must authenticate the whole chain.
- The setup fixed point converges within `MAX_SETUP_ITERATIONS` for every configuration used later; record the iteration count.

### P6: Multi-predecessor PCD and workload closure (7–12 days; depends on P5)

Goal: tree-shaped execution, isolating the effects of arity and of the number of predicates.

Work: binary merge first, then a = 4 and 8 **if time allows** (a = 2 is mandatory, a = 4/8 is stretch). Bind leaf task and position, predecessor order, sub-task ranges, node outputs and the root claim. Fix the dummy-leaf rule, and state the node semantics and the recursion base case.

Deliverables: `prove-tree`, a task-tree generator, the root statement format and a tree correctness report.

Acceptance:

- With 64 fixed real leaf tasks, every supported a computes the same target result. Padding and internal-node work are reported separately.
- Duplicate leaves, missing leaves, cross-task splicing, illegal order and forged predecessors are rejected. If a task allows repeated inputs, "same input" must still be distinguished from "same position".
- Total sequential CPU work and parallel wall-clock latency are reported separately. The main single-threaded results never mix in parallel gains.
- The mapping between multi-input folding μ/ν and PCD arity is written into every configuration. Never assume a = μ + ν.

### P7: Independent final verification and compression (10–20 days; depends on P5; tree coverage depends on P6)

Goal: a final verifier that depends only on declared public material and the proof, with no prover-private state. Today `RecursiveSNARK::verify` needs the folded witnesses (G2), as Nova's uncompressed `RecursiveSNARK` does.

Work:

- **P7a, reference-basis decider (first milestone):** prove the witness parts with a PCS opening (z̃*(r_y) = v₃, plus the opening of comm_W) and a Spartan proof for the auxiliary/secondary relation. The **verifier evaluates M̃ᵢ(r_x, r_y) for every base matrix itself** and checks Σλᵢ·M̃ᵢ = v_j. For Direct, the verifier also checks comm_M against λ, which then has to be revealed. This is succinct in the witness but O(K·N) in the index. Label it `reference-basis-decider` and report its K dependence.
- P7b: the paper's sparse evaluation (Spark-style holography) with terminal recursive binding. Keep the homomorphic top-level matrix commitments separate from the row/col/val auxiliary encodings; the latter cannot be folded linearly entry by entry without a proof.
- State how the witness commitment, the full assignment commitment, the matrix evaluation point and value, and the final application output relate.
- Separate-process prover/verifier file interfaces, recording the public preprocessing material and SRS.

Deliverables: `compress`, `verify-final`, a public proof format, a terminal-check map and a real communication-cost account.

Acceptance:

- After the prover's private checkpoint is deleted, the independent verifier still verifies chain and tree proofs, and never reads a witness from an undeclared cache.
- Changing the family, final output, step count or task size, span, evaluation point, evaluation value, opening or recursive output binding causes rejection.
- Measure a warm verifier with preloaded material and a cold verifier loading from files, including matrix reconstruction and virtual commitment computation.
- Account for proof bytes item by item from the message format, and match the real serialisation. State the dependence on K, N and the matrix dimensions.
- If the paper's optimisation is not implemented, or its proof is not closed, only the intermediate version (P7a) is accepted, and the full compression period is not marked done.

### P8: Baselines and fairness acceptance (7–12 days; tool integration can start after P3)

Goal: keep each scheme's original protocol semantics, and produce two kinds of comparison.

Work:

- The full bench-runner deferred from P1: workload generator, adapters and config validator.
- Same library: depends on D1. With the Nova fork: Nova (uniform IVC, existing), KiloNova-Direct, KiloNova-Span, and a correctly constrained dispatcher route. HyperNova and ProtoGalaxy are then external. With Sonobe: HyperNova, ProtoGalaxy, KiloNova-Direct and KiloNova-Span.
- External: SuperNova via Arecibo, and KZH-Fold via the authors' implementation (KZH-Fold is stretch). Pin the commits that actually run and their comparable capabilities. Do not assume they support every chain, tree or high-degree feature.
- Native high-degree HyperNova is the preferred comparison. The inspected Sonobe ProtoGalaxy instance is bound to R1CS; a high-degree extension is a separate version that must be re-tested, not an existing feature.
- A dispatcher must constrain all of its selection logic. It may not run a Rust branch on the witness and then reuse a mismatched key.
- Compare `KiloNova-Span + reference decider` against the optimised decider under the same configuration.

Deliverables: adapters, a capability matrix, same-semantics test vectors and a fairness review table.

Acceptance:

- Every baseline produces the same public result on the same application trace, and really verifies.
- Same-library comparisons unify compatible curves, commitments, transcripts and security parameters. Anything that cannot be unified with an external baseline is disclosed item by item, and cross-backend ratios are never presented as pure protocol gains.
- A fixed K=1 circuit is not presented as a functionally equivalent baseline for a K>1 task.
- SuperNova's serial work is not called same-arity multifolding. PCD comparisons only use capabilities that are actually implemented.
- A simple dispatcher is not presented as a general circuit with logarithmic overhead. If the latter is not implemented, keep the theoretical discussion and its limits in the paper.
- If a scheme has only folding or only a gadget, it appears only in the matching table. Missing data is N/A with a reason, never zero.

### P9: Freeze parameters, formal experiments and claim audit (5–10 days plus batch machine time; depends on P7/P8)

Goal: measured results with uncertainty and complete costs.

Work: run the experiment matrix of §§5–8. Run a pilot first to freeze configurations and resource caps, then sample formally. Analyse break-even points, memory and final verification cost. **Runs happen on the dedicated Linux host from §5.2, never on the development laptop.**

Deliverables: immutable raw JSONL, summary tables, plotting scripts, a configuration list per figure and a claim-to-evidence map.

Acceptance:

- Every formal configuration uses at least 3 input seeds, with 2 untimed warm-ups and 10 timed runs per seed. Expensive configurations, flagged in advance, may drop to 5 runs per seed. Reducing samples after seeing the results is not allowed.
- Every successful run executes its verification. Failures, timeouts and OOMs are all kept.
- Main tables report median, IQR and sample count. Main speedups come with paired statistics and seed-grouped bootstrap intervals; repetitions of the same seed are not independent workloads.
- Main results cover both favourable and unfavourable regions. Losses at large K, small T or small circuits are never removed.
- Formal data never reuses numbers from older paper figures. Any existing number is either re-run or labelled historical and kept out of the statistics. **In particular, the constraint counts from `NIFS-circuit/` (the old paper figures) are historical and must not be reused.**

### P10: Artifact, paper alignment and reproduction (3–5 days; depends on P9)

Goal: an outside reader can verify the scope, re-run the minimal examples and regenerate the main results.

Deliverables: README, dependency lock, minimal demo, full experiment commands, raw data, figure sources, known limitations, and the commit the paper corresponds to.

Acceptance:

- A clean environment can run the small chain, tree and high-degree examples and the tamper-rejection tests.
- An independent reproduction of at least one end-to-end group, one K scan and one high-degree CCS result matches in functionality and byte counts. If median times differ by more than 15%, investigate and record the environment differences, but do not conclude that correctness failed and do not rewrite data.
- The paper no longer confuses the private checkpoint, the public uncompressed state and the final proof. Every figure has units and full parameters.
- The README states explicitly: non-ZK, fixed predicate family, which recursive structures are supported, and which modules are not implemented. Passing tests is never called passing a security audit. The current README and `folding/README.md` claims of "zero knowledge" are removed in P0.

### Schedule summary (estimates, single developer)

| Period | Days | Critical path | Notes |
|---|---|---|---|
| P0 | done | — | |
| P1 | done | no | |
| P2 | 5–8 | yes | |
| P3 (incl. P3.0) | 10–16 | yes | D1 decided here |
| P4 | 5–8 | yes | |
| P5 | 10–15 | yes | |
| P6 | 7–12 | partly | a=4/8 is stretch |
| P7 | 10–20 | yes | P7a is the minimum |
| P8 | 7–12 | partly | KZH-Fold is stretch |
| P9 | 5–10 + machine time | yes | |
| P10 | 3–5 | yes | |
| **Total** | **≈64–109 working days** | | **≈13–22 weeks** before slack. Re-plan after P3.0. |

Minimum viable artifact, if time runs out: P2 + P3 + P4 + P5 (K∈{2,4}, T≤64, d∈{2,5}) + P7a + the same-library baselines + E1/E2/E5/E7/E9. Never cut recursion binding, final verification or negative tests (§9).

## 4. Code layout and versioning

The layout follows the current repository and does not require restructuring it.

```text
KiloNova-poc/
  Nova/src/kilonova/        # normative HFS (Direct) + span/ (Span ablation)
    relation.rs nifs.rs transcript.rs circuit/ span/ test_utils.rs
  <new> ccs/                # P2: NativeCcsBuilder, ACCS reference checker (same field types)
  tools/kn-run              # P1: process-isolated runner, JSONL output
  folding/                  # generic CCS PoC (arkworks): reference oracle only, not mainline
  NIFS-circuit/             # historical constraint-count model behind old paper figures; do not reuse numbers
  configs/ docs/ results/raw/ results/summary/ plots/
```

If D1 picks Sonobe, the Sonobe dependency is a pinned commit or fork with small patches, and the layout above maps to crates in that workspace. Automatic dependency updates are forbidden during experiments. External baselines can be wrapped as separate processes, so nobody has to rewrite cryptographic protocols just to unify dependency versions.

Source pointers (these are selection candidates, not claims that they passed this plan's acceptance):

- Sonobe: <https://github.com/ethereum/sonobe>, candidate commit `5ffe1fa91fbbb7ecf68cf226416ce82e4ea0155e` (CCS, HyperNova, ProtoGalaxy and CycleFold modules not yet compiled locally).
- SuperNova candidate implementation: <https://github.com/lurk-lang/arecibo>.
- KZH-Fold authors' implementation: <https://github.com/h-hafezi/kzh_fold>.

## 5. Common parameter contract

### 5.1 Symbols and configuration rules

| Parameter | Single definition | Default and sweep |
|---|---|---|
| K | Size of the fixed predicate family | Default 16; 1, 2, 4, 8, 16, 32, 64, 128 |
| m_app | Constraint rows of the application CCS, excluding the recursive verifier | Synthetic default 2^12; 2^10, 2^12, 2^14, 2^16 |
| n_app | Full assignment columns of the application, including the constant and public inputs | Synthetic reference n_app = m_app; real applications come from synthesis |
| w_app | Number of private witness field elements | Recorded separately, never mixed with n_app |
| m_aug, n_aug | Actual dimensions of the augmented predicate | Record raw and padded values after synthesis; never force them equal across schemes |
| d | Actual maximum product degree of the CCS | R1CS = 2; native high-degree main point = 5; sweep 2, 3, 5, 8, 16 |
| t | Number of matrices per CCS | R1CS = 3; high degree as recorded per template, never written as 3 by default |
| q | Number of CCS product terms | Recorded per template; degree-isolation experiments fix all other controllable factors in the template family |
| N_j, N_total | Non-zeros per matrix and in total | Measured, together with the support size after folding |
| s | Non-zeros per row of synthetic matrices | Default 3; sweep 1, 3, 8; not applicable to semantically constrained real circuits |
| T | Real application steps in a chain | Default 256; 1, 16, 64, 256, 1024 |
| a | Number of predecessors per PCD node | Default 2; 2, 4, 8; kept separate from μ/ν |
| μ, ν | Number of ACCS / CCS inputs per fold | Filled in explicitly per protocol instance, never inferred from K or a. **Currently μ = ν = 1.** |
| L | Real leaf tasks in a tree | Default 64; scale experiments 64, 256, 1024 |
| threads | Actual compute threads | Main results 1; extension experiments 8 if the machine allows |
| seeds | Semantic input seeds | Default 101, 202, 303; shared by all comparable schemes |

Application experiments prefer "same semantics"; native micro-benchmarks prefer "same relation and size". No scheme may do extra application work to match m_aug. All padding, dummy nodes and extra witness are listed separately.

Values currently hard-coded by the implementation are frozen in `configs/common.toml` (t=3, d=2, μ=ν=1, num_io=2). P3 generalises them.

### 5.2 Cryptographic and machine parameters

- **Curves.** The current code and all P0 measurements use Pallas/Vesta. Switching to BN254/Grumpkin is re-evaluated at the P3.0 decision, together with the PCS choice for P7. If an external baseline does not support the chosen cycle, list it in a separate platform group, and never switch curves silently.
- Curve names and 128-bit challenges are not by themselves 128-bit overall security. Record the curve security basis, challenge length (`NUM_CHALLENGE_BITS = 128`), hash output length (`NUM_HASH_BITS = 250`), number of sum-check rounds and the soundness budget under repeated recursion. These are frozen in `docs/protocol-spec.md` §6.
- Same-library witness commitments prefer a commonly supported configuration (Pedersen today). The compression PCS (IPA today) is registered separately from the witness commitment. KZH keeps its own PCS; the compared scheme is never changed to unify back-ends.
- The transcript hash (Poseidon), parameter generation, domain separation (`transcript.rs` tags), challenge encoding and hiding switches are all fixed. No instantiation may use an insecure number of rounds for performance.
- **Hosts.** Development and correctness work: the 16 GB macOS laptop, and the 2-vCPU, 7 GiB cloud Linux VM used in P0. Formal experiments: one dedicated Linux bare-metal host, or one explicitly pinned VM, with ≥64 GB RAM. Never mix WSL, macOS and Linux timing data. Record CPU model, cores, memory, OS/kernel, frequency governor, compiler and release flags.
- Control threads, CPU affinity and implicit thread counts such as rayon's (`RAYON_NUM_THREADS`), and stop other heavy loads. Fix and record whether turbo is on.
- Resource caps are frozen at the P9 pilot, using the dedicated host's RAM: memory cap at 80% of physical RAM, default per-run timeout of 30 minutes. The same cap applies to all schemes, and experiments with longer caps are listed separately. On the 16 GB laptop, tests must run with `--release --test-threads=1`.
- SRS and key generation and their sources are recorded separately. Incompatible SRSs never count as shared preprocessing, and setup cost is never charged to one scheme while being excluded from another.

## 6. Workloads and minimum experiment matrix

### W1: Controlled synthetic relations

Generate satisfiable sparse R1CS and native high-degree CCS separately, with a published generation algorithm. Making all effective constraints zero is forbidden. Matrix supports come in three patterns, shared, partly overlapping and low-overlap, and the actual overlap is measured, so that a "fully disjoint" assumption that cannot hold at large K is never built in.

Purpose: isolate the effect of K, m_app, d, sparsity and arity on native and recursive cost. Synthetic results are not extrapolated to real VM performance.

### W2: High-degree arithmetic and hashing

- A fifth-power chain, or a precisely specified MinRoot-style arithmetic kernel. Without the real MinRoot parameters and semantics, it is called a fifth-power arithmetic kernel.
- Poseidon with vetted parameters. The native CCS and R1CS paths prove the same inputs, outputs and number of rounds.
- High-degree d sweeps use synthetic relations. Never alter a real hash's security parameters to manufacture a degree experiment.

Purpose: show native high-degree support and the real cost of the same computation. Report application compression and recursive overhead separately.

### W3: Finite-state non-uniform application

Fixed-size registers of field elements, with predicates for add, multiply, select, constant update and hash update. This is explicitly not a full ISA or zkVM. Predicate selection agrees with the state or a bound task trace.

Family distributions: uniform, 90% hot predicate, and contiguous blocks, plus a heterogeneous circuit-size variant of about 1:4:16 with real sizes and max-size padding cost recorded. Distribution comparisons use the same K, T and input generation specification.

Purpose: test real scheduling, shared state and the gain from predicate switching, rather than only proving mutually unrelated random circuits.

### W4: Mixed-predicate task tree

Leaves run fixed arithmetic or hash tasks. Internal nodes verify and merge the sub-task digests and agreed results. Positions, counts and task identities are constrained. Different a values use the same real leaf tasks, and the difference in internal-node count is reported.

Purpose: separate total multi-predecessor PCD work from parallel latency.

### Required experiment groups

| Group | Varied | Fixed / purpose |
|---|---|---|
| E1 Correctness | W1–W4, boundary parameters, all negative cases | No performance; checks the claims close |
| E2 K scan | K = 1..128 (values above) | m_app = 2^12, d = 2, T = 256, including the final verifier and memory |
| E3 Scale scan | m_app = 2^10..2^16 (values above) | K = 16, d = 2, T = 64; shorter chain to limit cost, stated as differing from the default |
| E4 Crossover | K ∈ {1, 8, 32, 64, 128} × m_app ∈ {2^10, 2^12, 2^14} | T = 64, everything else fixed; not a full Cartesian product |
| E5 High degree | d ∈ {2, 3, 5, 8, 16} | Same synthetic template family and input size, plus a W2 same-semantics comparison |
| E6 Arity | a ∈ {2, 4, 8}, optionally crossed with d ∈ {2, 5, 8, 16} | L = 64; state each scheme's supported range |
| E7 Trace length | T ∈ {1, 16, 64, 256, 1024} | K = 16, fixed per-step work; total cost and amortisation |
| E8 Applications | W3's three distributions and the heterogeneous variant, W4 | Functionally equivalent systems; sizes arise naturally |
| E9 Ablation | Direct / Span / reference decider / optimised decider | Same inputs and parameters; change only one target factor at a time |

If the run budget is short, keep E1, E2, E5, E7, E8 and representative E9 points first, then cut stress sizes and parallel scaling. Never drop final verification, memory or the high-degree closed loop to keep a nice curve.

## 7. Common metrics and timing boundaries

### 7.1 Metrics by layer

| Layer | Required metrics | Notes |
|---|---|---|
| Setup | SRS/setup, family preprocessing time, **fixed-point iteration count**, peak RSS, prover/verifier material bytes | One-off costs listed separately, with whether they can be cached |
| Native folding | Witness generation, matrix operations, both sum-checks, commit/MSM, transcript, span, total | The breakdown must sum to the total; any unexplained remainder is listed |
| Recursive | First-step and steady-state step time, full-chain time, constraint counts and witness sizes on both curves | Counts on different curves are reported separately and never merged without explanation |
| PCD | Total proving CPU time, sequential wall time, parallel wall time, root verification time | Leaf and internal-node counts reported together |
| Compression | Compression time, peak RSS, real proof size | Never hidden inside setup or outside recursion |
| Final verification | Warm/cold time, peak RSS, public material and statement size | Includes the K-dependent work actually executed |
| End-to-end | witness + recursive + compression time and total RSS | Setup reported both excluded and amortised |

Serial closed-loop time is `T_online = T_witness + T_recursive + T_compress`. If native folding time is already inside the recursive time, it is not added again. Overlapping intervals in a breakdown are never summed. Parallel wall time is measured directly, never replaced by a sum of phase CPU times.

Also report `T_amortized = T_online + T_family_setup / B` for B reuses, with B = 1, 10 and 100 as transparent scenarios; no single high B is presented as the only result. Sensitivity to verification frequency is analysed separately.

### 7.2 Size metrics

Serialise and measure separately:

1. The private prover checkpoint, including the witness if present.
2. The public uncompressed recursive state or proof.
3. The final compressed proof.
4. The public statement, family/verifier material and SRS.

The main unit is bytes; when KiB is shown, state that it is divided by 1024. Field-element counts are reported as well. A length-K span is K-dependent state. If it is not transmitted explicitly after compression, explain how it is bound and where the cost moves. "One accumulator" never implies "all byte counts are constant in K".

### 7.3 Memory and statistics

- Each trial runs in its own process and measures whole-run peak RSS. Per-phase RSS is reported from separate phase processes or clearly separable measurements; per-phase peaks are never added up.
- Describe the streaming and caching strategy. If all T steps of witness are kept, count them in memory, and never claim constant memory.
- Randomise the execution order of schemes within a configuration. Pair input seeds, and record the warm-up and cold-start boundaries.
- Main tables use median and IQR. Throughput states its denominator as real application steps or leaf tasks, excluding dummies.
- Speedups are computed from paired samples at the same layer and on the same workload, with sample counts and confidence intervals. Cross-backend ratios carry a prominent label.
- Timeouts and OOMs are kept as results. The timeout cap is never used as an exact time in a mean.

## 8. Raw records and result figures

Each run record contains at least:

```text
run_id, timestamp, experiment_id, config_hash
scheme, implementation_commit, dependency_lock_hash, protocol_version, transcript_version
machine_id, rust_version, build_flags, threads, security_profile
workload, input_digest, seed, repetition, warmup
K, T, L, a, mu, nu, d, t, q
m_app, n_app, w_app, m_aug, n_aug, padding, N_total, setup_iterations
setup_ms, witness_ms, recursive_ms, compression_ms
verify_warm_ms, verify_cold_ms, peak_rss_bytes
checkpoint_bytes, public_state_bytes, proof_bytes, statement_bytes, vk_bytes
verification_ok, status, error_message
```

Fields that do not apply are null with an explanation, never 0. Fine-grained breakdowns, matrix non-zero counts and per-curve counts may use nested objects. Configurations and raw records are append-only; a fix produces a new run_id and never overwrites old records.

The paper needs at least six groups of evidence:

1. A functional-scope and end-to-end cost table.
2. K scan: recursive cost, final verification, public state and material size, memory.
3. Direct vs Span: absolute constraint counts and time breakdowns, not just percentage pie charts. **Direct and Span have different security properties (Span makes λ public), and the figure caption must say so** (spec G5).
4. Native high-degree CCS against the real size of the equivalent R1CS.
5. T scan and the crossover points of setup and compression amortisation.
6. Application chain and tree results, showing total work and latency separately.

Figure titles and captions list the fixed parameters, whether setup and compression are included, units, sample counts and the implementation version. If any point in a range fails, show it or explain it in an adjacent table.

## 9. Key risks, fallback paths and forbidden conclusions

| Risk | Handling and fallback | Forbidden |
|---|---|---|
| **B15 field mismatch is harder to fix than estimated** | P3.0 spike picks the cheaper of CycleFold-in-Nova and a Sonobe port. If both overrun, report native-only (G1) results and stop before recursion claims | Folding over the wrong field and claiming recursion works; projecting with `field_switch` |
| Augmented circuit stops converging after changes (F1 regression) | `MAX_SETUP_ITERATIONS` / `MAX_SETUP_CONSTRAINTS` budget plus `CountingCS` pre-check; keep the gadget succinct | Raising the caps to hide divergence |
| Binding between the sparse encoding and the top-level commitment is not closed | Stay on the reference decider (P7a) and say the optimised compression is not done | Folding row/col/val linearly and assuming it is correct |
| High-degree recursive front end does not work | Add a common template embedding; temporarily report native high-degree results only | Calling R1CS-only recursion a full high-degree implementation |
| Sonobe dev branch is unstable (if D1 = Sonobe) | Pin a verified snapshot and record the minimal patches | Switching branches during formal experiments |
| External baseline lacks matching parameters or capabilities | List it in a separate platform group or layer, recorded as N/A | Turning it into a new protocol while still calling it the original scheme |
| Span or final verifier gets slower at large K | Report crossover points and the applicable range | Picking only small-K results or hiding final verification |
| Max-size padding erases the non-uniform gain | Report heterogeneous sizes and padding; consider bucketing as a later design | Excluding the padding cost |
| Out of time | Cut sweep points, parallel scaling and secondary optimisations; fall back to the minimum viable artifact (§3) | Dropping recursion binding, final verification or negative tests |
| Development machine too small (16 GB) | `--release --test-threads=1`; formal runs on the dedicated host | Mixing laptop and server timings |

Example of an allowed conclusion: "Within the stated curves, fixed predicate family and parameter range, index-span reduces a specific recursive overhead, but introduces K-dependent state and terminal cost."

Forbidden conclusions: uniformly better than all non-uniform schemes; a complete zkVM; unproven zero knowledge; unmeasured 1000× per-unit advantages; constant total proving or verification cost for arbitrary K; and, until B15 is closed, any working multi-step recursion.

## 10. Release gates and phase status

Gates:

- G1 (P0–P4): native algebra and folding with different indices are correct over the native field. Only native prototype results may be published.
- G2 (P5–P6): real non-uniform recursive chain and tree, and the high-degree closed loop. Recursive-layer experiments may be published, but reference checks must not be presented as a compressed SNARK.
- G3 (P7–P8): independent final verification, statement binding and fair baselines are complete. Full formal experiments may start.
- G4 (P9–P10): raw data, statistics, reproduction and paper-scope alignment are complete. The research-artifact release bar is met.

Current status (2026-10-07):

| Period | Status | Evidence |
|---|---|---|
| P0 | **Done**, with open blocker B15 | `docs/baseline-status.md`; `cargo test -p nova-snark --release --lib kilonova -- --test-threads=1` → 25 passed, 5 ignored (B15 and the perf harness) |
| P1 | **Done** (OOM check pending a Linux run) | `docs/P1-report.md`; `target/release/kn-run selfcheck` → 16 checks, 0 failed; kilonova suite → 28 passed, 5 ignored |
| P2–P10 | Not started | — |

A status changes only on the commands, results and versions in an acceptance report. Creating or revising this plan does not mean prototype code, tests or experiments have been executed beyond what the P0 reports show.
