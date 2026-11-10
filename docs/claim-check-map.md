# Claim → checker → code map (P0, HFS v1)

Each row is a claim the protocol relies on, who produces it, who checks it, and where. "Gadget" is the in-circuit verifier (`circuit/r1cs.rs::fold_with_r1cs_holographic`, mirrored in `span/circuit/r1cs.rs`). "Decider" is the final relation check, currently `RecursiveSNARK::verify` → `GlobalStructure::is_sat` (needs the witness, G2).

Status legend: ✅ checked, ⏩ deferred to a later layer by design, ❌ gap.

## 1. Per-fold claims (HFS NIFS)

| Claim | Producer | Native checker | Gadget checker | Status |
|---|---|---|---|---|
| Inputs bound: pp_digest, id, U1 (incl. ι′ = comm_M), U2, ι | transcript | `nifs.rs::absorb_inputs` | `fold_with_r1cs_holographic` (tag_input, `self.absorb_in_ro`, `u.absorb_in_ro`, incoming_M) | ✅ (fixed B4) |
| Proof shape: rounds = s_max / s′_max, poly sizes 4 / 3, claims 3/3/4/4 | prover | `NIFS::verify` length checks | fixed by allocation in `AllocatedNIFS::alloc` | ✅ |
| Running instance shape (X, r_x, r_y, v lengths) | — | `NIFS::verify` (new in P0) | fixed by allocation | ✅ |
| X sum-check start `Σ = v0 + γv1 + γ²v2` | `compute_sum_x` | `sumcheck_verify` round 0 | `sum_x_match`, `claim_x_eq_*` | ✅ |
| X round consistency and point = transcript | prover | `sumcheck_verify` (`point != proof.point`) | `rx_point_match_*` | ✅ |
| X end `c_x = eq(r_x,r_x′)·Σγ^jσ_j + γ³·eq(α,r_x′)(τ0τ1−τ2)` | `compute_cx` | `claim_x != cx ⇒ Err` | `claim_x_match_cx` | ✅ |
| σ, τ bound before δ | transcript | `absorb_x_claims` | `tag_x_claims` + absorb | ✅ (fixed B16) |
| Y sum-check start `Σδ^jσ_j + δ³v3 + Σδ^{4+j}τ_j` | `compute_sum_y` | `sumcheck_verify` | `sum_y_match`, `claim_y_eq_*` | ✅ |
| Y round consistency and point | prover | `sumcheck_verify` | `ry_point_match_*` | ✅ |
| Y end `c_y = eq(r_y,r_y′)Σδ^jε_j + Σδ^{4+j}θ_jθ_3` | `compute_cy` | `claim_y != cy ⇒ Err` | `claim_y_match_cy` | ✅ |
| ε, θ bound before ρ | transcript | `absorb_y_claims` | `tag_y_claims` + absorb | ✅ (fixed B16) |
| ε_j = M̃′_j(r′), ε_3 = z̃′(r_y′), θ_j = M̃_j(r′), θ_3 = z̃(r_y′) | prover | **not checked here** | **not checked here** (previously recomputed from witnesses, which broke the fixed point, F1) | ⏩ folded into `v* = ε + ρθ`, checked by the decider |
| Output: `comm_W* = comm_W1 + ρ·comm_W2`, `comm_M* = comm_M1 + ρ·ι`, `u* = u1 + ρ`, `X* = X1 + ρX2`, `r* = (r_x′, r_y′)` | verifier | `FoldedInstance::fold` | `W_fold`, `M_fold_*` (scalar_mul + add), `u_fold`, `x_fold_*`, `v_fold_*` | ✅; native = gadget checked by `test_transcript_native_matches_gadget_*` |
| Incoming predicate id = the circuit's id | host | `predicate_id < K` | `predicate_id_match` | ✅ (v1: host constant; φ missing. v2 recursion: φ enforced in-circuit, P4, §6) |
| **Incoming R1CS holds over its own field** | — | zero-check over `F_B` | zero-check over `F_B` | ❌ **B15**: checked over the wrong field |

## 2. Decider claims (`GlobalStructure::is_sat`, `RecursiveSNARK::verify`)

| Claim | Checker | Code | Status |
|---|---|---|---|
| `comm_W = Com(W; r_W)` | is_sat | `relation.rs` is_sat | ✅ needs W (G2) |
| `comm_M = Com(ck_index, λ)` (Direct) | is_sat | `commit_index_coeffs(λ) == comm_M` | ✅ needs λ. Closes **G1** by design: comm_M is folded homomorphically in-circuit and its opening is a decider check, like comm_W. |
| `v_j = Σλ_i M̃_{i,j}(r_x,r_y)`, `v_3 = z̃(r_y)` | is_sat | `compute_v_from_coeffs` | ✅ O(K·N) |
| Secondary last instance satisfies its R1CS | verify | `shape.is_sat(l_u_secondary)` | ✅ |
| Link hashes match public IO of `l_u_secondary` | verify | `hash_primary`, `hash_secondary` | ✅ |
| Step count, z0, IO lengths | verify | `invalid` check | ✅ |
| Predicate trace | verify | recomputes `update_trace_digest` from the **verifier-supplied** trace | ⚠️ v1 only (historical, B15). The v2 recursion recovers the trace from the proof (P4, §6). |

## 3. Gaps G1–G5 (status after P0)

| # | Gap | Status | Moved to |
|---|---|---|---|
| G1 | In-circuit M not bound to λ | **Closed by design.** The binding is a decider check (above). The old circuit allocated λ as an unconstrained witness, which neither bound it nor was needed. | — |
| G2 | Verifier needs private witnesses; no CompressedSNARK | Open; same as Nova's uncompressed `RecursiveSNARK` | P7 (P7a reference-basis decider) |
| G3 | Predicate trace supplied to the verifier | **Closed for the v2 recursion (P4)**: `ivc::RecursiveSNARK::verify(pp, n, z_0)` takes no schedule and returns the trace hash recovered from the proof; `verify_schedule` only compares it. v1 unchanged (historical). | P6 (trees) |
| G4 | No in-circuit φ; id is a host constant | **Closed for the v2 recursion (P4)**: every primary circuit evaluates the program's φ on its input state and enforces `φ(i, z_i) = k` (`ivc::program`). v1 unchanged (historical). | — |
| G5 | Direct and Span differ in security: Span makes λ public (O(K) public state); its decider has no comm_M check | Documented; Span folds λ in-circuit with field additions only (no group operations) | Ablation interpretation in P8/P9 (PLAN §8, item 3) |

## 4. Field / challenge producer–consumer table

| Item | Producer | Consumers |
|---|---|---|
| γ, α | squeeze after inputs | prover X tables; `compute_sum_x`, `compute_cx`; gadget `gamma_pows`, `eq_alpha` |
| r_x′ (reversed X point) | X rounds | `compute_sigmas/taus`, Y tables, `compute_cx`, output `r_x` |
| δ | squeeze after σ,τ | `compute_sum_y`, `compute_cy`, gadget `delta_pows` |
| r_y′ | Y rounds | `compute_epsilons/thetas`, `compute_cy`, output `r_y` |
| ρ (F_B), ρ_scalar (F_S) | squeeze after ε,θ | all output folds; `FoldedWitness::fold` (W, r_W, λ) |
| `FoldedInstance` fields (7) | `fold`, `from_r1cs_instance_witness`, `default` | NIFS transcript, link hash, is_sat |
| `FoldedWitness` fields (5) | `fold`, `from_r1cs_witness`, `default` | NIFS prover, is_sat (W_proj is only used by the prover now; the circuit no longer takes it) |
| `NIFS` fields (6) | `prove`, `dummy` | `verify`, gadget |
| `KiloNovaAugmentedCircuitInputs` (13 fields after P0: W and λ removed, `w` replaced by `z_at_zero`) | `RecursiveSNARK::{new,prove_step}` | circuit `alloc_witness` |

## 5. HFS v2 (P3, native field, no recursion)

Code: `Nova/src/kilonova/hfs/`. Spec: `docs/protocol-spec.md` §8. "Decider" is `hfs::decide`; "Oracle" is the independent `kn_ccs::accs::check_accs` plus the index opening, run by the tests and by `kn-scenario hfs` on every fold. There is no gadget yet (P5).

| Claim | Producer | Native checker | Layer | Test | Status |
|---|---|---|---|---|---|
| Template, family and dimensions are well formed | setup | `CcsTemplate::new`, `CcsShape::new`, `HfsParams::new` | Input | `test_rejects_mismatched_shapes` | ✅ |
| μ + ν ≥ 1; instance lengths (io, r_x, r_y, v, comm_M / λ); predicate id < K; witness lengths | — | `check_inputs`, prover length checks | Input | `test_rejects_mismatched_shapes` | ✅ |
| Proof shape: s rounds × (deg_x + 1), s′ rounds × 3, σ/τ/ε/θ = μ×t, ν×t, μ×(t+1), ν×(t+1) | prover | `check_proof_shape` | Input | `test_rejects_mismatched_shapes` (incl. a degree-3 proof against a degree-5 template) | ✅ |
| Inputs bound: tag, digest, μ, ν, every running instance (incl. comm_M or λ), every incoming (k, comm_W, io, ι_k) | transcript | `absorb_inputs` | Verifier (challenges change) | `test_negative_matrix` (running/incoming tampering, predicate id, tags, field order) | ✅ |
| X start `Σ_i Σ_j γ^{it+j} v_{i,j}`, round consistency, point | prover | `sumcheck::verify` | Verifier | `test_negative_matrix` (every evaluation of every round), `proptest_single_tamper_rejected` | ✅ |
| X end `c_x` (running row claims σ and the incoming zero-check over τ, for any template) | prover | `NIFS::verify` | Verifier | same | ✅ |
| σ, τ bound before δ | transcript | `absorb_claims(TAG_X_CLAIMS)` | Verifier | tag cases in `test_negative_matrix` | ✅ |
| Y start, rounds, end `c_y` | prover | `sumcheck::verify`, `NIFS::verify` | Verifier | `test_negative_matrix` | ✅ |
| ε, θ bound before ρ | transcript | `absorb_claims(TAG_Y_CLAIMS)` | Verifier / Decider | `test_negative_matrix` (a Y-claims tag mismatch changes only ρ and is caught by the decider) | ✅ |
| ε_i, θ_l are the true evaluations | prover | **not checked by the verifier** (one equation c_y) | ⏩ Decider via `v*` | `test_negative_matrix`: compensated ε and θ tampering passes the verifier and is rejected by the decider and the oracle (`Claim`) | ✅ deferred by design |
| Fold output `comm_W*, index*, u*, io*, (r_x′, r_y′), v*` | verifier | `fold_instances` = prover output | — | every positive test asserts verifier output = prover output and equal challenges (bincode bytes) | ✅ |
| Incoming CCS holds **over its own field** | — | X zero-check over `E::Scalar` | Verifier | `test_b15_instance_class_folds_in_v2`; unsatisfied witness rejected at X round 0 | ✅ (B15 fixed for native folding) |
| `comm_W* = Com(W*)` | decider | `decide` | Decider | inconsistent running/incoming comm_W, honestly proved | ✅ |
| Direct: `comm_M*[j] = Com(ck_index_j, λ*)` | decider | `Direct::check_opening` | Decider | inconsistent running index, honestly proved; tampered λ | ✅ |
| Span: public λ* = witness λ* | decider | `Span::check_opening` | Decider | same | ✅ |
| `v*_j = Σ_k λ*_k M̃_{k,j}(r_x′, r_y′)`, `v*_t = z̃*(r_y′)` | decider | `decide` (bitwise eq, no shared code with the prover) and the oracle | Decider | all positive tests; tampered outputs | ✅ |
| v2 serialisation and transcript frozen | — | `vectors/*.txt` | — | `test_vectors_v2_*`, `test_commitment_absorption_matches_ro2`, `test_noncanonical_field_element_rejected` | ✅ |
| In-circuit v2 verifier, CycleFold for the group operations | gadget | `ivc::gadgets::verify_hfs`, `ivc::cyclefold` | — | §6 below | ✅ P5 |

## 6. Recursive layer (P5, `kilonova::ivc`, HFS v2 + CycleFold)

Spec: `docs/protocol-spec.md` §9. "Gadget" is the primary circuit (`ivc/circuit.rs`, `ivc/gadgets.rs`); "CF" is the CycleFold circuit (`ivc/cyclefold.rs`); "Final" is `ivc::RecursiveSNARK::verify` with its layer (`IvcError::layer`).

| Claim | Producer | Checker | Layer | Test | Status |
|---|---|---|---|---|---|
| HFS v2 fold of (U_i, u_i) verified in-circuit, same transcript as native | prover π | `verify_hfs` (gated by i ≠ 0) | Gadget → propagates to Final/LastIncoming | `test_transcript_native_matches_gadget_v2_{direct,span}` (challenges, folded scalars, tamper → unsatisfied, gate off in the base case) | ✅ |
| Gadget is succinct (instances, proof messages, hints only) | — | code structure; size independent of the matrices | — | `test_primary_circuit_is_succinct`, `test_constraint_breakdown`, setup fixed point converges (3 iterations) | ✅ |
| `comm_W* = comm_W + ρ·comm_W_u`, `comm_M*[j] = comm_M[j] + ρ·ι_{k_prev}[j]` | hints | CF circuit (public inputs built in-circuit from the same limbs) | CF accumulator → Final/CycleFold | `test_cyclefold_circuit` (wrong output, ρ, k), `test_ivc_rejects_unbound_hint`, `test_ivc_rejects_bad_cyclefold_witness` | ✅ |
| ι selected by the folded instance's predicate inside CF (not an input) | CF | one-hot over K | CF | `test_cyclefold_circuit` (wrong k) | ✅ |
| CycleFold instance folded into the accumulator with r binding (pp, U, u, T) | prover T | `AllocatedRelaxedR1CSInstanceN::fold_with_r1cs` = `cf_fold_verify` | Gadget | `test_cyclefold_fold_native_matches_gadget` | ✅ |
| Link: `u_i.io = H(pp, fam, i, z_0, z_i, trace_i, U_i, cfU_i)` unless base (P4: the digest slot is the family digest) | previous circuit | Gadget equality OR is_base | Gadget → Final | `test_ivc_rejects_broken_state_link`, `test_ivc_rejects_repeated_counter` | ✅ |
| Step counter, z_0, z_n, trace, U_n, cfU_n bound at the end | last circuit | `verify`: link hash | Final/LinkHash | `test_ivc_rejects_wrong_claims` (wrong z_0 incl. program register, skipped step, wrong counter) | ✅ |
| Predicate id of each step enters the trace in-circuit (constant of the circuit) | circuit k | Poseidon chain; the trace hash is read from the proof and bound by the link hash (P4) | Final/LinkHash | `test_p4_rejects_forged_ids` (forged trace) | ✅ (N15 closed for v2; G3 closed P4) |
| **φ: the executed predicate is the one the program selects**, `φ(i, z_i) = k` (P4) | circuit k | `PredicateProgram::synthesize_select` + `phi selects k` | Gadget → Final/LastIncoming | `test_p4_rejects_schedule_disagreeing_with_phi` (base, inner, last step), `test_phi_scheduled_program` | ✅ (G4 closed) |
| Expected schedule = recovered trace (optional check) | verifier | `verify_schedule` | Final/Trace | `test_ivc_rejects_wrong_claims` (swapped steps, wrong predicate, wrong last predicate, other length) | ✅ |
| Family digest (stable ids, canonical matrices, selector) bound in pp, every link hash and every HFS transcript | setup | `PredicateFamily`, `HfsParams::from_family`, `setup_pinned` | Setup / Final/LinkHash | `test_p4_rejects_reordered_and_substituted_family` | ✅ |
| Last instance's claimed predicate | proof | CCS of that member (incl. its φ check) | Final/LastIncoming, Input | `test_p4_rejects_forged_ids` | ✅ |
| Folded incoming predicate `k_prev` < K and consistent with ι / e_k / transcript | prover | one-hot in Gadget and CF | Gadget | `test_ivc_rejects_wrong_incoming_predicate` | ✅ |
| Running ACCS satisfied (openings, claims) | — | `hfs::decide` + kn-ccs oracle in tests | Final/Decider | `test_ivc_rejects_tampered_accumulators`; oracle on every verified step of every chain test | ✅ needs W (G2) |
| CycleFold accumulator satisfied | — | `is_sat_relaxed` | Final/CycleFold | `test_ivc_rejects_tampered_accumulators`, `test_ivc_rejects_bad_cyclefold_witness` | ✅ needs W (G2) |
| Last incoming instance satisfies its predicate `l_u.k` | — | `ccs_is_satisfied` + opening | Final/LastIncoming | `test_ivc_rejects_broken_state_link`, `test_ivc_rejects_wrong_incoming_predicate` | ✅ |
| Native degree-5 application rows not lowered | shape builder | `KnShapeCS` (D/E rows) | Setup | `test_ivc_native_pow5_application`, `test_ivc_r1cs_template_rejects_pow5_rows` | ✅ |
| Canonical limb encodings (< p) of E1 points | — | not checked (range-checked only) | — | — | ⚠️ documented limitation (spec §9.7) |
| Trace recovered from the proof; in-circuit φ | — | see the φ / trace rows above | — | — | ✅ P4 (G3, G4 closed for v2) |

## 7. Fixed predicate family and index-span (P4, `kilonova::family`)

Spec: `docs/protocol-spec.md` §10. Layers are `hfs::Layer` (Input, Verifier, Decider) or `IvcLayer`.

| Claim | Checker | Layer | Test | Status |
|---|---|---|---|---|
| Canonical member encoding = kn-ccs `encode` (byte-identical, decodes back, order/duplicate independent) | `family::encode_member` vs `kn_ccs::encode` | — | `family::tests::test_encoding_matches_kn_ccs` | ✅ |
| Family digest binds order, matrices, ids, selector, label, key labels/sizes | `PredicateFamily::new`, `check_digest`, `check_member` | Input | `test_family_digest_binds_order_and_matrices` | ✅ |
| Malformed family (duplicate/empty ids, dims, template, empty) and unknown ids rejected | `PredicateFamily::new`, `position`, `check_member` | Input | `test_family_rejects_unknown_or_duplicate_ids` | ✅ |
| A fold made under another (reordered / substituted) family is rejected | `NIFS::verify` then `decide` | Verifier or Decider | `test_hfs_rejects_other_family` | ✅ |
| Incoming index is e_k; non-unit vectors and out-of-range ids rejected | `NIFS::prove/verify` (Input), `decide` (Decider); gadget one-hot; CF ι selection | Input / Decider / Gadget / CF | `test_non_one_hot_incoming_rejected`, `ivc::tests::test_p4_one_hot_gadget_rejects_forged_bits`, `test_p4_cyclefold_rejects_non_unit_iota` | ✅ |
| Tampered running span rejected | `decide` (SpanIndex / Claim / IndexCommitment), next sum-check, link hash | Decider / Verifier / LinkHash | `test_tampered_span_rejected`, `ivc::tests::test_p4_rejects_tampered_span` | ✅ |
| Explicit folded matrix (step by step) = from λ = weighted evaluation = protocol claims = kn-ccs MLE; λ tracked = witness λ; support reaches the union | `FoldedMatrices`, `weighted_eval`, `decide`, `check_accs` | — | `test_span_paths_agree_k{1,2,4,16}` (Direct and Span) | ✅ |
| Zero-term template embedding preserves semantics for every u | `kn_ccs::pad::embed_zero_terms` + HFS fold with u ≠ 1 | Decider + oracle | `test_zero_term_embedding_folds` | ✅ |
| At least two members change the wiring | sparsity patterns of the application circuits | — | `ivc::tests::test_p4_members_change_wiring` | ✅ |
