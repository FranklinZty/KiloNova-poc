# P3 plan: native-field HFS (transcript v2) with negative tests (2026-11-08)

PLAN.md §3 P3. Acceptance report: `docs/P3-report.md`. Decision memo for the field question: `docs/P3.0-decision.md`.

## Context

B15: the v1 HFS folds R1CS instances over `E::Base`, while the relation lives over `E::Scalar`. The P3.0 spike (`kilonova/spike_p3.rs::hfs_native`) showed that the same protocol run over the relation's native field, generalised to any CCS template, folds the B15 counter-example class for 100 alternating steps with every output accepted by the P2 oracle. P3 turns that prototype into production code.

P3 has **no recursion**. It delivers the native prover, the succinct native verifier, the decider and the tests. P5 moves the recursion layer onto it.

**D1 is not formally confirmed yet.** The memo recommends option (a): Nova fork plus CycleFold. Almost all of P3 is independent of D1. Two choices are not, because they fix the transcript:

1. **The sponge field.** Under (a), the E1 primary circuit verifies the HFS for E1-instances natively over E1::Scalar. The transcript is therefore Poseidon over E1::Scalar. In this code base that sponge is `E::RO2` (`PoseidonRO<E::Scalar>`), with circuit twin `E::RO2Circuit`.
2. **How commitments are absorbed.** E1 points have coordinates in E1::Base, which is non-native in that circuit. They are absorbed as `BN_N_LIMBS = 4` limbs of `BN_LIMB_WIDTH = 64` bits per coordinate, least significant limb first, then the infinity flag. This is the encoding `Commitment::absorb_in_ro2` already uses, and the one CycleFold-style circuits carry.

If the maintainer picks (b), the transcript is re-frozen as v3 for Sonobe's sponge. The algebra, tests and oracle stay.

## Design

The v1 code (`nifs.rs`, `relation.rs`, `span/`, `circuit/`, `RecursiveSNARK`) is not touched apart from documentation, so the v1 recursion suite stays green. The new code goes into a new module, `Nova/src/kilonova/hfs/`.

| File | Content |
|---|---|
| `transcript.rs` (existing) | New `v2` submodule: `HFS_TRANSCRIPT_VERSION = 2`, tags `0x4b4e_4846_5302_000{1,2,3,4}` ("KNHFS" ‖ v2 ‖ n), `absorb_tag`, `absorb_commitment` (4×64-bit limbs per coordinate plus the infinity flag). The v1 constants are unchanged. |
| `hfs/structure.rs` | `CcsTemplate` (t, multisets with repeats, coefficients; `degree`, `validate`), `CcsShape` (m, num_w, num_io, t sparse matrices; layout `z = (w ‖ u ‖ io)`), and `HfsParams` (the family of K shapes plus keys). Keys: witness key `ck` (label `kn-hfs-v2-ck`), one index key of size t·K (label `kn-hfs-v2-index`; the j-th index commitment uses generators jK..(j+1)K), and ι_k[j] = Com(e_k) at offset jK. `HfsParams::digest` is the SHA3-to-field digest (250 bits) of the version, template, shapes and key labels and sizes. A bridge `CcsShape::from_r1cs_shape` takes an existing `R1CSShape`. |
| `hfs/instance.rs` | `Variant` trait with `Direct` (running index = t commitments `comm_M`) and `Span` (running index = λ ∈ F^K, public). `RunningInstance<E, V>{comm_w, index, u, io, r_x, r_y, v[t+1]}`, `RunningWitness{w, lambda}`, `CccsInstance{comm_w, io}`. |
| `hfs/sumcheck.rs` | Generic sum-check prover (tables plus product terms) and verifier. Round i binds bit i of the index (least significant first), so the point is the MLE point in the kn-ccs order with no reversal. Round messages are the evaluations at 0..=deg. |
| `hfs/nifs.rs` | `HfsProof{sc_x, sigma, tau, sc_y, eps, theta}` and `NIFS::{prove, verify}` for μ running and ν incoming inputs (μ + ν ≥ 1). The verifier uses only instances, proof messages and public parameters, never a witness or a matrix. `Challenges{gamma, alpha, r_x, delta, r_y, rho}` come back from both sides, so they can be compared byte for byte. |
| `hfs/decider.rs` | Native decider: lengths, `comm_W = Com(W)`, index opening (Direct: `comm_M[j]` opens to λ; Span: the instance λ equals the witness λ), and the claims v_j = Σ_i λ_i M̃_{i,j}(r_x, r_y), v_t = z̃(r_y). It shares no evaluation code with the prover. |
| `hfs/mod.rs` | `HfsError` with `layer() ∈ {Input, Verifier, Decider}`, so every negative test asserts its detection layer. |

### Protocol (generalises v1 to t, q, d, μ, ν)

Inputs: running `U_i` (i < μ) at points (r_x^i, r_y^i), incoming CCCS `(k_l, comm_W_l, io_l)` (l < ν).

- X phase (s rounds, degree d+1): Σ_x [ Σ_i eq(r_x^i, x) Σ_j γ^{it+j} R_{i,j}(x) + eq(α, x) Σ_l γ^{μt+l} Σ_k c_k Π_{j∈S_k} (M_{k_l,j} z_l)(x) ] = Σ_i Σ_j γ^{it+j} v_{i,j}, where R_{i,j}(x) = Σ_y eq(r_y^i, y) M_{λ_i,j}(x, y). End claims σ_{i,j} = R_{i,j}(r_x′) and τ_{l,j} = (M_{k_l,j} z_l)~(r_x′). End check c_x.
- Y phase (s′ rounds, degree 2): Σ_y [ Σ_i eq(r_y^i, y)(Σ_j δ^{i(t+1)+j} M_{λ_i,j}(r_x′, y) + δ^{i(t+1)+t} z_i(y)) + Σ_l Σ_j δ^{μ(t+1)+lt+j} M_{k_l,j}(r_x′, y) z_l(y) ] equals the same combination of σ, v_{i,t} and τ. End claims ε_i = (M_{λ_i,j}(r_x′, r_y′))_j ‖ z̃_i(r_y′) and θ_l = (M_{k_l,j}(r_x′, r_y′))_j ‖ z̃_l(r_y′). End check c_y.
- Fold with weights ρ^0, ρ^1, …, running first: comm_W, index (comm_M or λ), u, io, and v = Σ ρ^i ε_i + Σ ρ^{μ+l} θ_l, at (r_x′, r_y′). For μ = ν = 1 this is the v1 assignment of γ and δ powers (N7, N8) and the v1 weighting (N6).

The ε and θ claims are deferred. c_y is one linear equation in them, and the prover chooses them after seeing δ and r_y′, so they are not determined by the bare verifier. They enter v* and are checked by the decider. A test constructs exactly this attack and checks that the decider rejects it.

### Fixtures

These go in `kn-ccs` (`gen::wiring_pair`), so the Nova tests and `kn-scenario` share them. Two predicates per template with the same dimensions and different wiring:

- R1CS, k = 0: a = x², a·x = y + 3x − 11. R1CS, k = 1: a = x·(−x), (a + 2)·x = y − 7. These use negative coefficients and full-field values.
- `power(5)`, k = 0: x⁵ = w + 3, (w + x)⁵ = y − x. `power(5)`, k = 1: (2x − 1)⁵ = w, (w − x)⁵ = y + 2x.

`reps` copies chain the output into the next input, which scales m. These are the spike's predicates. The checker code in kn-ccs does not change.

## Acceptance → tests

All tests are in `Nova/src/kilonova/hfs/tests.rs` unless noted. Every positive fold is checked three ways: by the bare verifier (which must produce the same instance as the prover), by the native decider, and by the **independent** P2 oracle `kn_ccs::accs::check_accs`, which gets a Pedersen `commit` closure and its own matrices from `kn_ccs`, plus the comm_M opening.

| PLAN.md P3 criterion | Test(s) |
|---|---|
| ≥ 2 predicates, same dimensions, different matrices, negative coefficients and wrapping products, 100 alternating steps, oracle accepts every step (closes B8/B10) | `test_chain_100_{r1cs,power5}_{direct,span}`: K = 2, step 0 is the (μ, ν) = (0, 1) fold, steps 1..99 are (1, 1) folds alternating k. Every step runs the verifier, the decider and the oracle. |
| B15 class folds over the native field | `test_b15_instance_class_folds_in_v2`: the exact R1CS of `nifs::tests::test_known_issue_b15_scalar_r1cs_not_foldable_over_base`, taken through `from_r1cs_shape`, folds and is accepted. The v1 test stays, re-documented: v1, and so recursion, is still affected until P5. |
| Valid μ/ν combinations | `test_mu_nu_combinations`: (0,1), (0,2), (1,0), (1,1), (1,2), (2,1), (2,2), (3,2) for both variants. Plus the proptest. |
| Mismatched input counts, lengths and degrees rejected explicitly | `test_rejects_mismatched_shapes`: verifier with an extra or a missing running/incoming input; wrong lengths of io, r_x, r_y, v, comm_M and λ; witness length; predicate id ≥ K; round polynomial with the wrong degree; wrong number of rounds; σ/τ/ε/θ counts; μ = ν = 0. `HfsParams::new` rejects mixed templates and dimensions, mixed degrees, empty families and invalid templates. Every case expects `Layer::Input` and a named field. |
| Prover and verifier challenges agree byte for byte | `test_challenges_agree_bytewise` (serialised `Challenges` compared). The chain tests also assert prover output = verifier output. |
| Tampering: sum-check coefficients, evaluations, commitments, field order, transcript tags, running instance; detection layer named | `test_negative_matrix` runs every case, prints a table (case, layer, error) and asserts the expected layer: each X/Y round evaluation, σ, τ, ε, θ (plain tamper → verifier), incoming comm_W and io, running comm_W/comm_M/λ/u/io/r_x/r_y/v, predicate id, transcript tag (each of the 4 tags), absorption order (reversed r_x as in v1's N9, swapped io, swapped σ entries), and a non-canonical field element in the proof bytes (rejected by deserialisation). |
| Deferred claims must not escape the decider | `test_deferred_eps_theta_caught_by_decider`: compensated ε and θ tampering that keeps c_y. The bare verifier accepts, and both the decider and the oracle reject (`Claim`). Also: an inconsistent running instance or incoming commitment that is honestly proved goes through the verifier and is rejected by the decider (`Commitment` / `IndexCommitment`). |
| Fixed bincode test vectors for NIFS, folded instance and transcript (v2) | `test_vectors_v2_{direct,span}_{r1cs,power5}`: deterministic inputs, `expect_file!` against `hfs/vectors/*.txt` (digest, challenges, proof hex, folded instance hex). Plus `test_commitment_absorption_matches_ro2` (limb encoding = `Commitment::absorb_in_ro2`). |
| Fuzz / property tests | `proptest_random_ccs_fold`: random template (R1CS, power(2..6), product(2..4)), K ∈ 1..4, random sizes, μ ∈ 0..3 and ν ∈ 0..3, random satisfiable members (`kn_ccs::gen::random_satisfiable`). Prove, verify, decide, oracle. `proptest_single_tamper_rejected`: one random proof element changed, rejected by the verifier. |
| Decider agrees with the oracle | Every positive test calls both. `test_decider_matches_oracle_on_tamper`: both reject the same tampered outputs. |
| Measurements via kn-run | `kn-scenario hfs template={r1cs,power5} variant={direct,span} steps=T reps=R`: per-step prove, verify, decide and oracle times; bincode bytes of the NIFS proof and the running instance; verification status. Records in `results/raw/p3-hfs.jsonl`, seeds 101/202/303, T ∈ {10, 100}, plus reps = 64. |

Kept green: `cargo test -p nova-snark --release --lib kilonova -- --test-threads=1` (33 passed, 5 ignored before P3), `cargo test -p kn-ccs --release`, `cargo test -p kn-run --release -- --test-threads=1`, fmt, and clippy on the touched crates.

## Out of scope (stated in the report)

- The in-circuit v2 verifier, CycleFold and recursion (P5). The v1 recursion path keeps transcript v1 and B15.
- Predicate selection φ, trace chain and family preprocessing (P4).
- Any security claim. The tests are not a knowledge-soundness proof, and the ε/θ deferral is a design property the decider must enforce.
