# KiloNova HFS: Protocol Specification (frozen at P0)

Status: v1 frozen 2026-10-05; **v2 added 2026-11-08 (P3)**. Two transcript versions coexist:

- **HFS v1** (`transcript.rs::HFS_TRANSCRIPT_VERSION = 1`), §§1–7: the R1CS-specialised HFS over `E::Base` used by `RecursiveSNARK`, the augmented circuits and their gadgets. Still affected by B15.
- **HFS v2** (`transcript.rs::v2::HFS_TRANSCRIPT_VERSION = 2`), §8: the native-field HFS of P3 (`Nova/src/kilonova/hfs/`), generic over the CCS template and over (μ, ν), with no recursion yet. P5 moves the recursion path onto v2.

## 0. Normative declaration

`Nova/src/kilonova/` is the **normative** implementation. Where this document and the paper disagree, this document describes what the code does. The "paper" column records the correspondence. Changing anything in §§2–5 requires bumping the version and the test vectors.

Roles of the three crates (also in `AGENTS.md`):

| Crate | Role | Use in P1+ |
|---|---|---|
| `Nova/src/kilonova/` | Normative R1CS-specialised HFS plus two-curve recursion. `span/` is the Span ablation. | Mainline |
| `folding/` | Generic CCS algebra PoC (arkworks/BLS12-381). Not serialisable, no statement binding, no negative tests, known defects B11/B12/B14. | Reference oracle for P2/P3 only |
| `NIFS-circuit/` | Independent cost model behind the old paper's constraint-count figures. Does not use `kilonova/`. | Historical; its numbers must not be reused (PLAN §P9) |

## 1. Objects

Notation: `E` is the curve whose group commits the witness. `F_S = E::Scalar` is the R1CS field and `F_B = E::Base` is the field the HFS currently runs in (see §7, B15). K is the family size. Rows use `s = log₂(num_cons)` bits; columns use `s' = log₂(next_pow2(num_vars + 1 + num_io))` bits; both take the maximum over the family.

- `GlobalStructure`: padded shapes of the K predicates, `s_max`, `s_prime_max`, `num_vars_max`, `num_io = 2`, `ck_index[3]` (Pedersen keys of size K), and per predicate `comm_M[j] = Com(ck_index[j], e_id)`.
- Running ACCS instance `FoldedInstance{comm_W, comm_M[3], u, X[2], r_x[s_max], r_y[s'_max], v[4]}`, with witness `FoldedWitness{W, W_proj, r_W, λ (F_S), λ_proj (F_B)}`.
- Relation (`GlobalStructure::is_sat`):
  `comm_W = Com(ck, W; r_W)`; `comm_M[j] = Com(ck_index[j], λ)`; `v[j] = Σ_i λ_i·M̃_{i,j}(r_x, r_y)` for j = 0,1,2; and `v[3] = z̃(r_y)` with `z = (W_proj ‖ u ‖ X)`.
- Incoming CCCS: an R1CS instance `(comm_W, X)` with `u = 1` and predicate id k (index `e_k`).
- Span variant: `FoldedInstance` stores `lambda: Vec<F_B>` publicly instead of `comm_M`, and `is_sat` has no comm_M check.

## 2. Notation freeze (N1–N16)

| # | Item | Decision |
|---|---|---|
| N1 | ACCS fields | Equivalent mapping: `v` is a flat vector of t+1 = 4 entries; `v[0..3] = v_j` and `v[3] = v_z`. |
| N2 | `z` layout | `(w ‖ u ‖ io)`, as in the paper. Frozen. (`folding/` uses `(u ‖ io ‖ w)` and must be adapted in P2.) |
| N3 | σ / τ | Code `sigmas` ≡ paper σ′ (running side, with eq); code `taus` ≡ paper σ (new side). Code names kept. |
| N4 | ε / θ | Code `epsilons = (θ′_0..2, ε′)` (running) and code `thetas = (θ_0..2, ε)` (new), both packed as t+1 entries. Code names kept. |
| N5 | Fold challenge | Code ρ ≡ paper η. |
| N6 | Which side carries weight 1 | **Resolved: equivalent convention, not a bug.** The running side has weight 1 and the new side weight ρ: `u* = u′ + ρ`. The folded relation is linear (evaluation claims only), and the R1CS zero-check is applied only to the fresh instance with its constant 1 fixed in `z_new`, so the output relation is the same under either weighting. The base case (`from_r1cs_instance_witness`, `u = 1`, `r = 0`) is consistent with it. |
| N7 | γ powers | **Resolved: internally consistent.** `compute_sum_x`, `sumcheck_prove_x` and `compute_cx` all use γ⁰, γ¹, γ² for the running matrix terms and γ³ = γ^t for the zero-check. The paper revision uses γ^{t+1}. Any distinct powers give a sound batch, so this is a rescaling. |
| N8 | δ powers | **Resolved: internally consistent.** δ⁰..δ² for the running matrices, δ³ for the running z, δ⁴..δ⁶ for the new matrices, identical in `compute_sum_y`, `sumcheck_prove_y` and `compute_cy`. |
| N9 | Variable order | Sum-check round i binds bit `s−1−i` of r_x (`canonical_point` reverses the point). The gadget applies the same `.rev()`. Matrix/MLE index bits are little-endian (`bits_le`). |
| N10 | Degree bounds | X rounds: degree 3 (= d+1), evaluations at {0,1,2,3}. Y rounds: degree 2, evaluations at {0,1,2}. |
| N11 | Generality | t=3, d=2, μ=ν=1 are hard-coded (`configs/common.toml`). Generalised in P3. |
| N12 | ι encoding | **Intentional deviation.** ι = Pedersen commitment to the K-vector λ (index-span), not `PCS.Com(M̃_j)`. The two are not equivalent. The paper notes the trade-off is "not an asymptotic improvement for every parameter choice". |
| N13 | Predicate selection φ | Not implemented. The predicate id is a host constant bound to a witness (G4, moved to P4). |
| N14 | Link hash | `H(pp_digest, i, z0, zi, U, r_i, trace_digest)`. Compared with the paper it adds i, z0 and the trace and omits idx; idx is bound only through `trace_digest`, which is not collision resistant (N15). Closed in P4. |
| N15 | Trace digest | `(t + id + 1)² + id + 1`, an algebraic map, **not collision resistant**. To be replaced by a Poseidon chain in P4. |
| N16 | ZK | Not provided; see §4. |

## 3. Transcript (HFS v1)

The oracle is Poseidon (`E::RO` natively, `E::ROCircuit` in-circuit), absorbing `F_B` elements. Every squeeze returns `NUM_CHALLENGE_BITS = 128` bits and re-seeds the sponge with the full hash. Commitments are absorbed as `(x, y, is_infinity ∈ {0,1})`. R1CS public inputs are absorbed as `scalar_as_base(X_i)`; they are 250-bit hashes, so the representation is unique.

Direct variant (`nifs.rs::absorb_inputs`, `absorb_x_claims`, `absorb_y_claims`; gadget `circuit/r1cs.rs::fold_with_r1cs_holographic`):

```text
absorb TAG_INPUT = 0x4b4e_4846_5301_0001
absorb pp_digest (as F_B)
absorb predicate_id
absorb U1: comm_W, comm_M[0..3] (= iota'), u, X[0..2], r_x[..], r_y[..], v[0..4]
absorb U2: comm_W, X[0..2]
absorb iota = comm_M of predicate_id, [0..3]
gamma <- squeeze ; alpha[i] <- squeeze  (i = 0..s_max)
for each X round: absorb 4 evals ; r_i <- squeeze
absorb TAG_X_CLAIMS = 0x4b4e_4846_5301_0003 ; absorb sigma[0..3], tau[0..3]
delta <- squeeze
for each Y round: absorb 3 evals ; r_i <- squeeze
absorb TAG_Y_CLAIMS = 0x4b4e_4846_5301_0004 ; absorb epsilon[0..4], theta[0..4]
rho <- squeeze            (rho_scalar = base_as_scalar(rho), 128 bits fit both fields)
```

Span variant (`span/nifs.rs`): the same sequence with `TAG_INPUT_SPAN = 0x4b4e_4846_5301_0002`. U1 is absorbed as `comm_W, lambda[0..K], u, X, r_x, r_y, v`, and there is no separate ι absorption, because the incoming index `e_k` is fixed by `predicate_id`.

`NIFS::dummy` (the base-case proof) follows the same sequence with `U1 = FoldedInstance::default`, all-zero polynomials and all-zero claims.

Changes from the pre-P0 transcript: U1 (B4) and the helper claims (B16) are now bound, and domain tags were added. The checks are `test_nifs_rejects_substituted_running_instance`, `test_nifs_rho_binds_y_claims` and `test_transcript_native_matches_gadget_{direct,span}`; the last one compares the gadget's output hash, which depends on ρ, against the native fold.

**In-circuit verifier contract (succinctness).** The gadget uses only U1, U2, ι, the NIFS proof messages and `pp_digest`. It never takes the running or incoming witness, and never recomputes σ/τ/ε/θ. Those are prover messages bound by the transcript: σ and τ are checked through `c_x` and the Y sum-check, and ε and θ are folded into `v* = ε + ρ·θ` and checked by the decider. The only witness-derived input is `z_at_zero` in the secondary base case (`v[3] = z̃(0) = z[0]`), and it is bound through the link hash and the decider's comm_W check.

## 4. Non-ZK boundary

The KiloNova PoC **does not provide zero knowledge**. NIFS proofs reveal evaluations of z̃ at random points (`epsilons[3]`, `thetas[3]`) in the clear, sum-check messages are not masked, and `RecursiveSNARK` carries the full folded witnesses. The paper's Theorem 3 likewise keeps only perfect completeness and computational knowledge soundness, for constant depth. Any README text claiming zero knowledge is wrong and was removed at P0.

## 5. Setup and digest construction order

1. Start from a guess for the secondary structure (`dummy_shape`, 16×16).
2. Loop: synthesise K primary augmented shapes against the guess, build `structure_primary` with `new_for_setup` (dimensions, index commitments and `matrix_at_zero` only), dry-run the secondary circuit with `CountingCS` (abort with `SetupDidNotConverge` above `MAX_SETUP_CONSTRAINTS = 2^20`), synthesise the secondary shape, and compare `structure_signature` (dimensions only). Abort after `MAX_SETUP_ITERATIONS = 12`.
3. **Exactness check:** re-synthesise the primary shapes against the final secondary structure and require identical matrices. This settles the P0 question of whether a dimensions-only signature is enough. It is now, because the circuits depend on the other structure only through its dimensions, K and `matrix_at_zero`, and the check enforces it anyway.
4. Build the final `GlobalStructure`s with runtime tables.
5. Size the commitment keys from the **padded** shapes and `num_vars_max` (B17).
6. Assemble `PublicParams`, then `digest = H(serialise(pp))`, where the `digest` field is `#[serde(skip)]`, so nothing is self-referential.

## 6. Security parameters (frozen)

| Parameter | Value | Source |
|---|---|---|
| Curves | Pallas / Vesta | `test_utils.rs`, tests |
| Challenge bits | 128 | `constants.rs::NUM_CHALLENGE_BITS` |
| Hash bits (link hash) | 250 | `NUM_HASH_BITS` |
| Non-native limbs | 4 × 64 | `BN_N_LIMBS`, `BN_LIMB_WIDTH` |
| Witness commitment | Pedersen (`provider::pedersen`) | |
| Compression PCS (single-step test only) | IPA (`ipa_pc::EvaluationEngine`) | `test_utils.rs` |
| Sum-check soundness per fold | rough bound ≤ (4·s_max + 3·s'_max + O(1)) / 2^128 (Schwartz–Zippel over 128-bit challenges, union bound) | not a proof; to be restated once B15 is fixed |

## 7. Known deviations and open blockers

- **B15 (critical; fixed for native folding in v2, open for recursion).** The v1 HFS for an instance whose R1CS lives over `F_S` is computed over `F_B` on `field_switch`-projected values. `field_switch` is not a homomorphism. Negative coefficients (`−1 ↦ q−1 mod p ≠ −1`) and wrapping products break satisfaction, so honest multi-step proving fails. Evidence: `nifs::tests::test_known_issue_b15_scalar_r1cs_not_foldable_over_base`, and `prove_step` returns `UnSat("HFS zero-check failed … (B15)")`. The fix belongs to P3/P5: run the HFS over `F_S`, and either delegate the group operations to the other curve (CycleFold-style) or verify the field operations non-natively. **P3 status:** HFS v2 (§8) folds over `F_S`; `hfs::tests::test_b15_instance_class_folds_in_v2` folds the exact counter-example shape. The v1 evidence test is kept, because `RecursiveSNARK` still runs v1 (P5).
- G2 to G4 (`docs/claim-check-map.md`) are moved to P4, P6 and P7.

## 8. HFS v2: native-field HFS (P3, 2026-11-08)

Code: `Nova/src/kilonova/hfs/` (`structure.rs`, `instance.rs`, `sumcheck.rs`, `nifs.rs`, `decider.rs`), tags and the commitment encoding in `transcript.rs::v2`. Test vectors: `Nova/src/kilonova/hfs/vectors/v2_{direct,span}_{r1cs,power5}.txt`, checked by `hfs::tests::test_vectors_v2_*`. Changing anything in this section requires a new version (v3) and new vectors.

### 8.1 D1 (decided (a), 2026-11-09)

D1 was decided (a) by the maintainer on 2026-11-09. v2 follows option (a) of `docs/P3.0-decision.md` (Nova fork plus CycleFold): the HFS for instances committed on `E` (E1 = Pallas in the tests) is verified natively in a circuit over `E::Scalar`. Therefore:

- the sponge is **Poseidon over `E::Scalar`**, i.e. `E::RO2` (`PoseidonRO<E::Scalar>`, U24 constants, `Strength::Standard`), with circuit twin `E::RO2Circuit`;
- commitments (points with coordinates in `E::Base`, non-native in that circuit) are absorbed as **`BN_N_LIMBS = 4` limbs of `BN_LIMB_WIDTH = 64` bits per coordinate**, least significant limb first: `x[0..4], y[0..4], is_infinity ∈ {0, 1}` (9 elements). This is the encoding of `Commitment::absorb_in_ro2`; `test_commitment_absorption_matches_ro2` pins the equality.

If (b) (Sonobe) is chosen, the transcript is re-frozen as v3.

### 8.2 Objects

| Object | Content |
|---|---|
| `CcsTemplate` | t matrices, q multisets `S_k` (repeats allowed), coefficients `c_k`; degree d = max |S_k|. Relation `Σ_k c_k ∘_{j∈S_k} (M_j z) = 0`. Reference description: `kn_ccs::Template`. |
| `CcsShape` | m rows, `n = num_w + 1 + num_io` columns, `z = (w ‖ u ‖ io)` (N2), t sparse matrices. `From<&R1CSShape>` bridges the v1 shapes. |
| `HfsParams` | K shapes with one template and identical dimensions; `s = max(1, ⌈log₂ m⌉)`, `s′ = max(1, ⌈log₂ n⌉)`; witness key `ck` (label `kn-hfs-v2-ck`, size max(num_w, 1)); index key `ck_index` (label `kn-hfs-v2-index`, size t·K), with `comm_M[j](λ) = Com(ck_index, 0^{jK} ‖ λ)` (disjoint generators per j); `ι_k[j] = comm_M[j](e_k)`; `digest` = SHA3-256 → 250-bit field element of bincode(version = 2, template, shapes, key labels and sizes). |
| Running ACCS `RunningInstance<V>` | `comm_W, index, u, io[num_io], r_x[s], r_y[s′], v[t+1]`; index = `comm_M[0..t]` (Direct) or `λ[0..K]` (Span). Witness `(W[num_w], λ[K])`. |
| Relation (`decide`) | `comm_W = Com(ck, W)` (no blinding; non-ZK); Direct: `comm_M[j] = comm_M[j](λ)`; Span: public λ = witness λ; `v_j = Σ_k λ_k M̃_{k,j}(r_x, r_y)` (j < t); `v_t = z̃(r_y)` with `z = (W ‖ u ‖ io)`. |
| Incoming CCCS `IncomingInstance` | `k, comm_W, io`; witness `W`; u = 1, λ = e_k. Relation: the CCS of predicate k holds on `(W ‖ 1 ‖ io)`. |

### 8.3 Notation changes against v1

| # | v1 | v2 |
|---|---|---|
| N9 | round i binds bit s−1−i; the point is reversed (`canonical_point`) | **round i binds bit i** (least significant first); the point is the MLE point directly, in kn-ccs order. No reversal. |
| N10 | X degree 3, Y degree 2 | X degree `deg_x = max(d + 1, 2)`, Y degree 2; messages are the evaluations at `0..=deg` |
| N11 | t = 3, d = 2, μ = ν = 1 | any template; μ running and ν incoming inputs, μ + ν ≥ 1 |
| fold field | `E::Base` on `field_switch`-projected values (B15) | `E::Scalar`; no projection anywhere |
| N6–N8 | γ⁰..γ² / γ³; δ⁰..δ⁶; weights (1, ρ) | generalised below; identical for μ = ν = 1 |

### 8.4 Protocol

Inputs: running `U_i` (i < μ), incoming `(k_l, comm_W_l, io_l)` (l < ν). `R_{i,j}(x) = Σ_y eq(r_y^i, y) M_{λ_i,j}(x, y)` with `M_{λ,j} = Σ_k λ_k M_{k,j}`.

- **X phase** (s rounds, degree deg_x). Claim `Σ_i Σ_j γ^{it+j} v_{i,j}`. Polynomial `Σ_i eq(r_x^i, x) Σ_j γ^{it+j} R_{i,j}(x) + eq(α, x) Σ_l γ^{μt+l} Σ_k c_k Π_{j∈S_k} (M_{k_l,j} z_l)(x)`. Prover messages after the rounds: `σ_{i,j} = R_{i,j}(r_x′)`, `τ_{l,j} = (M_{k_l,j} z_l)~(r_x′)`. End check `c_x = Σ_i eq(r_x^i, r_x′) Σ_j γ^{it+j} σ_{i,j} + eq(α, r_x′) Σ_l γ^{μt+l} Σ_k c_k Π_{j∈S_k} τ_{l,j}`.
- **Y phase** (s′ rounds, degree 2). Claim `Σ_i (Σ_j δ^{i(t+1)+j} σ_{i,j} + δ^{i(t+1)+t} v_{i,t}) + Σ_l Σ_j δ^{μ(t+1)+lt+j} τ_{l,j}`. Polynomial `Σ_i eq(r_y^i, y)(Σ_j δ^{i(t+1)+j} M_{λ_i,j}(r_x′, y) + δ^{i(t+1)+t} z_i(y)) + Σ_l Σ_j δ^{μ(t+1)+lt+j} M_{k_l,j}(r_x′, y) z_l(y)`. Messages: `ε_i = (M̃_{λ_i,j}(r_x′, r_y′))_{j<t} ‖ z̃_i(r_y′)`, `θ_l = (M̃_{k_l,j}(r_x′, r_y′))_{j<t} ‖ z̃_l(r_y′)`. End check `c_y = Σ_i eq(r_y^i, r_y′)(Σ_{j≤t} δ^{i(t+1)+j} ε_{i,j}) + Σ_l Σ_j δ^{μ(t+1)+lt+j} θ_{l,j} θ_{l,t}`.
- **Fold** with weights `w = (ρ⁰, ρ¹, …)`, running inputs first, then incoming: `comm_W* = Σ w·comm_W`; index `Σ w·comm_M` with `ι_{k_l}` (Direct) or `Σ w·λ` with `e_{k_l}` (Span); `u* = Σ w·u` (u = 1 incoming); `io* = Σ w·io`; `(r_x*, r_y*) = (r_x′, r_y′)`; `v* = Σ_i w_i ε_i + Σ_l w_{μ+l} θ_l`. Witness: `W* = Σ w·W`, `λ* = Σ w·λ`.

**Deferred claims.** ε and θ are checked only through `c_y`, one equation, and the prover chooses them after seeing δ and r_y′. They are deferred to the decider through `v*`. Also ρ is the last challenge: a prover/verifier disagreement that affects only ρ (for example the Y-claims tag) yields a valid fold under a different ρ, so it is detected only when the prover's witness meets the verifier's instance in the decider. `test_negative_matrix` exercises both.

**Verifier contract (succinctness).** `NIFS::verify` reads only `HfsParams` (digest, dimensions, template, ι), the instances and the proof. It never reads a witness or a matrix: the matrices enter only through σ, τ, ε, θ.

### 8.5 Transcript (HFS v2)

Sponge `E::RO2`. Every squeeze returns `NUM_CHALLENGE_BITS = 128` bits and re-seeds the sponge with the full hash (`PoseidonRO::squeeze`). Field elements of `E::Scalar` are absorbed natively. Integers (μ, ν, k) are absorbed as `E::Scalar::from(u64)`.

```text
absorb TAG_INPUT            Direct 0x4b4e_4846_5302_0001 | Span 0x4b4e_4846_5302_0002
absorb digest
absorb mu, nu
for each running U_i (i = 0..mu):
    absorb comm_W (9 elements, §8.1)
    Direct: absorb comm_M[0..t] (9 elements each)   | Span: absorb lambda[0..K]
    absorb u, io[0..num_io], r_x[0..s], r_y[0..s'], v[0..t+1]
for each incoming l (l = 0..nu):
    absorb k_l, comm_W (9 elements), io[0..num_io]
    Direct: absorb iota_{k_l}[0..t] (9 elements each) | Span: nothing (e_k is fixed by k)
gamma <- squeeze ; alpha[i] <- squeeze (i = 0..s)
X rounds i = 0..s: absorb p_i(0..=deg_x) ; r_x'[i] <- squeeze
absorb TAG_X_CLAIMS = 0x4b4e_4846_5302_0003 ; absorb sigma[i][j] (i-major), tau[l][j] (l-major)
delta <- squeeze
Y rounds i = 0..s': absorb p_i(0), p_i(1), p_i(2) ; r_y'[i] <- squeeze
absorb TAG_Y_CLAIMS = 0x4b4e_4846_5302_0004 ; absorb eps[i][0..=t], theta[l][0..=t]
rho <- squeeze
```

Proof (`HfsProof`, bincode legacy in the vectors): `sc_x[s][deg_x+1], sigma[μ][t], tau[ν][t], sc_y[s′][3], eps[μ][t+1], theta[ν][t+1]`. Its size depends on (s, s′, t, d, μ, ν), not on K. The verifier rejects any other shape before touching the transcript (`HfsError::Shape`, layer Input). Deserialisation rejects non-canonical field elements (`test_noncanonical_field_element_rejected`).

### 8.6 Detection layers

`HfsError::layer()`: **Input** (template, family, counts and lengths, predicate id; checked before any transcript work); **Verifier** (`SumcheckRound{phase, round}`, `EndCheck{phase}`); **Decider** (`Commitment`, `IndexCommitment{j}`, `SpanIndex`, `Claim{index}`). The P3 report (`docs/P3-report.md` §4) lists which tamper cases land on which layer.

### 8.7 Security parameters (v2)

As §6, with: fold field `E::Scalar`; sponge Poseidon over `E::Scalar`; commitment absorption 4 × 64-bit limbs per coordinate. A rough Schwartz–Zippel count for one fold is ≤ (deg_x·s + 2·s′ + O(q·d)) / 2^128 plus the batching terms. This is not a proof, and the knowledge-soundness argument for the generalised (t, q, d, μ, ν) protocol is not written (PLAN.md §2: tests are not a security proof).
