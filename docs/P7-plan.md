# P7 plan: independent final verification and compression (2026-11-14)

PLAN.md §3 P7. Base: `origin/p6-pcd` at `f5682da` (P0–P6 and the B18 fix). Work branch `p7-compress`. Acceptance report: `docs/P7-report.md`. Spec: new `docs/protocol-spec.md` §12.

Entry conditions (P4 report §7, P5 report §6, P6 report §8, baseline G2/B6): `RecursiveSNARK::verify` and `NodeProof::verify_root` read the final witnesses (the running ACCS witness `(W, λ)`, the CycleFold relaxed-R1CS witness `(W, E)` and the last incoming CCCS witness), and the decider uses the weighted O(Σ_k nnz) index path.

**Scope.** P7a (`reference-basis-decider`) is the mandatory milestone. P7b (Spark-style sparse holographic evaluation with terminal recursive binding) is a stretch goal, attempted only after P7a is accepted; if it is not finished P7 is reported as **P7a only, P7 not done** (PLAN.md P7, last acceptance item).

## 1. What the final verifier must establish

For a chain (`ivc`, IVC version 2) after n steps the uncompressed verifier checks five things on `(U_n, W_n)`, `(cfU_n, cfW_n)`, `(u_n, w_n)`: Input, LinkHash `u_n.io[0] = H_link(pp, hfs, n, z_0, z_n, trace, U_n, cfU_n)`, Decider on `(U_n, W_n)`, CycleFold `is_sat_relaxed(cfU_n, cfW_n)`, LastIncoming (CCS of member `u_n.k` on `(w_n, 1, io)` and `comm_W` opens). For a tree root (`pcd`, PCD version 1) the same with Statement (range `[0, a^d)`) and RootIncoming. Three of these read witnesses.

## 2. Design (P7a, reference basis)

### 2.1 The last incoming instance: fold it natively (Nova-style)

The final CCCS `u_n` (chain: last step; tree: the root's own CCCS) is **folded into the running ACCS by one more HFS v2 fold with μ = ν = 1**, done by the compressor and verified natively by `verify-final` with `hfs::NIFS::verify` (same protocol, same transcript v2 and tags as every recursive step; nothing new is introduced into the HFS). The group operations of that fold (`comm_W* = comm_W_n + ρ·comm_W_u`, Direct `comm_M*[j] = comm_M_n[j] + ρ·ι_k[j]`) are computed by the native verifier itself, so no CycleFold instance is needed for it. Result `U* = (comm_W*, index*, u*, io*, r_x*, r_y*, v*)`. Knowledge soundness of the HFS (not proven, spec §8.7) reduces "U_n and u_n satisfied" to "U* satisfied". This avoids a separate Spartan-for-CCS proof (alternative rejected: one more SNARK and a second matrix-evaluation path).

### 2.2 Terminal checks on U* (reference basis)

- **Index.** Span: λ* is public in U*. Direct: the proof **reveals λ*** (K field elements) and the verifier checks `comm_M*[j] = Com(ck_index_j, λ*)` for every j < t (t MSMs of size K; the "virtual commitment" computation).
- **Matrix evaluation (reference basis).** The verifier evaluates `M̃_{k,j}(r_x*, r_y*)` for **every** base matrix (k < K, j < t), from the declared family matrices, with eq tables of size 2^s and 2^{s′} (written in the compress module, independent of the prover's tables and of `hfs::decide`), and checks `Σ_k λ*_k M̃_{k,j} = v*_j`. Cost O(2^s + 2^{s′} + Σ_k nnz(M_k)), i.e. O(K·N) in the index; succinct in the witness. Index path decision: the **weighted (reference-basis) path**, not the explicit union. For a one-shot verifier the explicit folded matrix must first be built from λ* (a sorted merge over all K members, Σ_k nnz work and union-size memory), so it never beats the weighted path asymptotically; it only helps when a folded matrix is cached, which a per-proof λ* rules out. The measured K dependence is reported.
- **Witness opening (z claim).** `z* = (W* ‖ u* ‖ io*)`, so `v*_t = z̃*(r_y*) = Σ_{i<num_w} W*_i·eq(i, r_y*) + u*·eq(num_w, r_y*) + Σ_j io*_j·eq(num_w+1+j, r_y*)` (index bit i ↔ r_y*[i], as in the decider). The verifier computes the public part and the target `y = v*_t − u*·eq(num_w, r_y*) − Σ_j io*_j·eq(num_w+1+j, r_y*)`, and an **IPA (Bulletproofs-style inner-product argument from `provider/ipa_pc.rs`) over Pedersen on E1** proves knowledge of `a ∈ F^{2^{s′}}` with `Com(ck_ext, a) = comm_W*` and `⟨a, b⟩ = y` for the **masked** vector `b_i = eq(i, r_y*)` for i < num_w, `b_i = 0` otherwise. `ck_ext` = the witness key `kn-hfs-v2-ck` extended to 2^{s′} generators (same SHAKE stream, so its prefix is the HFS key). Why masked: with the standard IPA evaluation (`b = eq(r_y*, ·)` over all 2^{s′} entries) a prover could commit to a vector with non-zero entries beyond num_w (generators that the HFS key does not have) and use them to shift the u/io entries of z* (for example the last circuit's link-hash output). With the mask, entries beyond num_w never enter any evaluation; the relation becomes "comm_W* = Com(W*) + Com(tail), CCS on (W* ‖ u* ‖ io*)", in which the tail is inert.
- **CycleFold accumulator.** `cfU_n` (relaxed R1CS over E2 = Vesta, key `kn-ivc-cf-ck` / `kn-pcd-cf-ck`) is proven by the inherited **Spartan `RelaxedR1CSSNARK<E2, ipa_pc::EvaluationEngine<E2>>`** (`spartan/snark.rs`, non-preprocessing: the verifier evaluates the fixed CycleFold matrices itself). The CycleFold shape is already padded (power-of-two, regular) and its key has exactly that many generators (B18 fix untouched).
- **Link hash and statement** are recomputed natively from the public statement, `U_n` and `cfU_n` (unchanged native twins).

### 2.3 Compression transcript (new, own tags)

The HFS final fold uses transcript v2 unchanged. The IPA runs on a new Keccak transcript `E1::TE::new(b"kn-compress-v1")` that first absorbs `TAG_COMPRESS = 0x4b4e_4350_0001_0001` ("KNCP" v1), the pp digest and the **header digest** (SHA3-256 of the canonical bytes of every proof section before the openings, truncated to 250 bits), then the IPA's own messages. The masked vector b is a function of r_y* and num_w, both fixed by the header digest and the pp digest. Spartan keeps its own inherited transcript (`"RelaxedR1CSSNARK"`, vk digest, cfU); cfU is bound to the statement through the link hash. `COMPRESS_VERSION = 1`.

### 2.4 Relations (spec)

statement (chain `(n, z_0, z_n, trace)`; tree `(task_id, L, a, lo, hi, R, h)`) → `H_link` → `u_n.io[0]` → `io* = io_n + ρ·u_n.io` → `z* = (W* ‖ u* ‖ io*)` → `v*_t = z̃*(r_y*)` (witness opening, against `comm_W*`, which commits to W* only; the full assignment has **no** commitment of its own, its public part is evaluated by the verifier) and `v*_j = Σ_k λ*_k M̃_{k,j}(r_x*, r_y*)` (matrix evaluation point `(r_x*, r_y*)` = the final fold's sum-check points, values v*_j = ε_n,j + ρ·θ_j from the final fold).

## 3. Terminal-check map (the layers of `verify-final`)

| # | Check | Reads | Layer (`CompressLayer`) |
|---|---|---|---|
| 0 | file: magic, version, kind, variant, section tags, lengths, canonical field/point encodings, no trailing bytes, re-encoding equals the input | proof bytes | **Format** |
| 1 | pp digest and family digest in the proof = the verifier's (recomputed from the material, pinned by the setup digest) | proof header, material | **Binding** (material mismatch at load: **Material**) |
| 2 | statement: chain n ≥ 1, |z_0| = |z_n| = arity, expected (n, z_0); tree 1 ≤ L < 2^32, lo = 0, hi = a^d, a = material a, optional expected statement | statement | **Statement** |
| 3 | `u_n.k < K`, `u_n.io[0] = H_link(…)` | statement, U_n, cfU_n, u_n | **LinkHash** (k out of range: Format) |
| 4 | final HFS fold `NIFS::verify(U_n, u_n, π_fold) → U*` | U_n, u_n, π_fold | **FinalFold** |
| 5 | Direct: `comm_M*[j] = Com(ck_index_j, λ*)` | λ*, U* | **IndexOpening** |
| 6 | `Σ_k λ*_k M̃_{k,j}(r_x*, r_y*) = v*_j`, j < t | family matrices, λ*, U* | **MatrixEval** |
| 7 | IPA: `comm_W*` opens to a with `⟨a, b_mask(r_y*)⟩ = y(v*_t, u*, io*)` | U*, IPA proof | **WitnessOpening** |
| 8 | Spartan on cfU_n | cfU_n, Spartan proof | **CycleFold** |

## 4. Proof format v1 (canonical)

```text
"KNCP" | version u16 = 1 | kind u8 (1 chain, 2 tree) | variant u8 (0 direct, 1 span) | sections u16 = 9
section = tag u8 | len u32 LE | payload            (tags 1..9, in this order, all present)
1 BINDING        pp_digest, family_digest
2 STATEMENT      chain: n u64, z_0[arity], z_n[arity], trace | tree: task_id, L u64, a u64, lo u64, hi u64, R[arity], h
3 RUNNING        U_n: comm_W, index (Direct comm_M[t] | Span λ[K]), u, io[num_io], r_x[s], r_y[s'], v[t+1]
4 INCOMING       u_n: k u64, comm_W, io[num_io]
5 CF_INSTANCE    cfU_n: comm_W, comm_E, u, X[n_cf]
6 FOLD_PROOF     sc_x[s][deg_x+1], σ[t], τ[t], sc_y[s'][3], ε[t+1], θ[t+1]
7 INDEX_OPENING  Direct: λ*[K] | Span: empty
8 WITNESS_OPEN   IPA (bincode legacy): L[s'] (u64 len + 32 B each), R[s'], a_hat
9 CF_SNARK       Spartan RelaxedR1CSSNARK (bincode legacy), sub-items accounted field by field
```

Field elements: 32 B canonical little-endian repr (non-canonical rejected). Points: 32 B compressed (halo2curves encoding, invalid points rejected). Integers u64/u32/u16 little endian. No length prefixes inside our own sections (all lengths follow from the public material); sections 8–9 are the inherited serde objects. The verifier rejects any byte string whose decoding does not re-encode to exactly the same bytes, so the encoding is canonical. Size formula: `10 + 9·5 + Σ items`, items listed in the report with their dependence on K (Span section 3, Direct section 7: 32·K bytes), N (s, s′ = log₂ of the padded dimensions) and the CycleFold size (Spartan: logarithmic in the CycleFold shape).

**Public material file** (`material.knvm`, also canonical): kind, variant, template, arity, (tree: a, K_leaf), family label, ids, selector, **the canonical member encodings** (`family::encode_member`, the kn-ccs encoding), the padded CycleFold R1CS shape (bincode). The verifier recomputes member digests, the family digest, the CycleFold shape digest and the pp digest, compares the pp digest with the one recorded at setup, then derives the keys from their labels (`kn-hfs-v2-ck` extended to 2^{s′}, `kn-hfs-v2-index`, ι, the CycleFold key, the IPA key, the Spartan vk). Transparent setup: no trusted SRS; the "SRS" record is the key labels, sizes and the SHA-256 of the derived generators.

## 5. Interfaces

- `kilonova::compress`: `CompressorKey::{chain, tree}` (prover keys), `compress_chain`, `compress_tree`, `FinalMaterial::{of_chain, of_tree, encode, decode}`, `FinalVerifierKey::from_material`, `verify_final_chain`, `verify_final_tree(_statement)`, `ProofFile::{encode, decode, account}`, `CompressError::layer`.
- `kn-scenario compress-setup | compress-prove | compress-verify` (`kind=chain|tree`, `variant`, `K`/`a`, `T`/`L`, `seed`, `dir`, `mode=cold|warm`): setup writes `dir/public/{material.knvm, setup.json}`; prove re-runs the deterministic setup, checks the pp digest against `setup.json`, writes `dir/private/checkpoint.bin` and `dir/public/proof.kncp`; verify reads **only** the material, the proof and the pinned digest, and derives the expected public input from the declared task (chain: K, T, seed → z_0; tree: L, seed → root statement).

## 6. Acceptance → test map

| PLAN.md P7 acceptance | Test / record |
|---|---|
| checkpoint deleted, chain and tree, separate processes | kn-run integration test `compress_cli_checkpoint_deleted` (setup, prove, `rm -r private/`, verify in separate `kn-scenario` processes; chain Direct K=2 and tree Direct a=2); in-process file round trip `test_compress_*_file_roundtrip` |
| verifier inputs contain no witness | `test_verifier_inputs_have_no_witness` (proof item inventory, field-element count independent of num_w, verifier built from material bytes only) |
| each binding rejects, with layer | `test_compress_rejects_*` (family, final output, step count / L, span, evaluation point, evaluation value, opening, recursive output binding), byte flips over every section, truncation, forged lengths |
| warm vs cold | `results/raw/p7-compress.jsonl` records `compress-verify mode=warm` / `mode=cold` |
| proof bytes item by item = file length; K, N, dims | `test_proof_account_matches_file` (Direct and Span, chain and tree); records for chains K ∈ {2, 4, 16} and trees a = 2 |
| records | `p7-compress.jsonl`: compress time, verify warm/cold, bytes per item, peak RSS; seeds 101/202/303 for chain Direct K = 2 and tree Direct a = 2 |
| coverage | chain and tree, Direct and Span: `test_compress_chain_{direct,span}`, `test_compress_tree_{direct,span}` |

## 7. Not in P7a

P7b (Spark-style sparse evaluation, terminal recursive binding, separate row/col/val encodings). No zero knowledge. No new soundness proof: the IPA and Spartan are the inherited instantiations; the masked-evaluation argument and the final native fold are argued in the spec, not proven.
