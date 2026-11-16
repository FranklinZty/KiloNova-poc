# P7 report: independent final verification and compression (2026-11-14; completed 2026-11-16)

The definition of done was re-run in full at `9fc575e` on 2026-11-16 (§4), and the 8 records missing after the stopped campaign were added the same day (§3.4).

PLAN.md §3 P7. Plan: `docs/P7-plan.md`. Spec: `docs/protocol-spec.md` §12. Claim map: `docs/claim-check-map.md` §9. Branch `p7-compress` (from `origin/p6-pcd` `f5682da`); commits in §8.

**Status: P7a (`reference-basis-decider`) done for chains and trees (a = 2), Direct and Span. P7b (Spark-style sparse holographic evaluation with terminal recursive binding) is not implemented and was not started. Per PLAN.md P7, P7 as a whole is therefore NOT done.** The record campaign was stopped early on the user's request on 2026-11-14; the missing configurations were run on 2026-11-16, so all 36 planned records exist (§3.4). No independent review yet (PLAN.md §2). Nothing here is a performance or security claim; timings come from the 16 GB development laptop (Apple M4, fanless) and are for orientation only.

## 1. What was built

| Item | Code | Notes |
|---|---|---|
| final native fold of the last CCCS | `compress::compress_common`, `verify_terminal` | one more HFS v2 fold (μ = ν = 1) of `(U_n; u_n)`; chain: last step's CCCS, tree: the root's own CCCS; verified by `NIFS::verify` (transcript v2 unchanged), group operations done natively, no CycleFold instance needed |
| index opening | `FinalVariant::lambda_star` | Direct: proof reveals λ* (K elements), verifier recomputes `comm_M*[j] = Com(ck_index_j, λ*)`; Span: λ* public in U* |
| reference-basis matrix evaluation | `compress::reference_basis_eval`, `check_matrix_eval` | every `M̃_{k,j}(r_x*, r_y*)` from the declared family, own eq tables (O(2^s + 2^{s′} + Σ_k nnz)); weighted path chosen (spec §12.6) |
| masked z opening | `z_claim_target`, `check_witness_opening` | IPA (`provider/ipa_pc.rs`, made `pub(crate)`) on E1 against `comm_W*`, key `kn-hfs-v2-ck` extended to 2^{s′}, eq vector **masked to the first num_w entries** (closes a tail-shift of io*, spec §12.2) |
| CycleFold accumulator | `check_cyclefold` | inherited Spartan `RelaxedR1CSSNARK<E2, IPA<E2>>`; panics of the inherited verifier on malformed input are caught and reported as rejections |
| compression transcript | `compress_transcript` | Keccak `kn-compress-v1`, `TAG_COMPRESS = 0x4b4e_4350_0001_0001`, absorbs pp digest and the head digest (sections 1–7); `COMPRESS_VERSION = 1` |
| proof format v1, account | `compress::format` | `KNCP`, 9 sections, canonical (lengths from the material, canonical scalars, valid points, re-encode equality); `account` lists every item with its formula; `Spartan::field_bytes` added to `spartan/snark.rs` for the sub-items |
| public material file | `format::{write_material_chain, write_material_tree, read_material}`, `FinalVerifierKey::from_parts` | `KNVM`: header + canonical member encodings (`family::decode_member`, new, strict); verifier recomputes every digest and checks the pp digest pinned at setup; keys derived from labels |
| CLI, separate processes | `kn-scenario compress-setup | compress-prove | compress-verify` | files `public/{material.knvm, setup.json, proof.kncp}`, `private/checkpoint.bin`; verify derives the expected input from the declared task only |
| refactors (no behaviour change) | `ivc::{chain_pp_digest, chain_link_hash}`, `pcd::{tree_pp_digest, tree_link_hash, expected_root_statement}`, `HfsParams::build_with_ck_len`, accessors | pp digests, link hashes and HFS transcripts unchanged (all P4/P5/P6 tests pass, §4) |

Relations (spec §12.3): statement → `H_link` → `u_n.io[0]` → `io* = io_n + ρ·u_n.io` → `z* = (W* ‖ u* ‖ io*)`; only `W*` is committed (`comm_W*`); the full assignment has no commitment, its public part is evaluated by the verifier; `v*_t = z̃*(r_y*)` is opened (masked IPA); `v*_j = Σ_k λ*_k M̃_{k,j}(r_x*, r_y*)` at the matrix evaluation point `(r_x*, r_y*)` = the final fold's sum-check points. The final application output (z_n or R) reaches the opened claims only through the link hash.

## 2. P7a vs P7b

| | Status |
|---|---|
| P7a reference-basis decider: PCS opening of the z claim, Spartan for the CycleFold relaxed R1CS, verifier evaluates every base matrix, Direct λ revealed and checked against comm_M, chain and tree, Direct and Span | **done** |
| P7b sparse holographic evaluation (Spark-style), terminal recursive binding, top-level homomorphic matrix commitments separate from row/col/val encodings | **not started** |
| P7 overall | **not done** (PLAN.md P7: only P7a accepted) |

## 3. Results

### 3.1 Acceptance → evidence

Tests: `cargo test -p nova-snark --release --lib kilonova::compress -- --test-threads=1` (17 tests, 575 s, peak RSS 1.9 GiB) and `cargo test -p kn-run --release -- --test-threads=1` (the two separate-process tests, 441 s). Every rejection asserts its `CompressLayer`.

| PLAN.md P7 acceptance | Test / record | Detection layer |
|---|---|---|
| checkpoint deleted, chain and tree, separate processes, no undeclared cache | kn-run `compress_cli_checkpoint_deleted_chain` (Direct K = 2, T = 3), `compress_cli_checkpoint_deleted_tree` (Direct a = 2, L = 3): setup, prove and verify are separate `kn-scenario` processes, `private/` is deleted before `compress-verify` (cold and warm), which reports reading only `public/{setup.json, material.knvm, proof.kncp}`; in process: `test_compress_file_roundtrip_checkpoint_deleted`; every campaign record also verified after `rm -r private/` | — |
| verifier input types contain no witness | `test_verifier_inputs_have_no_witness` (section inventory = the declared 9; 32·elements < num_w; no witness-like item; verifier built from the material file alone; two different witnesses give equal-length, different proofs) | — |
| family | `test_compress_rejects_family`: pp digest, family digest in the proof; material with one substituted matrix entry (pinned: rejected at load; unpinned: the proof no longer binds); Span verifier on Direct material; chain proof to a tree verifier | Binding; Material; Binding; Material; Format |
| final output | `test_compress_rejects_statement_and_output`: z_n, trace (chain); R, tree hash, task id (tree) | LinkHash |
| step count / task size | same: n in the file; verifier expects n + 1; other z_0; n + 1 claimed and expected; tree L (same capacity / other capacity); a; root range; expected statement differs | Statement; Statement; Statement; LinkHash; LinkHash / Statement; Statement; Statement; Statement |
| span | `test_compress_rejects_span_and_index`: Span λ in U_n; Span λ* at the terminal check; Direct revealed λ*; Direct comm_M in U_n; swapped λ* | LinkHash; MatrixEval; IndexOpening; LinkHash; IndexOpening |
| evaluation point | `test_compress_rejects_evaluation_point_and_value`: Y/X round messages (they produce r_y*, r_x*); running r_y; moved r_y*, r_x* at the terminal checks | FinalFold; LinkHash; MatrixEval and WitnessOpening |
| evaluation value | same: ε, θ in the final fold; running v; v*_1, v*_t, io* at the terminal checks | FinalFold; LinkHash; MatrixEval, WitnessOpening, WitnessOpening |
| opening | `test_compress_rejects_openings`: IPA â; Spartan eval_W; Spartan proof against another cfU; opening under another head digest; `test_masked_opening_closes_tail_shift` (the unmasked relation accepts a commitment tail shifting io*; the masked check rejects it) | WitnessOpening; CycleFold; CycleFold; WitnessOpening; WitnessOpening |
| recursive output binding | `test_compress_rejects_recursive_output_binding` (chain Direct and tree Span): u_n.io (link-hash output), running u, running comm_W, CycleFold X and comm_E; incoming comm_W and predicate id | LinkHash; FinalFold |
| byte-level tampering, truncation, forged length | `test_compress_rejects_byte_tampering` (chain Direct, tree Direct, chain Span): every header and framing byte plus first/middle/last byte of every section, bits 0 and 7 (79–82 positions × 2 per proof, **all rejected**; e.g. chain Direct: Format 132, LinkHash 10, FinalFold 7, Binding 5, IndexOpening 5, Statement 2, WitnessOpening 2, CycleFold 1); truncations at 0, 3, 10, 15, len/2, len − 1; one extra byte; forged section lengths (shorter, longer with an extra byte, u32::MAX); non-canonical scalar | Format (truncation, extension, lengths, non-canonical); mixed for flips |
| warm vs cold verifier, separate records | `p7-compress.jsonl` `compress-verify mode=cold` / `mode=warm` (§3.3) | — |
| proof bytes item by item = real serialisation; K, N, dims | `test_proof_account_matches_file` (all four fixtures; per section and total; Spartan sub-items = `Dims::spartan_bytes`; K-dependent bytes = 32·K exactly); every verify record carries `details.proof_items` and checks Σ = file length | — |
| coverage | `test_compress_{chain,tree}_{direct,span}`, `test_compress_base_cases` (1-step chain, L = 1 tree with default accumulators) | — |

### 3.2 Proof size, item by item (bytes; identical across seeds)

| Section | chain Direct K = 2 | chain Direct K = 4 | chain Span K = 2 | tree Direct a = 2 (K = 4) | tree Span a = 2 (unit test) | formula |
|---|---|---|---|---|---|---|
| header + framing | 55 | 55 | 55 | 55 | 55 | 10 + 9·5 |
| binding | 64 | 64 | 64 | 64 | 64 | 64 |
| statement | 232 | 232 | 232 | 160 | 160 | chain 8 + 64·arity + 32 (arity 3); tree 96 + 32·arity (arity 2) |
| running U_n | 1,408 | 1,408 | 1,376 | 1,472 | 1,504 | 32·(2 + num_io + s + s′ + t + 1) + Direct 32t / **Span 32K** |
| incoming u_n | 72 | 72 | 72 | 72 | 72 | 40 + 32·num_io |
| cf_instance | 736 | 736 | 320 | 1,088 | 448 | 32·(3 + n_cf) |
| fold_proof | 4,256 | 4,256 | 4,256 | 4,480 | 4,480 | 32·(s(deg_x+1) + 2t + 3s′ + 2(t+1)) |
| index_opening | 64 | **128** | 0 | 128 | 0 | Direct **32K**; Span 0 |
| witness_opening (IPA) | 1,136 | 1,136 | 1,136 | 1,200 | 1,200 | 2·(8 + 32s′) + 32 |
| cf_snark (Spartan) | 4,432 | 4,432 | 3,808 | 4,744 | 4,120 | `Dims::spartan_bytes`, log₂(CycleFold rows) = 13 / 13 / 11 / 14 / 12 |
| **total** | **12,455** | **12,519** | **11,319** | **13,463** | **12,103** | |

Parameters: chain s = s′ = 17 (m = 121,284, num_w = 121,278), t = 3, deg_x = 3, n_cf = 20 (Direct) / 7 (Span); tree s = s′ = 18 (m = 227,923), n_cf = 31 (Direct) / 11 (Span). **Dependence:** K enters only through λ (32·K bytes: Direct revealed λ*, Span running λ); N and the matrix dimensions only logarithmically through s, s′ (sum-check rounds, IPA rounds); the CycleFold size (which grows weakly with K and with a) through n_cf and log₂ of its rows. K = 16 (record of 2026-11-16): the chain Direct proof is **12,903 bytes**, exactly the formula value 12,455 + 32·14 (s, s′ and the padded CycleFold size are unchanged from K = 2/4). Tree Span a = 2: 12,103 bytes. Comparison (§7.2): the uncompressed checkpoints are 8,288,768 B (chain Direct), 5,762,368 B (chain Span), 15,627,400 B (tree Direct root).

### 3.3 Times and memory (`results/raw/p7-compress.jsonl`, `--threads 1`, every record `status = success`)

| Config (seeds) | setup | recursion (T = 16 / L = 8) | compressor key | **compress** | **verify-final warm** (median of 3) | **verify-final cold** | of which material + keys / verify | peak RSS prove / verify | material (vk) |
|---|---|---|---|---|---|---|---|---|---|
| chain Direct K = 2 (101, 202, 303) | 26–41 s | 26–36 s | 22–26 s | **29–35 s** | **1.12–1.45 s** | **27–31 s** | 26–29 s / 1.1–1.3 s | 0.91–0.99 / 0.55 GiB | 266 MB |
| tree Direct a = 2, L = 8 (101, 202, 303) | 43–57 s | 30–32 s | 45–50 s | **57 s** | **3.25–3.27 s** | **53–55 s** | 49–52 s / 3.3–3.4 s | 1.12–1.17 / 0.74–0.79 GiB | 261 MB |
| chain Direct K = 4 (101) | 28–39 s | 38 s | 28 s | **37 s** | **1.56 s** | **35 s** | 34 s / 1.5 s | 1.47 / 0.88 GiB | 531 MB |
| chain Span K = 2 (101) | 20–22 s | 24 s | 36 s | **37 s** | **1.06 s** | ~~46 s~~ **not usable** (see note) | 45 s / 1.2 s | 0.80 / 0.57 GiB | 214 MB |
| tree Span a = 2, L = 8 (101) | 27 s | 28 s | 50 s | **58 s** | **3.08 s** | **61 s** | 57 s / 3.3 s | 0.74 / 0.55 GiB | 169 MB |
| chain Direct K = 16 (101) | 67 s | 43 s | 38 s | **40 s** | **3.19 s** (reps 3.06, 3.19, 4.84 s) | **96 s** | 91 s / 4.8 s | 2.59 / 2.27 GiB (setup 3.04 GiB) | 2.12 GB |

- "compress" = `compression_ms`: final fold + IPA prove (2^{s′} vector) + Spartan prove, single-threaded; "compressor key" (witness key at 2^{s′} generators by hash-to-curve, Spartan setup) is reported separately in `details.compressor_key_ms` and is a one-off per parameter set.
- **Cold** = from opening the files to the verdict: material decode (canonical member parsing), member/family/CycleFold/pp digests, key derivation from labels (the 2^{s′}-generator hash-to-curve dominates), Spartan vk, then verify-final. **Warm** = verify-final only with the key and proof preloaded: final fold verify, Direct index re-commitment, reference-basis evaluation over every member (K·nnz), IPA verify (MSM over 2^{s′}), Spartan verify.
- **K dependence (measured, Direct chains):** warm 1.12–1.45 s (K = 2, N_total = 5.52 M) → 1.56 s (K = 4, N_total = 11.04 M) → 3.19 s (K = 16, N_total = 44.2 M); cold 27–31 s → 35 s → 96 s; material 266 MB → 531 MB → 2.12 GB; proof 12,455 → 12,519 → 12,903 B (32 B per member) (linear in Σ_k nnz, 48 B per entry). The reference-basis evaluation is the only K-linear term of verify-final; IPA and Spartan are K-independent here.
- **Note — not usable for timing:** the record chain Span K = 2 seed 101 `mode=cold` (`20261114T093145Z-a109d5d3`) ran while the process was paused by the user with SIGSTOP for about 30 s; its wall-clock `verify_cold_ms` (46.3 s) is inflated (CPU time unaffected). Its verdict (accepted) is valid.
- **The 2026-11-16 records** (tree Span a = 2, chain Direct K = 16) were taken at `9fc575e` with no source or documentation edits. 7 of the 8 carry `implementation_dirty = true` only because kn-run's dirty check (`git status --porcelain --untracked-files=no`) sees the tracked `results/raw/p7-compress.jsonl` itself, modified by the first new record. This is a harness artifact, not a code difference.
- One 2026-11-14 record carries `implementation_dirty = true`: chain Direct K = 2 seed 101 `compress-prove` (`20261114T085345Z-87583ac1`), because documentation was being edited while it ran (no code change). Records before it are at `453e403`, records after it at `e40b421`; the two commits differ only in documentation.

### 3.4 Records: planned vs present

The campaign script is `results/raw/logs/p7-compress-campaign.sh`, its log is `results/raw/logs/p7-compress-campaign.log`. **The user stopped the campaign** on 2026-11-14 while `compress-setup` for the tree Span a = 2 configuration was running. That job wrote no record; its log stub `20261114T093300Z-bcfd22a8.{out,err}` is kept. The two remaining configurations were run on 2026-11-16 with the same script body (only their two `cfg` lines), at `9fc575e`.

| Configuration | Planned records | Present |
|---|---|---|
| chain Direct K = 2, T = 16, seeds 101/202/303 | setup + 3 × (prove, cold, warm) = 10 | **10** |
| tree Direct a = 2, L = 8, seeds 101/202/303 | 10 | **10** |
| chain Direct K = 4, T = 16, seed 101 | 4 | **4** |
| chain Span K = 2, T = 16, seed 101 | 4 | **4** (cold record not usable for timing, §3.3) |
| tree Span a = 2, L = 8, seed 101 | 4 | **4** (2026-11-16) |
| chain Direct K = 16, T = 16, seed 101 | 4 | **4** (2026-11-16) |

Total: **36 of 36** planned records, all `status = success`, every verify record `verification_ok = true`. Chains are covered for K ∈ {2, 4, 16} and trees for a = 2 in both variants. One record (chain Span K = 2 seed 101 cold) is not usable for timing (§3.3).

## 4. Suite results

Full definition of done re-run at `9fc575e` on 2026-11-16 (development laptop, `--release`, `--test-threads=1`). The user had stopped an earlier run on 2026-11-14.

| Command | Result |
|---|---|
| `cargo fmt --all --check` | clean |
| clippy (`-p kn-ccs -p kn-run -p nova-snark --release --all-targets -- -W clippy::all -A clippy::len_without_is_empty`) | clean (only the pre-existing workspace `resolver` warning) |
| `cargo test -p nova-snark --release --lib kilonova -- --test-threads=1` | **126 passed, 0 failed, 10 ignored** (3,451 s). P6 baseline 109 / 10, plus the 17 `kilonova::compress` tests. |
| `cargo test -p nova-snark --release --lib nova::tests::test_ -- --test-threads=1` | 11 passed, 2 ignored |
| `cargo test -p kn-ccs --release` | 21 passed |
| `cargo test -p kn-run --release -- --test-threads=1` | 12 passed (10 + 2 `compress_cli_*` separate-process tests) |

The P4/P5/P6 tests that pin pp digests, link hashes and transcripts are part of the kilonova suite and all pass, so the refactors outside `compress/` (§1) changed no digest, hash or transcript. The 10 ignored long tests (P4/P5 long chains, P6 64-leaf trees) were not re-run on this branch; they passed on `p6-pcd`, and the values they depend on are pinned by tests that passed here.

## 5. Known limitations and open items

- **P7b not done.** The final verifier is the reference basis: O(K·N) in the index, with the whole family as public material (266–531 MB here, linear in K). Spark-style sparse evaluation, terminal recursive binding and separate row/col/val encodings are not implemented.
- **Verifier time.** The IPA verifier and Spartan-with-IPA verifier are linear in their vector sizes (2^{s′} and CycleFold rows): the proofs are succinct in size, not in verifier time (as in inherited Nova). Cold verification is dominated by deriving keys from labels (hash-to-curve of 2^{s′} generators) and by decoding and hashing the material, not by verify-final itself.
- **Direct reveals λ\*** at the end (K elements). This is not a zero-knowledge claim, which is not made anyway.
- **No soundness proof.** The composition (final native fold, masked IPA, Spartan, link hash) is argued in spec §12, not proven. The tail-shift test shows why the mask is necessary; it does not show that the mask suffices.
- **Pallas/Vesta only.** The compression code is concrete for Pallas/Vesta (`compress::{E1, E2}`); the recursion layers stay generic.
- **Inherited-code changes.** Visibility only in `provider/ipa_pc.rs`; one added accessor (`field_bytes`) in `spartan/snark.rs`. The inherited Spartan verifier asserts on some malformed proofs, so `check_cyclefold` catches the panic and turns it into a rejection.
- **Test time.** The compress module adds 575 s to the kilonova suite (the byte-flip test performs about 490 verifications).
- **Unchanged.** v1 code, the B18 fix, the HFS v2 transcript and vectors, and the IVC and PCD versions are untouched. `kn-ccs` stays independent.
- **Review.** No independent review yet.

## 6. Definition-of-done commands

```bash
cargo fmt --all --check
cargo clippy -p kn-ccs -p kn-run -p nova-snark --release --all-targets -- -W clippy::all -A clippy::len_without_is_empty
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1
cargo test -p nova-snark --release --lib nova::tests::test_ -- --test-threads=1
cargo test -p kn-ccs --release
cargo test -p kn-run --release -- --test-threads=1
# separate processes (example)
target/release/kn-scenario compress-setup kind=chain variant=direct K=2 dir=D
target/release/kn-scenario compress-prove kind=chain variant=direct K=2 T=16 seed=101 dir=D
rm -r D/private
target/release/kn-scenario compress-verify kind=chain variant=direct K=2 T=16 seed=101 dir=D mode=cold
```

## 7. Entry conditions for later periods

- **P7b:** sparse holographic evaluation of `M_{λ*}` at `(r_x*, r_y*)`. It replaces `check_matrix_eval`, the only K-linear verifier step, and makes the material independent of the family's matrices. It needs a binding between the homomorphic `comm_M` and the row/col/val encodings, which cannot be folded linearly without a proof (PLAN §9).
- **K = 16 record and tree Span record:** rerun only on request: `cfg chain-direct-k16 …` and `cfg tree-span-a2 …` in the campaign script.
- **P8/P9:** compression and final verification are now measurable layers (`compression_ms`, `verify_warm_ms`, `verify_cold_ms`, `proof_bytes`). Formal runs belong on the Linux host.

## 8. Commits

| Commit | Content |
|---|---|
| `65129a9` | plan (`docs/P7-plan.md`) |
| `f5a32ef` | compress module, proof format, material file, tests (WIP checkpoint after an external-disk disconnect) |
| `e284eaa` | compress tests pass; `kn-scenario compress-*`; separate-process CLI tests; `pcd::expected_root_statement`; spec §12 |
| `453e403` | clippy fixes; claim map §9; campaign script |
| `e40b421` | PLAN, README and AGENTS status; baseline B6/G2; `versions.lock`; `configs [compress]` |
| follow-up | records `results/raw/p7-compress.jsonl` (28) and logs; this report |
