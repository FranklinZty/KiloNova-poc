# P6 report: multi-predecessor PCD and workload closure (2026-11-14)

PLAN.md §3 P6 and §6 W4. Plan: `docs/P6-plan.md`. Spec: `docs/protocol-spec.md` §11. Claim map: `docs/claim-check-map.md` §8. Branch `p6-pcd` (from `origin/master` `9273d60`, which contains P0–P5, P4 and the B18 fix); commits in §7.

**Status: P6 done for a = 2 (mandatory) and for the stretch arities a = 4 (Direct) and a = 8 (Span only), with the limitations in §5.** a = 8 with the Direct variant does **not** fit: its merge circuit has 1,712,219 rows, above `MAX_SETUP_CONSTRAINTS = 2^20`, and setup rejects it (layer Setup); the cap was not raised. No independent review yet (PLAN.md §2). Nothing here is a performance or security claim; all timings come from the 16 GB development laptop (Apple M4, fanless, 10 cores) and are for orientation only.

## 1. Goal and scope

Goal: tree-shaped execution over a fixed predicate family, with leaf task and position, predecessor order, sub-task ranges, node outputs and the root claim bound in-circuit, and a root verifier that needs nothing beyond the root statement.

| Item | Code | Notes |
|---|---|---|
| μ/ν-generic HFS v2 verifier gadget | `pcd/gadgets.rs::verify_hfs_multi` | transcript §8.5 for any μ ≥ 1, ν (γ/δ powers, weights ρ^0..ρ^{μ+ν−1}); for μ = ν = 1 exactly the P5 gadget's size (`verify_hfs` untouched) |
| multi-input CycleFold circuit | `pcd/cyclefold.rs::CycleFoldCircuitN` | `W_out = Σ ρ^i W_i`, Direct `M_out[j] = Σ ρ^i M_i[j] + Σ ρ^{μ+l} ι_{k_l}[j]` by Horner's rule with the 128-bit ρ only; ι selected in-circuit; for μ = ν = 1 the P5 circuit's size and input order |
| tree CycleFold accumulators | `pcd/gadgets.rs::CfAcc`, `pcd/cyclefold.rs::cf_fold_{relaxed,fresh}_prove` | a − 1 relaxed–relaxed folds (`E ← E + r(T + rE′)`) + 1 fresh fold per merge; u and X as 4 × 64-bit limbs (u grows by a 128-bit factor per level otherwise) |
| node circuits | `pcd/circuit.rs` | leaf (one per leaf predicate), merge (a children), dummy; one public output, the node link hash |
| parameters, prover, verifier | `pcd/mod.rs` | `TreeParams::setup` (family `[leaf/0, leaf/1, merge, dummy]`, fixed point, padded shapes, keys from padded shapes, pp digest), `NodeProof::{prove_leaf, prove_dummy, prove_node}` (native pre-checks at layer Input; hidden test hooks), `verify_root`, `verify_statement`, `check_incoming`; `prove_tree` (sequential, depth-first) and `prove_tree_levels` (level-parallel) |
| task-tree generator | `pcd/task.rs` | `TreeTask::generate(seed, L, K_leaf)`, `layout(a)` with the dummy rule, `expected_result`; `TreeParams::root_statement` |
| breakdown | `pcd/breakdown.rs` | per-component counts of every member (disjoint, sum to CountingCS); `ivc::breakdown::BreakdownCS` gained a pluggable categorizer (default unchanged) |
| kn-run | `kn-scenario tree` | `results/raw/p6-tree.jsonl` (main, single-threaded), `results/raw/p6-tree-parallel.jsonl` (measured parallel latency, labelled) |

### Design (from the plan)

- **Node semantics.** A node over `[lo, hi)` proves `r = Σ_{p ∈ [lo,hi) ∩ [0,L)} β^p F_{k_p}(x_p)` (β = 7) and the tree hash h of its subtree. Leaf: `([p, p+1), β^p F_k(x_p), H(TAG_LEAF, p, k, x_p))` with k a circuit constant and `p < L` enforced. Merge: contiguous, ordered, equal-width children; `r = Σ r_c`; `h = H(TAG_NODE, lo, hi, h_0..h_{a−1})`. Dummy: `([lo, hi), 0, H(TAG_DUMMY, lo, hi))` with `lo ≥ L` enforced.
- **Base case.** Leaves and dummies; they contain no verifier and output the default accumulators. There is no `is_base` gate: the base case is a separate family member (the non-uniform family pads the 9.3k-row leaf circuits to the merge circuit's size).
- **Dummy rule.** Capacity `a^d` with the minimal d; a node with `lo ≥ L` whose parent has `lo < L` is one dummy proof covering the whole padding subtree, so padding costs at most `(a − 1)·d` dummy proofs.
- **Binding.** Every node's link hash covers `(pp_digest, family_digest, task_id, L, lo, hi, r, h, U, cfU)`; a merge recomputes each child's link hash **with its own task context**, so a subtree of another task cannot be folded. Ranges are enforced in-circuit (not only hashed).
- **Root statement** `(task_id, L, a, [0, a^d), R, h)`, returned by `verify_root(pp)` without any tree structure; `root_statement(task)` computes the expected one from the task alone.

### μ/ν ↔ a (written into every configuration and record)

| Configuration | a | HFS μ | HFS ν | CycleFold accumulators |
|---|---|---|---|---|
| chain step (P4/P5) | 1 | 1 | 1 | 1 running + 1 fresh |
| tree leaf / dummy | 0 | 0 | 0 | none (defaults) |
| tree merge | a | **a** | **a** | a running (a − 1 relaxed folds) + 1 fresh |

So μ + ν = 2a, never a. `configs/common.toml [pcd]`, every `p6-tree` record (`a`, `mu`, `nu` fields and `details.mu_nu_mapping`) and spec §11.5 carry it.

## 2. Configuration

Pallas (E1) / Vesta (E2), Pedersen, Poseidon (`Strength::Standard`), challenges 128 bits, hashes 250 bits, non-ZK, uncompressed. Leaf predicates: P4 chain members 0 `(x, y) ↦ (x³ + y + 5, x)` and 1 `(x² − y + 7, y + 1)` (different wiring); K = 4 family members. Task: `TreeTask::generate(seed, L, 2)` (positions 0, 1 use both predicates, then seeded). Rust 1.92.0, `--release`, `--test-threads=1`; kn-run records `--threads 1` unless labelled parallel.

## 3. Results

### 3.1 Acceptance (PLAN.md P6) → evidence

Tests: `cargo test -p nova-snark --release --lib kilonova::pcd -- --test-threads=1` (plus the ignored long tests, run explicitly). Every rejection asserts its detection layer (`pcd::TreeLayer`). "Circuit" = the tampered node's own CCCS is unsatisfied (`NodeProof::check_incoming`, layer RootIncoming); in a full tree it propagates through the parents' in-circuit HFS verifiers to the root's CCCS.

| PLAN.md P6 acceptance | Test / record | Detection layer |
|---|---|---|
| a = 2 tree PCD, root verify without host structure, dummy rule | `test_tree_a2_small` (L = 4 no padding, L = 5 two dummies, L = 6 one dummy; sequential and level drivers; kn-ccs oracle on the root accumulator), `test_tree_layout_dummy_rule` (8 (L, a) cases) | — |
| 64 fixed real leaf tasks, same R for every supported a | `test_tree_64_leaves_all_arities` (`#[ignore]`; Direct a = 2, 4 and Span a = 8 give the same R; Direct a = 8 rejected at Setup), `test_tree_64_leaves_a2` (`#[ignore]`); records §3.3: **`result_digest` is identical across a ∈ {2, 4, 8} and both variants for each seed** (seed 101: `c065db6b…`, 202: `a942cbcf…`, 303: `ee40f9e8…`) | — |
| padding and internal-node work reported separately | every record: `details.work.{leaf, merge (internal-node work), dummy (padding work)}`, `details.layout.{merges, dummies, merges_if_unpadded}`; L = 50 record (§3.4) | — |
| duplicate leaves | `test_tree_rejects_duplicate_leaf` (leaf 0 twice, leaf 1 twice, a subtree twice) | Input (API); Circuit; root: RootIncoming (range still `[0, 4)`) or Statement (range broken) + Circuit |
| missing leaves | `test_tree_rejects_missing_leaf` (gap; a dummy at position 3 < L; a valid tree of the first 3 leaves claimed for the 4-leaf task) | Input; Circuit → RootIncoming; Statement |
| cross-task splicing | `test_tree_rejects_cross_task_splice` (a subtree of task B under task A; a leaf of B under A; B's valid tree against A's statement) | Input; Circuit → RootIncoming; Statement |
| illegal order | `test_tree_rejects_swapped_children` (swapped leaves; swapped subtrees at the root; swapped leaves one level below the root) | Input; Circuit; Statement + Circuit |
| forged predecessors | `test_tree_rejects_forged_predecessor` (forged child result, forged child proof = garbage witness under the child's io, swapped child accumulators; at a leaf pair and at the root; tampered root result / tree hash / range / running witness / CycleFold witness / running instance) | Circuit → RootIncoming; LinkHash, Statement, Decider, CycleFold |
| same input ≠ same position | `test_tree_same_input_different_positions` (identical leaves at positions 1 and 2 verify; their leaf hashes differ) + the duplicate test | — |
| sequential CPU vs parallel latency | main records `--threads 1` (§3.3); the computed critical path is labelled in every record; measured level-parallel latency only in the separate `p6-tree-parallel` record (§3.5) | — |
| μ/ν ↔ a in every config and record | `configs/common.toml [pcd]`; record fields `a`, `mu`, `nu` and `details.mu_nu_mapping`; spec §11.5 | — |
| no regressions; succinct HFS verifier | kilonova suite and long chains (§3.6); `ivc::tests::test_primary_circuit_is_succinct` (unchanged) and new `test_merge_circuit_breakdown_and_succinctness` (merge size independent of the leaf members' wiring, below the family nnz) | — |
| native vs gadget transcript for μ = 2 (and the other new paths) | `test_transcript_native_matches_gadget_multi_{direct,span}` ((μ, ν) ∈ {(1,1), (2,2), (2,1), (4,4)}, R1CS and power-5; tampered round message, σ, τ, Y round, incoming id and running order rejected; gate off accepted), `test_multi_gadget_matches_p5_gadget_size`, `test_cyclefold_multi_circuit`, `test_cf_tree_fold_native_matches_gadget` | — |
| records `results/raw/p6-tree.jsonl` | 13 records (Direct a = 2 × 3 seeds, Direct a = 4 × 3, Span a = 8 × 3, Span a = 2/4 seed 101, Direct a = 2 L = 50, Direct a = 8 setup failure) + `p6-tree-parallel.jsonl` (1) | — |

Where the tampered node is the root and its native statement range is already impossible (a swapped or duplicated subtree gives `[2, 2)` or `[2, 4)`), the root verifier stops at Statement before reaching the CCCS; the tests assert both that and the unsatisfied root circuit. Swapping two *leaf* accumulators is a no-op (both are the default), so that tamper is exercised at the root.

### 3.2 Sizes (CountingCS breakdown; identical across seeds)

Merge circuit per component (`pcd::breakdown`, disjoint, sums to the CountingCS total; Direct a = 2 is the main configuration):

| Component | Direct a = 2 | Direct a = 4 | Span a = 8 |
|---|---|---|---|
| HFS sum-check rounds | 39,204 | 43,560 | 43,560 |
| HFS transcript (statement absorption, γ, α, δ, ρ) | 29,614 | 41,869 | 45,754 |
| HFS claims (powers, eq, end checks, scalar folds) | 280 | 564 | 1,092 |
| HFS index (ι selection / λ fold) | 54 | 108 | 64 |
| children's link hashes | 16,144 | 44,720 | 64,576 |
| hashing (output link hash, node tree hash) | 9,149 | 12,257 | 9,149 |
| non-native hints (limbs, range checks, one-hots) | 3,116 | 4,176 | 4,706 |
| CycleFold (a − 1 relaxed folds + 1 fresh fold, on-curve checks) | **130,357** | **430,193** | **586,837** |
| ranges, control | 5 | 9 | 17 |
| **merge total** | **227,923** | **577,456** | **755,755** |
| leaf / dummy members | 9,297 (9,296) / 9,259 | — | — |
| padded m (s = s′) | 227,923 (18) | 577,456 (20) | 755,755 (20) |
| CycleFold circuit raw → padded rows (inputs) | 14,911 → 16,384 (31) | 34,525 → 65,536 (53) | 18,553 → 32,768 (35) |
| setup iterations | 2 | 3 | 2 |

Direct a = 8 merge: **1,712,219 rows > `MAX_SETUP_CONSTRAINTS` = 1,048,576**; setup rejects it (layer Setup, record `20261113T161447Z-278665ee`). Span a = 2: 134,450 rows; Span a = 4: 279,085. The leaf circuit (application 3–4 rows, position range checks, β^p, leaf hash) is dominated by its output link hash (9,149 rows), which hashes the default accumulators; every member is padded to the merge circuit's size. The bignat folds of the CycleFold public inputs dominate the merge circuit (≈ 2.1k rows per input per fold, a folds of n_cf inputs; 57 %, 74 % and 78 % of the merge circuit), the P5 optimisation target now multiplied by a.

### 3.3 64-leaf trees (`results/raw/p6-tree.jsonl`, `--threads 1`, seeds 101/202/303; every record `status = success`, `verification_ok = true`)

| Config | merges / leaves / dummies | setup | leaf proof (median) | merge proof (median) | **sequential prove** (Σ node times) | of which internal-node work | computed critical path | root verify | peak RSS | root proof bytes |
|---|---|---|---|---|---|---|---|---|---|---|
| Direct a = 2 | 63 / 64 / 0 | 43–48 s | 0.18 s | 4.18–4.35 s | **275–289 s** | 264–278 s | 29–32 s | 6.6–7.0 s | 1.16–1.17 GiB | 15.6 MB |
| Direct a = 4 | 21 / 64 / 0 | 111–116 s | 0.23 s | 22.8–23.0 s | **511–514 s** | 497–499 s | 78 s | 13.0–13.1 s | 2.32–2.39 GiB | 41.1 MB |
| Span a = 8 | 9 / 64 / 0 | 136–139 s | 0.21 s | 45.4–46.1 s | **428–434 s** | 414–420 s | 98–99 s | 15.1–15.2 s | 2.62–2.75 GiB | 50.4 MB |
| Span a = 2 (seed 101) | 63 / 64 / 0 | 26 s | 0.14 s | 3.69 s | 239 s | 230 s | 24 s | 4.1 s | 0.80 GiB | 8.9 MB |
| Span a = 4 (seed 101) | 21 / 64 / 0 | 53 s | 0.16 s | 11.66 s | 264 s | 253 s | 40 s | 7.0 s | 1.80 GiB | 18.9 MB |

- **Same target result for every a**: per seed, every record (both variants, every a) has the same `result_digest` (SHA-256 of R) and passed `verify_statement` against `root_statement(task)`. The tree hashes differ with a (and agree across variants for the same a, as designed).
- "Sequential prove" is the sum of the per-node wall times in a single-threaded process. The record's `cpu_user_ms` covers the whole process (setup, breakdown synthesis, proving, verify): 335–339 s (Direct a = 2), 625–631 s (Direct a = 4), 566–568 s (Span a = 8). Setup is excluded from "sequential prove".
- "Computed critical path" = Σ over levels of the slowest node of that level, from these single-threaded times (one worker per node, no contention). It is **computed, not measured**, and labelled so in every record.
- Work per real leaf (Direct): a = 2 ≈ 4.4 s, a = 4 ≈ 8.0 s. A larger a needs fewer merges (63 → 21 → 9), but each merge circuit grows faster than a (the CycleFold accumulator folds scale with a·n_cf, and n_cf itself grows with a). On this implementation a = 2 is the cheapest in both total work and computed critical path; a = 4 and a = 8 only reduce the depth (6 → 3 → 2).

### 3.4 Padding work vs internal-node work (Direct a = 2, L = 50, seed 101)

| | count | time |
|---|---|---|
| real leaves | 50 | 8.9 s |
| dummy proofs (padding subtrees `[50, 52)`, `[52, 56)`, `[56, 64)`) | 3 | **0.53 s** |
| merges | 52 (49 for an unpadded tree of 50 leaves) | 213.3 s, of which ≈ 12.6 s for the 3 merges that exist only because of padding |
| root verify / peak RSS | — | 9.6 s / 1.19 GiB |

The dummy rule costs one base-case proof per maximal padding subtree, never one per padded position (14 here). L = 64 needs no padding for a ∈ {2, 4, 8}.

### 3.5 Parallel latency (separately labelled; `results/raw/p6-tree-parallel.jsonl`)

`kn-run scenario tree a=2 L=64 variant=direct mode=levels parallel=1 --threads 4 --seed 101 --experiment p6-tree-parallel`: the nodes of each level are proven concurrently on a 4-thread rayon pool (which also parallelises inside each node). **Measured** driver wall time **82.5 s** (per level: 3.7, 33.2, 19.4, 11.2, 5.7, 4.8, 4.4 s), against **289.4 s** sequential single-threaded (seed 101, §3.3) and the 31.5 s computed critical path. The per-node times summed in that run (305 s) are not single-threaded CPU work (contention, intra-node threads), and its peak RSS was 2.06 GiB (a whole level of proofs is kept). This number is never mixed into the main tables. a = 4 was not run in parallel (a level of 64 padded 2^20-row leaf proofs plus 4 concurrent merges would approach the 16 GB limit).

### 3.6 Suite results

Run on `p6-pcd` at `f11f559` plus the clippy rename and these docs (2026-11-14, development laptop):

| Command | Result |
|---|---|
| `cargo fmt --all --check` | clean |
| clippy (`-p kn-ccs -p kn-run -p nova-snark --release --all-targets -- -W clippy::all -A clippy::len_without_is_empty`) | clean (only the pre-existing workspace `resolver` warning) |
| kilonova suite (`--release --lib kilonova -- --test-threads=1`) | **109 passed, 0 failed, 10 ignored** (1,592 s, peak RSS 3.0 GiB). Master baseline was 95 / 8; the 14 new tests are in `pcd::tests`; the 10 ignored are the 4 v1 B15 tests, the v1 perf harness, the 3 long P4/P5 chains and the 2 long 64-leaf tree tests below |
| long tests, run explicitly (`--ignored`): `test_ivc_chain_t64_direct`, `test_ivc_chain_span_long`, `test_ivc_chain_k16`, `test_tree_64_leaves_all_arities`, `test_tree_64_leaves_a2` | @@LONG@@ |
| `cargo test -p nova-snark --release --lib nova::tests::test_ -- --test-threads=1` | 11 passed, 2 ignored |
| `cargo test -p kn-ccs --release` | 21 passed |
| `cargo test -p kn-run --release -- --test-threads=1` | 10 passed |

## 4. What changed for callers

- New module `kilonova::pcd` (no change to `kilonova::ivc` behaviour or to HFS v2): `TreeParams::setup(leaf, leaf_ids, a, tpl)`, `NodeProof::{prove_leaf, prove_dummy, prove_node, verify_root, verify_statement, check_incoming}`, `prove_tree`, `prove_tree_levels`, `TreeTask`, `RootStatement`.
- `ivc::breakdown::BreakdownCS::with_categorizer` (the default categorizer is unchanged); a few `ivc::gadgets` / `ivc::cyclefold` helpers became `pub(crate)` (visibility only).
- `kn-scenario tree` (`a`, `L`, `K_leaf`, `variant`, `mode=seq|levels`, `parallel`).

## 5. Known limitations and open items

- **Direct a = 8 does not fit the setup cap** (1.71 M rows > 2^20); a = 8 runs with Span only. Not optimised: the CycleFold accumulator folds (one `mult_mod` + `red_mod` per public input per fold, 57–78 % of the merge circuit). Fusing `X + r·X′` into one reduction, or not carrying the CycleFold inputs as bignat public inputs, would shrink it; neither is done.
- **Uncompressed** (G2, P7): `verify_root` reads the root witnesses; the decider is the weighted O(Σ_k nnz) path (root verify 4–15 s here).
- An in-circuit violation anywhere in the tree surfaces at the root as RootIncoming (or Statement when the root's own range is broken); the verifier cannot say which node failed (the tests locate it with `check_incoming`).
- Leaf predicates and inputs are fixed per position by the task and bound by the tree hash (and task id), which the verifier compares through the task-derived statement; there is no in-circuit φ for trees.
- Leaves are padded to the merge circuit (9.3k → 228k rows for Direct a = 2): every leaf still pays a padded witness commitment (0.18 s). The non-uniform family keeps leaf *circuits* small, not their commitments.
- The tree CycleFold accumulator carries u as limbs; like X, limbs are range-checked where produced (`red_mod`) and bound by the link hashes elsewhere (as in P5). The non-canonical limb encodings of E1 points (spec §9.7) apply here too.
- Timings come from a fanless laptop. The Direct a = 2 seed 202/303 records carry `implementation_dirty = true` because `configs/common.toml` and `versions.lock` were being edited during the run (no code change; committed in `9d22399`); all other records are clean (`f11f559`, `e114758`).
- No knowledge-soundness proof for the composed scheme; tests are not a proof. No independent review yet.
- v1 code and the B18 fix untouched.

## 6. Definition-of-done commands

```bash
cargo fmt --all --check
cargo clippy -p kn-ccs -p kn-run -p nova-snark --release --all-targets -- -W clippy::all -A clippy::len_without_is_empty
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1
cargo test -p nova-snark --release --lib -- kilonova::ivc::tests::test_ivc_chain_t64_direct kilonova::ivc::tests::test_ivc_chain_span_long kilonova::ivc::tests::test_ivc_chain_k16 kilonova::pcd::tests::test_tree_64 --ignored --test-threads=1
cargo test -p nova-snark --release --lib nova::tests::test_ -- --test-threads=1
cargo test -p kn-ccs --release
cargo test -p kn-run --release -- --test-threads=1
target/release/kn-run scenario tree a=2 L=64 variant=direct mode=seq --seed 101 --experiment p6-tree
```

## 7. Commits

| Commit | Content |
|---|---|
| `36bd238` | plan (`docs/P6-plan.md`) |
| `e114758` | `kilonova::pcd` (gadgets, CycleFold, node circuits, params, prover, verifier, task generator, breakdown, tests), `kn-scenario tree`, spec §11, claim map §8 |
| `9d22399` | `configs/common.toml [pcd]`, `versions.lock` |
| `f11f559` | 64-leaf arity test (Direct a = 2, 4; Span a = 8; Direct a = 8 at Setup) |
| follow-up | clippy rename (`TreeParams::pcd_arity`), records `results/raw/p6-tree*.jsonl` and logs, this report, PLAN/README/AGENTS/baseline updates |

## 8. Entry conditions for later periods

- **P7**: compress the root accumulators (HFS ACCS + tree CycleFold relaxed R1CS); the root statement `(task_id, L, a, [0, a^d), R, h)` is the public statement to bind.
- **Before the E6 arity scan**: the CycleFold accumulator folds dominate the merge circuit and grow with a·n_cf; without reducing them, Direct a = 8 cannot be set up and a larger a only trades depth for much larger nodes.
- **P8/P9**: `kn-scenario tree` covers E6 (a ∈ {2, 4, 8}, L = 64) and the W4 part of E8; formal runs on the Linux host.
