# P6 plan: multi-predecessor PCD and workload closure (2026-11-13)

PLAN.md §3 P6 and §6 W4. Base: `origin/master` at `9273d60` (P0–P5, P4, B18 fix). Work branch `p6-pcd`. Acceptance report: `docs/P6-report.md`. Spec: new `docs/protocol-spec.md` §11.

Entry conditions (P4 report §7, P5 report §6): trees need **μ running inputs in the in-circuit HFS verifier** (it is μ = ν = 1 today; the native HFS v2 already folds μ running + ν incoming instances), **several CycleFold accumulators** per node, and a **tree rule** replacing the trace chain.

## 1. Objects and node semantics

### 1.1 Task (W4)

A task is a list of L ≥ 1 **leaf tasks** `(k_p, x_p)` for positions `p = 0..L−1`: `k_p` is a leaf predicate of the P4 chain family (`ivc::fixtures::ChainPredicates`, members 0 and 1 by default, which really differ in wiring: `(x, y) ↦ (x³ + y + 5, x)` and `(x² − y + 7, y + 1)`), and `x_p ∈ F²` its input. Inputs may repeat; positions may not. `task_id` = SHA3-256 → 250-bit field element (`DigestComputer`) over `(PCD_VERSION, label, L, [(k_p, x_p)])`.

**Target result** (independent of the tree shape, hence of a):

```text
R = Σ_{p<L} β^p · F_{k_p}(x_p)        ∈ F²,   β = 7 (a constant of the leaf circuits)
```

β^p makes R depend on the positions (a reordering of leaves changes R), and the sum makes it independent of the bracketing, so every arity computes the same R.

### 1.2 Tree layout and the dummy rule

For arity a ≥ 2, depth `d = min{d ≥ 0 : a^d ≥ L}` and capacity `N = a^d`. The node at level h, index j covers `[j·a^h, (j+1)·a^h)`. A node with `lo < L` is a **leaf** (h = 0) or a **merge** (h ≥ 1). A node with `lo ≥ L` whose parent has `lo < L` is a **dummy** (a maximal padding subtree): one dummy proof covers the whole padding subtree, so padding work is at most `(a − 1)·d` dummy proofs, never `N − L` leaf proofs. Nodes inside a dummy subtree do not exist. For L = 64 and a ∈ {2, 4, 8}, N = 64 and there are no dummies; the rule is exercised by small trees (L = 5, 6 with a = 2, L = 5 with a = 4).

### 1.3 Node statement and semantics

Every node proves the statement `S = (lo, hi, r, h)` under the task context `(task_id, L)`:

| Role | Circuit (family member) | Statement | Predecessors |
|---|---|---|---|
| leaf, predicate k | `leaf/k` (k < K_leaf) | `lo = p, hi = p + 1, r = β^p · F_k(x_p), h = H(TAG_LEAF, p, k, x_p)`; enforces `p < L` | none (base case) |
| dummy | `dummy` | `[lo, hi)`, `r = 0`, `h = H(TAG_DUMMY, lo, hi)`; enforces `lo ≥ L`, `hi > lo` | none (base case) |
| merge | `merge` | `lo = lo_0, hi = hi_{a−1}, r = Σ_c r_c, h = H(TAG_NODE, lo, hi, h_0, …, h_{a−1})`; enforces `lo_c = hi_{c−1}` and `hi_c − lo_c = hi_0 − lo_0` (contiguous, ordered, equal widths) | exactly a, in order |

So a node over `[lo, hi)` proves `r = Σ_{p ∈ [lo,hi) ∩ [0,L)} β^p F_{k_p}(x_p)` and that h is the hash of the subtree's shape, positions, ids and inputs. **Recursion base case:** leaves and dummies; their running accumulators are the defaults (HFS: identity commitments, u = 0, all claims 0, satisfied by W = 0, λ = 0; CycleFold: identity, u = 0, X = 0). There is no `is_base` flag: base-case circuits are separate members that contain no verifier at all (non-uniform family: leaf members are padded to the merge circuit's size, which is the KiloNova point).

The **tree hash** `h` binds positions (leaf p, every range), predecessor order (children hashed in order), sub-task ranges, ids (`k` is a constant of each leaf circuit) and leaf inputs. Ranges are also enforced in-circuit, so duplicates, gaps and swaps are unsatisfiable, not only hash mismatches.

### 1.4 Node link hash and the PCD proof

Each node circuit has one public output

```text
H_node = H(TAG_LINK, pp_digest, family_digest, task_id, L, lo, hi, r[0..2], h, U, cfU)
```

(Poseidon over E1::Scalar; U in the §8.5 running-instance encoding; cfU = `W(x,y,inf), E(x,y,inf), u (4 limbs), X (4 limbs each)`). A node proof is `(S, U, W_U, u, w_u, cfU, cfW)`: the node's running HFS accumulator (fold of its children, or the default), its own CCCS (the node circuit's instance; io = H_node) and its CycleFold accumulator.

The merge circuit, for each child c: checks `u_c.io[0] = H_node(…, task_id, L, S_c, U_c, cfU_c)` with the **parent's** `task_id` and L (cross-task splicing is unsatisfiable); then one HFS v2 fold of **μ = a running** `U_0…U_{a−1}` and **ν = a incoming** `u_0…u_{a−1}` (in-circuit verifier, always active); one CycleFold instance for all group operations of that fold; then folds the a CycleFold accumulators and the fresh instance (`a − 1` relaxed–relaxed folds, then one fresh fold).

### 1.5 Root statement and verifier

```text
RootStatement = (task_id, L, a, lo = 0, hi = a^d, r = R, h = tree hash)
```

`verify_root(pp, proof) → RootStatement` checks (layers): **Input** (lengths, the root's predicate id < K); **Statement** (`lo = 0`, `hi = a^d` with the minimal d for L, 1 ≤ L < 2^32); **LinkHash** (`u.io[0] = H_node(pp, task_id, L, 0, hi, r, h, U, cfU)`); **Decider** (`hfs::decide(U, W_U)`); **CycleFold** (relaxed R1CS of cfU with openings); **RootIncoming** (the root's CCCS opens and the CCS of its member holds). It takes no tree structure. `verify_statement(pp, proof, expected)` then compares with an expected statement (layer Statement); `TreeTask::root_statement(a)` computes the expected statement from the task alone (task_id, L, R, tree hash), so the verifier never needs the tree.

**Claim.** An accepting `verify_statement` shows (up to the unproven knowledge soundness of the folding layers): there are leaf proofs for exactly the positions `0..L−1`, each once and in order, leaf p running member `k_p` on `x_p` (bound through h and task_id), padding only beyond L, and `R = Σ β^p F_{k_p}(x_p)`. With deterministic F_k the claim is "this specific task result".

## 2. μ/ν ↔ a mapping (never a = μ + ν)

| Configuration | PCD arity a | HFS fold μ (running) | HFS fold ν (incoming) | CycleFold accumulators folded | where |
|---|---|---|---|---|---|
| chain step (P4/P5, IVC) | 1 | 1 | 1 | 1 running + 1 fresh | `ivc` |
| chain base step | 0 | 0 (gated off) | 0 | 0 (default output) | `ivc` |
| tree leaf / dummy (base case) | 0 | 0 (no fold, no verifier) | 0 | 0 | `pcd`, leaf/dummy members |
| tree merge, a = 2 | 2 | **2** | **2** | 2 running (1 relaxed fold) + 1 fresh | `pcd`, merge member |
| tree merge, a = 4 (stretch) | 4 | 4 | 4 | 4 running (3 relaxed folds) + 1 fresh | same |
| tree merge, a = 8 (stretch) | 8 | 8 | 8 | 8 running (7 relaxed folds) + 1 fresh | same |
| root decider | — | 1 accumulator checked, no fold | — | 1 checked | `verify_root` |

So for merges `μ = ν = a` and `μ + ν = 2a`. Every record and config carries `a`, `mu`, `nu` explicitly (merge values; leaf/dummy values in details).

## 3. Components to build

| Item | Where | Notes |
|---|---|---|
| μ/ν-generic HFS v2 verifier gadget | `pcd/gadgets.rs::verify_hfs_multi` | transcript identical to `hfs::NIFS::verify` for any (μ, ν); constraint count equal to the P5 gadget for μ = ν = 1 (regression check); `verify_hfs` (chain) untouched |
| multi-input CycleFold circuit | `pcd/cyclefold.rs` | public inputs `ρ, [k_0..k_{ν−1}], W_0..W_{μ+ν−1}, W_out, (M_0[j]..M_{μ−1}[j], M_out[j])_j`; Horner `Σ ρ^i P_i` with 128-bit ρ only; ι_{k_l} selected in-circuit |
| CycleFold tree accumulator gadget | `pcd/gadgets.rs::CfAcc` | relaxed–relaxed fold (`E ← E_0 + r(T + r E_1)`, `u, X` as bignats mod \|E2::Scalar\|) and fresh fold; native twins `cf_tree_*`; tags `0x4b4e_4346_0002_000{1,2}` |
| node circuits | `pcd/circuit.rs` | leaf (per leaf predicate), merge, dummy |
| `TreeParams::setup` | `pcd/mod.rs` | family `[leaf/0 … leaf/K_leaf−1, merge, dummy]`, fixed point on (s, s′), padded shapes, family digest, keys from padded shapes, pp digest (PCD version, a, K_leaf, β, CycleFold shape) |
| prover API | `pcd/mod.rs` | `prove_leaf`, `prove_dummy`, `prove_node` (native pre-checks at layer Input; hidden `*_unchecked`/tamper hooks for the rejection tests), `prove_tree` (driver: depth-first, sequential) and a level-parallel driver |
| verifier | `pcd/mod.rs` | `verify_root`, `verify_statement`, `NodeProof::check_incoming` (locates in-circuit failures in tests) |
| task generator | `pcd/task.rs` | `TreeTask::generate(seed, L, K_leaf)`, `with_leaves`, `layout(a)` (levels, roles, ranges, dummies), `expected_result`, `root_statement(a)` |
| kn-run | `kn-scenario tree` | records `results/raw/p6-tree.jsonl` |

## 4. Acceptance → test / record

| PLAN.md P6 acceptance | Test / record | Detection layer |
|---|---|---|
| a = 2 tree PCD with root verify, small trees incl. dummies | `pcd::tests::test_tree_a2_small` (L = 4, 5, 6) | — |
| 64 real leaves, same R for every a; padding vs internal work | `pcd::tests::test_tree_64_leaves_all_arities` (`#[ignore]`, run explicitly) + `kn-scenario tree` records for a = 2 (and 4/8 if done) × seeds 101/202/303 | — |
| duplicate leaves | `test_tree_rejects_duplicate_leaf` | Input (honest API); circuit unsatisfied → RootIncoming / Statement |
| missing leaves | `test_tree_rejects_missing_leaf` (gap; dummy below L; shorter task claimed) | Input; circuit → RootIncoming; Statement |
| cross-task splicing | `test_tree_rejects_cross_task_splice` | Input; circuit → RootIncoming; Statement |
| illegal order (swapped children) | `test_tree_rejects_swapped_children` | Input; circuit → RootIncoming |
| forged predecessors | `test_tree_rejects_forged_predecessor` (forged child statement, forged child CCCS, swapped child accumulator, tampered root accumulators) | circuit → RootIncoming; LinkHash / Decider / CycleFold |
| same input ≠ same position | `test_tree_same_input_different_positions` (valid) + duplicate-position test above | — |
| sequential CPU vs parallel latency | kn-run records: main records single-threaded (`--threads 1`), `details.sequential_prove_ms` (Σ node times) and `details.critical_path_ms` (computed, labelled); separate `p6-tree-parallel` records with `parallel=1 --threads N` (measured wall-clock, labelled) | — |
| μ/ν mapping in every config/record | `configs/common.toml [pcd]`, record fields `a`, `mu`, `nu`, `details.mu_nu_mapping` | — |
| μ = 2 gadget native = gadget | `pcd::tests::test_transcript_native_matches_gadget_multi_{direct,span}` ((μ, ν) ∈ {(1,1), (2,2), (2,1), (4,4)}; tampering rejected) and `test_multi_gadget_matches_p5_gadget_size` | — |
| CycleFold multi circuit and tree folds | `test_cyclefold_multi_circuit`, `test_cf_tree_fold_native_matches_gadget` | — |
| succinctness | `test_merge_circuit_breakdown_and_succinctness` (merge size independent of member wiring and far below the family nnz); P5 `test_primary_circuit_is_succinct` still passes | — |
| no regressions | kilonova suite (95 passed / 8 ignored on master + new tests), P4/P5 long chains run explicitly, kn-ccs 21, kn-run 10 | — |

## 5. Decisions

| Item | Decision |
|---|---|
| Node fold | one HFS fold with μ = ν = a (not a cascade of 2-input folds) |
| CycleFold for μ + ν points | Horner with the 128-bit ρ (ρ^i are never non-native scalars) |
| CycleFold accumulators | a − 1 relaxed–relaxed folds then one fresh fold; u and X carried as bignats (u grows beyond 128·depth bits otherwise) |
| Base case | separate leaf/dummy members, no `is_base` gate |
| Dummy rule | maximal padding subtrees beyond L, one dummy proof each, `lo ≥ L` enforced in-circuit |
| Leaf binding | tree hash (positions, ranges, ids, inputs) + task_id in every link hash; target R with β^p weights |
| Version | `pcd::PCD_VERSION = 1`, new tags `0x4b4e_5043_4401_000{1..4}` (link, leaf, node, dummy); HFS transcript v2 unchanged; chain IVC v2 unchanged |
| Variants | generic over `IvcVariant` (Direct and Span); records use Direct |
| v1 code, B18 fix | untouched |

## 6. Priorities

1. This plan; μ = 2 gadget with native-vs-gadget test. 2. a = 2 PCD with root verify, small trees, rejection suite. 3. 64-leaf a = 2 tree, sequential/parallel, kn-run records. 4. Report and docs. 5. a = 4. 6. a = 8.
