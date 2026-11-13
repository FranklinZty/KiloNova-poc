# KiloNova-poc Project Guide

## Current status (read first)

- **P0 is done** (2026-10-05). See `docs/baseline-status.md`.
- **P1 harness** (`tools/kn-run`, `results/schema.json`): every measurement goes through `kn-run` so records share one format. See `docs/P1-report.md`.
- **P2 oracle** (`ccs/`, crate `kn-ccs`): native CCS builder and the independent ACCS/CCCS reference checker, ff-generic, with kilonova's conventions pinned by `test_kn_ccs_matches_kilonova_conventions`. Use it as the oracle in P3; do not make it depend on `kilonova/`. See `docs/P2-report.md`.
- `Nova/src/kilonova/` is the **normative** implementation (`docs/protocol-spec.md`). `folding/` is a reference oracle only. `NIFS-circuit/` holds the historical cost model behind the old paper figures; never reuse its numbers.
- **P3 native-field HFS v2** (`Nova/src/kilonova/hfs/`): folds over `E::Scalar` for any CCS template and μ running + ν incoming inputs, Direct and Span, transcript v2 (`transcript.rs::v2`, spec §8; Poseidon over `E::Scalar` with 4×64-bit limb commitments, following D1 = (a)). No recursion. Frozen vectors in `hfs/vectors/` (`KN_UPDATE_VECTORS=1` only with a version bump). See `docs/P3-report.md`.
- **D1 decided (a): Nova fork + CycleFold** (2026-11-09, `docs/P3.0-decision.md`). Transcript v2 stays v2. P5 builds the CycleFold recursion on `kilonova::hfs`.
- **P5 recursion on v2** (`Nova/src/kilonova/ivc/`): one primary augmented circuit per predicate over `E1::Scalar` verifying HFS v2 in-circuit, one CycleFold circuit over `E2::Scalar` for the E1 group operations (folded with an n-input Nova fold gadget), native `RecursiveSNARK` (`new`, `prove_step`, `verify`), in-circuit Poseidon trace chain, `kn-scenario ivc`. See `docs/P5-report.md`, spec §9. Not done: compression (P7). Trace recovery / φ: done in P4.
- **P4 family, φ and index-span** (`Nova/src/kilonova/family/`, `ivc/program.rs`): `PredicateFamily` (stable ids, canonical member encoding = `kn_ccs::encode`, family digest = the HFS transcript digest and the link-hash digest slot, `HfsParams::from_family`, `PublicParams::setup_pinned`); in-circuit selection φ (`PredicateProgram`; `Scheduled<P>` keeps an explicit schedule in a program register of the state); `ivc::RecursiveSNARK::verify(pp, n, z0)` takes **no schedule** and returns `(z_n, trace, last_id)`, `verify_schedule` only compares (G3, G4 closed for v2); IVC_VERSION = 2. Explicit folded-matrix vs weighted-evaluation paths (`FoldedMatrices`, `weighted_eval`, `support_stats`); `kn-scenario family`. See `docs/P4-report.md`, spec §9.8 and §10.
- **P6 tree PCD** (`Nova/src/kilonova/pcd/`): family `[leaf/k…, merge, dummy]`; a merge verifies one HFS v2 fold of **μ = a running + ν = a incoming** instances in-circuit (`pcd::gadgets::verify_hfs_multi`, μ/ν-generic, equal to the P5 gadget at μ = ν = 1) and folds a CycleFold accumulators (relaxed–relaxed folds, u and X as limbs) plus one multi-input CycleFold instance (`CycleFoldCircuitN`); leaves/dummies are the base case (no verifier). Tree hash + in-circuit ranges bind positions, order, ranges, ids; task id in every link hash. `NodeProof::verify_root(pp)` takes no tree structure and returns `(task_id, L, a, [0, a^d), R, tree hash)`; `TreeParams::root_statement(task)` gives the expected one. Never assume a = μ + ν. Direct a = 8 exceeds `MAX_SETUP_CONSTRAINTS` (do not raise the cap; a = 8 runs with Span). `kn-scenario tree`. See `docs/P6-report.md`, spec §11.
- **B15:** fixed for native folding (P3) and recursion (P5, v2). The **v1 recursion path** (`nifs.rs`, `span/`, `kilonova::RecursiveSNARK`) is kept unmodified as historical evidence; its multi-step tests stay `#[ignore = "known issue B15 (v1 path only …)"]`. Do not modify v1 to "fix" it.
- Invariants that must not regress:
  - The in-circuit HFS verifier is **succinct**. It must never take or re-evaluate the other curve's witness; that made setup diverge (44M constraints).
  - The native and gadget transcripts are identical (`transcript.rs` tags). `test_transcript_native_matches_gadget_*` guards this.
  - Commitment keys are sized from padded shapes.
  - The v2 verifier (`hfs::NIFS::verify`) reads only instances, proof messages and public parameters (never a witness or a matrix); ε/θ are deferred to `hfs::decide`. Every v2 test also runs the independent kn-ccs oracle.

## Overview

KiloNova is a **preprocessing recursive SNARK** for fixed sets of non-uniform predicates. It extends Nova's IVC (Incrementally Verifiable Computation) to support different circuits at each recursion step via **holographic folding schemes** and **index-span folding**. This repository is a proof-of-concept for academic use.

## Repository Structure

```
KiloNova-poc/
├── Cargo.toml              # Workspace root (members: NIFS-circuit, Nova, ccs, tools/kn-run; folding excluded)
├── README.md               # Project overview and development progress
├── kilonova.png            # Architecture diagram
├── PLAN.md                 # Development & experiment plan (English, revised 2026-10-05)
├── versions.lock           # Toolchain / dependency freeze (P0)
├── rust-toolchain.toml     # Pinned toolchain (1.92.0)
├── configs/common.toml     # Parameter contract (P0 freeze)
├── ccs/                    # P2 kn-ccs: native CCS builder + ACCS/CCCS reference checker (ff-generic oracle)
├── tools/kn-run/           # P1 experiment harness: kn-run (runner) + kn-scenario (child)
├── results/                # schema.json (record layout) + raw/ append-only JSONL run records
├── docs/                   # P0–P2 specs and reports
│   ├── protocol-spec.md    # NORMATIVE protocol + transcript (HFS v1)
│   ├── claim-check-map.md  # claim -> checker -> code location
│   ├── baseline-status.md  # measurements + blocker register B1-B17
│   ├── P0-plan.md          # P0 rebase plan (Chinese)
│   ├── P1-plan.md          # P1 harness plan
│   ├── P1-report.md        # P1 acceptance report
│   ├── P2-plan.md          # P2 CCS/ACCS oracle plan
│   ├── P2-report.md        # P2 acceptance report
│   ├── P3.0-decision.md    # D1 decision memo (decided (a), 2026-11-09)
│   ├── P3-plan.md          # P3 native-field HFS plan
│   ├── P3-report.md        # P3 acceptance report
│   ├── P5-plan.md          # P5 recursion plan
│   ├── P5-report.md        # P5 acceptance report
│   ├── P4-plan.md          # P4 family / φ / index-span plan
│   ├── P4-report.md        # P4 acceptance report
│   ├── P6-plan.md          # P6 tree PCD plan
│   ├── P6-report.md        # P6 acceptance report
│   └── PLAN.zh.md          # original Chinese PLAN (2026-09-21)
│
├── Nova/                   # Core crate: nova-snark v0.42.0
│   ├── Cargo.toml
│   ├── src/
│   │   ├── lib.rs          # Module declarations, type aliases
│   │   ├── constants.rs    # Global constants
│   │   ├── digest.rs       # Digest/hash utilities
│   │   ├── errors.rs       # Error types (NovaError)
│   │   ├── kilonova/       # *** ORIGINAL KILONOVA CONTRIBUTION ***
│   │   ├── nova/           # Original Nova uniform IVC
│   │   ├── neutron/        # NeutronNova single-curve IVC (experimental)
│   │   ├── spartan/        # Spartan SNARK (compression layer)
│   │   ├── traits/         # Core trait definitions
│   │   ├── provider/       # Curve & commitment implementations
│   │   ├── r1cs/           # R1CS data structures
│   │   ├── frontend/       # Constraint system framework (bellpepper port)
│   │   └── gadgets/        # Circuit gadgets (ECC, non-native arithmetic)
│   ├── benches/            # Benchmarks
│   └── examples/           # Example circuits
│
├── NIFS-circuit/           # Benchmark crate: circuit cost comparison
│   ├── Cargo.toml          # Depends on nova-snark + hyperplonk
│   └── src/
│       ├── main.rs         # Benchmarks Nova vs KiloNova vs ZK-PCD circuit sizes
│       └── circuit/
│           ├── mod.rs      # Augmented circuit with scheme dispatch
│           └── r1cs.rs     # In-circuit folding verification gadgets
│
└── folding/                # Standalone PoC crate: Generic Folding Scheme over CCS
    ├── Cargo.toml          # Package name "Kilonova-poc", uses arkworks ecosystem
    └── src/
        ├── lib.rs
        ├── genericfolding.rs  # Core multi-instance folding protocol
        ├── ccs/               # CCS/ACCS/CCCS data structures
        ├── espresso/          # Sumcheck & polynomial infrastructure (from HyperPlonk)
        ├── bellpepper/        # Spartan2/bellpepper integration test
        └── util/              # Hypercube, MLE, matrix/vector utilities
```

## Architecture

### Three IVC Schemes in the Nova Crate

```
                    ┌─────────────┐
                    │   lib.rs    │
                    └──────┬──────┘
           ┌───────────────┼───────────────┐
           ▼               ▼               ▼
      ┌─────────┐    ┌──────────┐    ┌──────────┐
      │ kilonova│    │   nova   │    │ neutron  │
      │(non-unif│    │(uniform  │    │(single-  │
      │  IVC)   │    │  IVC)    │    │ curve)   │
      └────┬────┘    └────┬─────┘    └────┬─────┘
           │              │               │
           ├──────────────┼───────────────┤
           ▼              ▼               ▼
      ┌────────────────────────────────────────┐
      │            Shared Infrastructure       │
      │  traits/  r1cs/  frontend/  gadgets/   │
      │  spartan/  provider/  constants/       │
      └────────────────────────────────────────┘
```

### KiloNova Protocol Flow

1. **Setup** (`PublicParams::setup`): Given a `PredicateSet` with N predicates, synthesizes N primary augmented circuits + 1 secondary. Determines shapes via fixed-point iteration. Builds `GlobalStructure` with precomputed matrix bucket tables and index commitments.

2. **Proving** (`RecursiveSNARK::prove_step`): At each step, selects a predicate ID. Folds secondary instance via holographic NIFS, synthesizes primary augmented circuit (verifies secondary fold + applies predicate), folds primary instance, synthesizes secondary augmented circuit (verifies primary fold). Updates trace digest.

3. **Verification** (`RecursiveSNARK::verify`): Checks step count, predicate trace digest, output hash consistency, folded relation satisfaction on both curves.

4. **Holographic Folding NIFS**: Two-phase sumcheck (row variables X, then column variables Y). Index commitments (`comm_M`) encode active predicates via linear combinations. Cross-term claims (sigmas, taus, epsilons, thetas) replace Nova's single comm_T.

### Crate Relationships

- **`Nova/`**: Main library containing all three IVC schemes and shared infrastructure. The `kilonova/` module is the original contribution; `nova/`, `spartan/`, `neutron/` are inherited.
- **`NIFS-circuit/`**: Benchmarking tool that synthesizes augmented circuits for Nova/KiloNova/ZK-PCD and measures constraint counts. Depends on `nova-snark`.
- **`folding/`**: Standalone algebraic PoC of the Generic Folding Scheme over CCS using arkworks/BLS12-381. Demonstrates folding mu ACCS + nu CCCS instances into one ACCS. Independent from the Nova crate.

## Key Modules Detail

### `Nova/src/kilonova/` (Original Contribution)

| File | Purpose |
|------|---------|
| `mod.rs` | `PredicateSet` trait, `PublicParams`, `RecursiveSNARK`, trace digest |
| `relation.rs` | `PredicateIndex`, `GlobalStructure`, `FoldedWitness`, `FoldedInstance` with lambda coefficients |
| `nifs.rs` | `NIFS` with two-phase sumcheck (sc_proof_x + sc_proof_y), cross-term computation |
| `transcript.rs` | HFS transcript v1 domain tags + in-circuit tag helper (shared by native and gadget); `v2` submodule (P3) |
| `ivc/` | P5 recursion on HFS v2 + CycleFold: `circuit.rs` (primary augmented circuit), `cyclefold.rs`, `gadgets.rs` (HFS gadget, n-input fold, non-native points), `shape.rs` (native power rows), `breakdown.rs`, `fixtures.rs` (K ≤ 16 chain family), `program.rs` (P4: φ, `Scheduled`), `tests.rs` |
| `family/` | P4: `PredicateFamily`, canonical member encoding, family digest, explicit folded-matrix and weighted-evaluation paths, support statistics, tests |
| `pcd/` | P6: tree PCD: `gadgets.rs` (μ/ν-generic HFS gadget, CycleFold tree accumulator), `cyclefold.rs` (multi-input CycleFold circuit, relaxed folds), `circuit.rs` (leaf/merge/dummy), `mod.rs` (params, prover, root verifier, drivers), `task.rs` (W4 task generator, layout, dummy rule), `breakdown.rs`, `tests.rs` |
| `hfs/` | P3 native-field HFS v2: `structure.rs` (template, shapes, params, digest), `instance.rs` (Direct/Span), `sumcheck.rs`, `nifs.rs` (prover/verifier, μ/ν inputs), `decider.rs`, `tests.rs`, `vectors/` |
| `circuit/mod.rs` | `KiloNovaAugmentedCircuit` for recursive verification |
| `circuit/r1cs.rs` | In-circuit holographic folding verification gadgets |
| `span/` | Alternative "span" variant (lambda stored directly, not committed) |
| `test_utils.rs` | Test infrastructure comparing direct vs span variants; native-vs-gadget transcript tests; shared `ExamplePredicates` (K=3) fixture used by tests and `kn-run` |

### `Nova/src/nova/` (Inherited from Nova)

Standard uniform IVC: `RecursiveSNARK`, `CompressedSNARK`, single-sumcheck NIFS with comm_T cross-term.

### `Nova/src/neutron/` (Inherited from NeutronNova, experimental)

Single-curve IVC using zero-fold relation. Feature-gated behind "experimental".

### `Nova/src/spartan/` (Inherited from Spartan)

SNARK compression layer: `snark.rs` (non-preprocessing), `ppsnark.rs` (preprocessing/Spark), `direct.rs` (direct proving), `sumcheck.rs`, `polys/` (multilinear/univariate/eq polynomials).

### `folding/src/` (Standalone PoC)

| File | Purpose |
|------|---------|
| `genericfolding.rs` | Core protocol: prove/verify/fold for mu ACCS + nu CCCS instances |
| `ccs/ccs.rs` | CCS structure (matrices, multisets, coefficients) |
| `ccs/accs.rs` | Atomic CCS instance with evaluation claims |
| `ccs/cccs.rs` | Committed CCS instance with witness commitment |
| `ccs/pedersen.rs` | Pedersen vector commitment scheme |
| `espresso/` | Sumcheck protocol, VirtualPolynomial, multilinear utilities (from HyperPlonk) |

## Build & Development

```bash
# Build workspace (Nova + NIFS-circuit)
cargo build

# Run tests (kilonova suite; --release and --test-threads=1 are REQUIRED on 16 GB machines)
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1

# Setup fixed-point sizes per iteration
cargo test -p nova-snark --release --lib kilonova::tests::test_setup_fixed_point_converges -- --nocapture

# Experiment harness (P1): process-isolated runs, JSONL records in results/raw/
cargo build -p kn-run --release && target/release/kn-run selfcheck --quick

# CCS reference oracle (P2)
cargo test -p kn-ccs --release

# Native-field HFS v2 (P3) and its kn-run scenario
cargo test -p nova-snark --release --lib kilonova::hfs -- --test-threads=1
target/release/kn-run scenario hfs template=r1cs variant=direct steps=100 --seed 101

# P5 recursion (v2 + CycleFold) and its kn-run scenario
cargo test -p nova-snark --release --lib kilonova::ivc -- --test-threads=1
target/release/kn-run scenario ivc K=2 steps=16 variant=direct verify_every=4 --seed 101 --experiment p5-ivc

# P4 family / index-span (support growth vs K) and its tests
cargo test -p nova-snark --release --lib kilonova::family -- --test-threads=1
target/release/kn-run scenario family source=synthetic K=16 overlap=partial --seed 101 --experiment p4-family

# P6 tree PCD (64-leaf trees are #[ignore]d; run explicitly) and its kn-run scenario
cargo test -p nova-snark --release --lib kilonova::pcd -- --test-threads=1
target/release/kn-run scenario tree a=2 L=64 variant=direct --seed 101 --experiment p6-tree

# Run NIFS-circuit benchmarks
cargo run -p NIFS-circuit

# Build folding crate separately (not in workspace)
cd folding && cargo build

# Run specific benchmark
cargo bench --bench kilonova-single-step
```

## Tech Stack

- **Language**: Rust (edition 2021)
- **Curves**: Pallas/Vesta (Pasta cycle; used by kilonova), BN254/Grumpkin, secp256k1/secq256k1, BLS12-381 (folding crate)
- **Crypto primitives**: Poseidon hash, Pedersen commitment, HyperKZG, IPA
- **Constraint systems**: R1CS, CCS (Customizable Constraint Systems)
- **Dependencies**: ff, halo2curves, arkworks (folding crate), hyperplonk/subroutines

## Files Marked for Deletion

The following files/directories are IDE artifacts, OS metadata, or otherwise irrelevant to the project and should be removed:

### `.DS_Store` files (macOS metadata)
- `.DS_Store`
- `NIFS-circuit/.DS_Store`
- `NIFS-circuit/src/.DS_Store`
- `Nova/.DS_Store`
- `Nova/src/.DS_Store`
- `Nova/src/spartan/.DS_Store`
- `folding/.DS_Store`

### `.idea/` directories (JetBrains IDE)
- `.idea/` (entire directory including `.gitignore`, `copilot.data.*.xml`, `modules.xml`, `vcs.xml`, `zkpcd.iml`)
- `NIFS-circuit/.idea/` (entire directory)
- `Nova/.idea/` (entire directory)

### Other IDE/config files
- `folding/.vscode/launch.json`
- `folding/.github/workflows/rust.yml` (CI config, may be intentionally kept)

### `.gitignore` (applied at P0)

`folding/target` is still tracked in git (5,620 files). Untracking it with `git rm -r --cached folding/target` is left to the maintainer.

```
.DS_Store
.idea/
.vscode/
*.iml
```
