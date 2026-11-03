# KiloNova-poc Project Guide

## Current status (read first)

- **P0 is done** (2026-10-05). See `docs/baseline-status.md`.
- **P1 harness** (`tools/kn-run`, `results/schema.json`): every measurement goes through `kn-run` so records share one format. See `docs/P1-report.md`.
- **P2 oracle** (`ccs/`, crate `kn-ccs`): native CCS builder and the independent ACCS/CCCS reference checker, ff-generic, with kilonova's conventions pinned by `test_kn_ccs_matches_kilonova_conventions`. Use it as the oracle in P3; do not make it depend on `kilonova/`. See `docs/P2-report.md`.
- `Nova/src/kilonova/` is the **normative** implementation (`docs/protocol-spec.md`). `folding/` is a reference oracle only. `NIFS-circuit/` holds the historical cost model behind the old paper figures; never reuse its numbers.
- **Open critical blocker B15:** the HFS folds over `E::Base` while the R1CS lives over `E::Scalar`. Multi-step IVC tests are `#[ignore = "known issue B15 …"]`; the 1-step bootstrap passes. The fix is P3/P5 (see PLAN.md §0 and the P3.0 decision spike).
- Invariants that must not regress:
  - The in-circuit HFS verifier is **succinct**. It must never take or re-evaluate the other curve's witness; that made setup diverge (44M constraints).
  - The native and gadget transcripts are identical (`transcript.rs` tags). `test_transcript_native_matches_gadget_*` guards this.
  - Commitment keys are sized from padded shapes.

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
| `transcript.rs` | HFS transcript v1 domain tags + in-circuit tag helper (shared by native and gadget) |
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
