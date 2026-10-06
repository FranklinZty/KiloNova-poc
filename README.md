# KiloNova

This is a proof-of-concept implementation of KiloNova for academic use.
Please do NOT use this in the production environment.

# Introduction

KILONOVA is a preprocessing recursive SNARK for fixed sets of non-uniform predicates. By introducing holographic folding schemes and index-span folding, it enables efficient multi-predicate PCD with constant-size recursive states. This repository contains the proof-of-concept implementation of KILONOVA and its core cryptographic components for scalable recursive proofs. **The PoC does not provide zero knowledge** (see `docs/protocol-spec.md` §4).

<div align="center">
  <img src="./kilonova.png" width="600">
</div>

# Development Progress

Status as of 2026-10-05. Details are in `PLAN.md` and `docs/baseline-status.md`.

## Holographic Folding Schemes

1. Multi-folding for CCS instances: algebraic PoC in `folding/` (reference only). ✅
2. Non-uniform (indexed) folding for R1CS, Direct and Span variants: implemented in `Nova/src/kilonova/`, with transcript v1 binding all inputs and helper claims. ✅ for small positive-coefficient instances. ⚠️ General R1CS is blocked by known issue B15 (folding runs over the wrong field).
3. Index commitment folding. ✅

## Preprocessing Recursive SNARK

1. Succinct in-circuit HFS verifier; setup converges (2 iterations for K=3). ✅
2. Index-span folding (Span variant). ✅
3. Multi-step non-uniform IVC. ⛔ Blocked by B15; the 1-step bootstrap verifies.
4. Compressed SNARK / independent final verifier. ⏳ (P7)
5. Native high-degree CCS proving. ⏳ (P2/P3)

## Build & test

```bash
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1
```
