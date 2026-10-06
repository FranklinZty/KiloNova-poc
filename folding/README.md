# KiloNova
This is a proof-of-concept implementation of KiloNova for academic use. 
Please do NOT use this in the production environment.

# Introduction
> **Status (2026-10-05):** this crate is a standalone algebraic PoC of generic CCS folding. It is **not** the mainline implementation (see `Nova/src/kilonova/` and `docs/protocol-spec.md`). It is not serialisable, does not bind statements in its transcript, has no negative tests and has known defects (B11, B12, B14 in `docs/baseline-status.md`). Use it only as a reference oracle.

KiloNova is a recursive SNARK for proof-carrying data over a fixed family of non-uniform predicates. **This PoC does not provide zero knowledge.**

Theoretically, KiloNova solves a specific class of problems called Proof-Carrying Data (a generalized version of Incrementally Verifiable Computation) by utilizing the generic folding schemes we proposed. Moreover, KiloNova handles non-uniform circuits from a fixed predicate family.

Inspired by HyperNova, KiloNova linearizes the high-degree CCS (Customizable Constraint Systems) relation by running an “early stopping” version of SuperSpartan and folds the derived instances without introducing extra communications.
The theoretical analysis shows that KiloNova achieves the same asymptotic complexity as HyperNova while providing the more appealing attributes mentioned above.

<p align="center">
<img src="https://github.com/FranklinZty/KiloNova-poc/assets/44116484/db9a7d96-8ef3-4622-b239-f54ef3d2b906" width="250">  <br>
Kilonova Space Explosion Could (from agnirva.medium.com)
<p>

# Development Progress (this crate)
1. Multi-folding for CCS instances (algebra only). Finished.
2. Everything else (non-uniform folding, recursion, transcript binding) lives in `Nova/src/kilonova/`. This crate is not developed further, except as a test oracle in P2/P3 of `PLAN.md`.
