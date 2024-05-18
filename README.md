# KiloNova
This is a proof-of-concept implementation of KiloNova. 
Please do NOT use this in the production environment.

# Introduction
KiloNova is a high-speed recursive zkSNARK, allowing a group of mutually distrusted provers to perform a complicated computation in private, and finally output a short proof with succinct verification to convince the verifier.

Theoretically, KiloNova solves a specific class of problems called Proof-Carrying Data (a generalized version of Incrementally Verifiable Computation) by utilizing the generic folding schemes we proposed. Moreover, KiloNova provides some useful attributes such as (1) handling non-uniform circuits, which is necessary for building zkVM, and (2) zero-knowledge, which ensures privacy among different provers.

Inspired by HyperNova, KiloNova linearizes the high-degree CCS (Customizable Constraint Systems) relation by running an “early stopping” version of SuperSpartan and folds the derived instances without introducing extra communications.
The theoretical analysis shows that KiloNova achieves the same asymptotic complexity as HyperNova while providing the more appealing attributes mentioned above.

<p align="center">
<img src="https://github.com/FranklinZty/KiloNova-poc/assets/44116484/db9a7d96-8ef3-4622-b239-f54ef3d2b906" width="250">  <br>
Kilonova Space Explosion Could (from agnirva.medium.com)
<p>

# Development Progress
## Generic Folding Schemes (In Progress)
1. Implement multi-folding schemes for CCS instances (Finished). 
2. Generalize the folding scheme to handle instances with non-uniform circuits (In Progress).
3. Achieve zero knowledge (In Progress).
## Recursive Circuit for CCS (TODO)
This step requires a crate for building CCS arithmetic circuits from rust (just like the bellpepper for building R1CS circuits in Nova). 
However, there is no known crate that satisfies this requirement.
## KiloNova PCD Constructions (TODO)
Implement the zero-knowledge PCD scheme, and integrate it with an off-the-shell SNARK system.
