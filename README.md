# zk\-PCD

<p align="center">
  <a href="https://opensource.org/licenses/Apache-2.0"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
  <a href="https://img.shields.io/badge/status-proof--of--concept-orange"><img src="https://img.shields.io/badge/status-proof--of--concept-orange.svg"></a>
</p>

<p align="center">A Rust implementation of Zero-Knowledge Proof-Carrying Data (PCD): modular, efficient and recursive-friendly </p>

## About

**zk\-PCD** is a new theoretical and practical improvements for zero-knowledge Proof-Carrying Data.
This repository is a proof-of-concept implementation for validating the performance improvements claimed in the paper "Zero-Knowledge Proof-Carrying Data from
Accumulation Schemes".

## Key Features

- **Zero Knowledge**: the zkPCD naturally supports zero-knowledge property for the recursive proofs.
- **New Construction**: we propose a new zero-knowledge PCD construction that directly avoids the requirement of a zero-knowledge NARK component.
- **High Efficiency**: we present a concrete design for an eligible accumulation scheme for special sound protocol.
- **Pluggable Backends**: abstract interface to integrate multiple curve engines (e.g., Pasta, Bn256, Secp256k1).

<img src="./doc/ZK-PCD.png" alt="New Zero-Knowledge Proof-Carrying Data Construction" width="60%" />

## Asymptotic Complexity

| SPS Protocols |                                Protogalaxy | Ours |
|---------------|-------------------------------------------:|:---|
| Degree-d gate |          \$O(2^d)\ G + O(d\log m)\ F\$ | \$2G + O(d\log m)\ F\$ |
| Permutation   |                  \$4G + O(\log m)\ F\$ | \$2G + O(\log m)\ F\$ |
| Lookup        | \$(4\ell+2)\ G + O(\log m + \ell)\ F\$ | \$3G + O(\log (m+\ell))\ F\$ |
| R1CS          |                  \$7G + O(\log m)\ F\$ | \$2G + O(\log m)\ F\$ |
| CCS           |          \$O(2^d)\ G + O(d\log m)\ F\$ | \$2G + O(d\log m)\ F\$ |

_Footnote:_ Assume \$m\$ is the number of accumulated predicate instance-proof pairs, \$d\$ is the maximum degree of relations, and \$\ell\$ is the size of the query set for lookup arguments. F, G represent the cost of field and group operations, respectively.

## Practical Complexity (simulated)
Currently, we only implement a simulated R1CS circuit for estimating the size of recursive overhead (especially the NIFS verification cost)..
| Steps | Degrees | BCL+21 Constraints | BCL+21 Synthesize Time \(ms\) | ZK\-PCD Constraints | ZK\-PCD Synthesize Time \(ms\) |
|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 14577 | 141 | 12139 | 112 |
| 1 | 3 | 19459 | 171 | 12145 | 115 |
| 1 | 4 | 29217 | 231 | 12151 | 114 |
| 2 | 2 | 15667 | 180 | 13229 | 154 |
| 2 | 3 | 20555 | 180 | 13241 | 156 |
| 2 | 4 | 30319 | 267 | 13253 | 161 |
| 3 | 2 | 16757 | 182 | 14319 | 173 |
| 3 | 3 | 21651 | 213 | 14337 | 166 |
| 3 | 4 | 31421 | 275 | 14355 | 177 |

## Installation

```bash
git clone [this repo](https://anonymous.4open.science/r/zk-PCD-B3FF/)
cd zk-pcd
cargo run
```

## Reference
[1] Kothapalli, Abhiram, Srinath Setty, and Ioanna Tzialla. "Nova: Recursive zero-knowledge arguments from folding schemes." Annual International Cryptology Conference. Cham: Springer Nature Switzerland, 2022.

[2] Eagen, Liam, and Ariel Gabizon. "Protogalaxy: Efficient protostar-style folding of multiple instances." Cryptology ePrint Archive (2023).
