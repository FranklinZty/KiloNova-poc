# P0 开发计划（基于本地代码库重定基）

> 本文是 `PLAN.md` §3「P0：协议与依赖冻结（3–5 日）」的落地版本。
> `PLAN.md` 的 P0 假设基座是 **Sonobe**（`ethereum/sonobe@5ffe1fa9`）+ 新建
> `prototype/crates/{ccs-builder,kilonova-core,kilonova-pcd,kilonova-decider,bench-runner}`。
> 本地仓库的实际情况完全不同，因此 P0 必须重定基，否则「冻结规范」会冻结一个不存在的代码库。

---

## 0. 重定基：PLAN.md 的假设 vs 本地实际

| PLAN.md P0 的假设 | 本地实际 | 对 P0 的影响 |
|---|---|---|
| 基座是 Sonobe，需固定其提交 | 基座是 **Nova fork**（`Nova/` = `nova-snark` v0.42.0），无 Sonobe | P0「固定 Sonobe 提交」一项**作废**，替换为固定本仓 + 3 个未 pin 的 git 依赖 rev |
| 协议尚未实现，P2/P3 才写 CCS 与 folding | **已存在三套实现**，且约定互相矛盾 | P0 的核心工作从「推导规范」变成「**在三套已有实现中判定唯一规范，并冻结其约定**」 |
| 「运行既有 CCS、HyperNova、ProtoGalaxy、CycleFold 测试」 | 本地无这四者；只有 `kilonova` 自有测试 + arkworks | 替换为「运行 `nova-snark` kilonova 测试套件」——**实测结果是 6/6 端到端测试被 OOM 杀死**（见 §1.2） |
| family digest 构造顺序未定，「不得哈希含自身摘要的对象」 | **已解决**：`mod.rs:88-89` 用 `#[serde(skip)] OnceCell` | 该项从「待决定」改判为「已满足，只需写入 spec 存档」 |
| P0 是纯冻结阶段，不改代码 | 递归层当前**跑不起来** | 新增决策点：P0 是否允许最小可运行性修复（见 §5） |

### 0.1 本地三套「KiloNova folding」实现

| | `folding/` | `Nova/src/kilonova/` | `NIFS-circuit/` |
|---|---|---|---|
| 定位 | 通用 CCS 代数 PoC | **R1CS 特化的完整两曲线递归 IVC** | 约束数成本模型 |
| 生态 | arkworks / BLS12-381 | halo2curves / Pasta | 依赖 nova-snark + hyperplonk |
| 折叠 arity | 通用 μ/ν（测试用 μ=10,ν=15） | **硬编码 μ=ν=1（二元折叠）** | n/a |
| t, d | 通用 CCS | **硬编码 t=3, d=2** | 参数化 `deg` |
| 递归 | 无 | 有（`RecursiveSNARK`） | 有（但是**独立的旧 `NovaAugmentedCircuit`**） |
| 索引编码 | 稠密 `M'_j = Σρ^i M_{i,j}` | **direct（Pedersen commit 到 K 维 λ）+ span（λ 进公开实例）两种** | 无 |
| 错误通道 | `prove`/`verify` **无 `Result`**（`genericfolding.rs:372,535`），端点用 `assert_eq!`（`:596,:657`） | `Result<_, NovaError>` 全程 | `Result` |
| 序列化 | **完全不可序列化**：`Proof`（`genericfolding.rs:23-32`）只 derive `Debug`；`IOPProof` 缺 `CanonicalSerialize`；`serde` 在 `Cargo.toml:18` 声明但**零使用** | `NIFS`/`SumcheckProof`/`FoldedInstance` 均有 `Serialize+Deserialize` | 部分 |
| Statement 绑定 | **无**：`prove:379` / `verify:541` 均写着 `// TODO appends to transcript`，任何实例都不进 transcript | 有（但有漏洞，见 §3.3） | 有 |
| 负例测试 | **零** | 有：`nifs.rs:723`（篡改 proof）、`:738`（篡改 sigmas/taus/epsilons/thetas 各一）、`circuit/mod.rs:487`（篡改 hash）、`span/circuit/mod.rs`（篡改 predicate_id） | 少 |
| workspace | **不在** workspace（根 `Cargo.toml` = `["NIFS-circuit","Nova"]`），独立 `Cargo.lock` | 是 | 是 |

---

## 1. 现状实测（P0 的事实基线）

### 1.1 通过的测试都测了什么

`cargo test -p nova-snark --release --lib kilonova -- --test-threads=1`：
**16 通过 / 1 ignored / 其余被 SIGKILL**。

关键事实——**通过的 16 个测试全部不调用 `PublicParams::setup`**。它们的数据来自
`test_utils.rs:129 tiny_nonuniform_base_data`，而该函数（`:132-158`）构造的 shape 是：

```rust
R1CSShape::<E>::new(2, 2, 2,
  SparseMatrix::new(&vec![], 2, 5),   // ← A 全空
  SparseMatrix::new(&vec![], 2, 5),   // ← B 全空
  SparseMatrix::new(&vec![], 2, 5))   // ← C 全空
```

即 **nnz = 0**，且 `pp_digest = E::Scalar::from(42u64)`（`:186`）是硬编码常量，
witness / instance 全为零向量（`:161-177`）。

⇒ 这 16 个测试检验的是**插管与形状检查**（分配、命名空间、长度校验、哈希 gadget 的接线），
**不检验任何折叠代数**：`row_buckets`/`col_buckets` 全空 ⇒ `eval_matrix_folded`
（`circuit/r1cs.rs:263`）与 `eval_row_compression_predicate`（`:295`）在电路里产生 ~0 条约束。

`PublicParams::setup` 的调用点只有 6 处测试 + 1 个 `#[ignore]` benchmark：
`mod.rs:851, :902`；`span/mod.rs:905, :971, :1028, :1037`。
**这正好就是全部被杀死的 6 个测试。**

### 1.2 冒烟测试实测结果

| 配置 | 结果 |
|---|---|
| `cargo test -p nova-snark --lib kilonova`（debug，默认并行） | 26 tests：19 pass, 1 ignored, **6 SIGKILL** |
| 同上 `--release --test-threads=1` | 16 pass，随后 `kilonova::span::tests::test_ivc_nontrivial_nonuniform` **SIGKILL** |
| 单个 `kilonova::tests::test_ivc_nontrivial_nonuniform_bootstrap`（release，trace=[1]，**仅 1 步**） | 运行 >10 min 未完成；CPU 占用仅 **8.5%**（在等 page-in，不在算）；VSZ 464→472 GB 单调增长；被 kill 后**系统 swap 从 24.4 GB used 降到 9.9 GB used** |
| 单个同测试（debug） | 7m41s，RSS 0.4 GB，未完成 |

机器：**16 GB RAM**，swap total 25.6 GB、used 24.4 GB（**95.5% 满**），Pageins 1.52 亿。
PLAN.md §5.2 的内存上限是「物理内存 80%」= **12.8 GB**。

⇒ **结论（P0 头号 blocker）**：最小的端到端 IVC 测试（1 步、K=3、谓词是
`y=x³+x+5` / `y=x²+x+7` / `y=x⁴+9` 这种玩具电路）就把进程工作集推到
**≈16 GB RAM + ≈15 GB swap ≈ 30 GB**，被 macOS jetsam 杀死。
**递归层（`setup` 不动点 + 两曲线 IVC 链）当前状态是「未验证」，不是「已验证但慢」。**

### 1.3 内存爆炸的机制定位（代码级，全部已核对行号）

1. **`new_for_setup` ≡ `new`**：`relation.rs:70-76` 两者都调 `build(shapes, true)`；
   `build` 的 `with_runtime_tables=false` 分支（`:128-148`）是**死代码**，永不执行。
2. **桶表按 `2^s_max` / `2^s_prime_max` 预分配空 Vec**：`relation.rs:119-120`
   ```rust
   let mut row_buckets = core::array::from_fn(|_| vec![Vec::new(); 1usize << s_max]);
   let mut col_buckets = core::array::from_fn(|_| vec![Vec::new(); 1usize << s_prime_max]);
   ```
   这是 **每个 predicate × 每个矩阵（3 个）** 各一份 ⇒
   `K × 3 × (2^s_max + 2^s_prime_max) × 24 B` 的纯 Vec 头开销（还没算内容）。
   且 `s_max`/`s_prime_max` 取的是**所有 predicate 的最大值**（`:84-90`），小 predicate 也按最大尺寸分配。
3. **稀疏三元组存两份**：`relation.rs:108-112` 把 `shape.A/B/C` 的 `(row,col,val)`
   再 collect 成 `mats: [Vec<(usize,usize,Base)>;3]`，与 `SparseMatrix` 并存。
4. **`setup` 不动点循环每轮重建完整表**：`mod.rs:267-306` 每次迭代都
   `GlobalStructure::new_for_setup(&primary_shapes)`（K 个 predicate 的全量桶表）
   + `new_for_setup(&[shape_secondary])`；循环退出后 `:314-315` 再各建一次
   `GlobalStructure::new(...)`。⇒ 全量表至少被物化 **3 次**。
5. **电路规模自反馈**：
   - `circuit/r1cs.rs:340-359 eval_z` 逐 `z` 元素一条 `eq_eval_bits` + 一条乘法
     ⇒ **O(z_len_max) 约束**，每次 fold 调用 **2 次**（`epsilon_z`、`theta_z`）。
   - `circuit/r1cs.rs:263-293 eval_matrix_folded` 遍历 `0..structure.predicates.len()`
     ⇒ **O(K · nnz) 约束**，每次 fold 调用 **6 次**（sigmas×3、epsilons×3）。
   - primary augmented 的规模取决于 **secondary** structure 的维度，
     secondary augmented 又取决于 **primary** 的维度 ⇒ 两条曲线**互相喂大**。
6. **收敛判据只看维度**：`mod.rs:124-144 structure_signature` 返回
   `(num_vars_max, s_max, s_prime_max, predicates.len(), Vec<(num_cons,num_vars,num_io)>)`，
   **不比较矩阵内容**。

> P0 必须产出一个**测量**（不动点迭代次数、每轮 signature、峰值 RSS），
> 而不是继续推测。测量方法见 §3.7。

---

## 2. P0 交付物（对齐 PLAN.md:55，内容重定基）

| PLAN.md 要求 | 本地产出路径 | 内容重定基说明 |
|---|---|---|
| `docs/protocol-spec.md` | 同 | 冻结对象是**本地 `Nova/src/kilonova/` 的实现约定**，论文记号作为对照列 |
| `docs/claim-check-map.md` | 同 | 见 §3.4；必须含 5 个已定位缺口 G1–G5 |
| `versions.lock` | 同 | 无 Sonobe；改为冻结本仓 + 3 个未 pin 的 git 依赖 rev + rustc |
| `configs/common.toml` | 同 | 参数契约用**实测硬编码值**（t=3, d=2, μ=ν=1, num_io=2）而非 PLAN.md §5.1 的通用符号 |
| 依赖 smoke-test 报告 | **新增** `docs/baseline-status.md` | 承载 §1.2 实测数据 + §3.7 blocker 清单 |

---

## 3. 任务分解

### P0.1 判定唯一规范实现（0.5 日）

**决定：以 `Nova/src/kilonova/` 为 normative。**

依据（全部可核对）：唯一具备 `Result/NovaError` 错误通道、serde 可序列化、
真负例测试、完整两曲线递归、以及 **direct + span 两种索引编码**
（`span/` 子模块正是 PLAN.md §7.2 要的 KiloNova-Direct / KiloNova-Span ablation）。

- `folding/` **降级为「通用 CCS 参考实现」**：仅用于交叉验证代数恒等式（`compute_fx`/`compute_gy`
  与 `relation.rs:388-473` 的 `compute_cx`/`compute_cy` 是否同一多项式），**不进 P1+ 主线**。
  理由见 §0.1 表（不可序列化、无 statement 绑定、无负测试、`mu` 从攻击者数据推断
  `genericfolding.rs:91,202`、稠密化 fold `:307-310`、`.zip()` 静默截断 `:287-305`）。
- `NIFS-circuit/` 标记为**论文旧约束数图的来源**，按 PLAN.md §9 / P9 的禁令**不得复用其数字**。
  它有自己独立的 `NovaAugmentedCircuit`（`circuit/r1cs.rs:207/344/484/610/773`），
  **不使用** `Nova/src/kilonova/`，也未实现真正的 holographic NIFS。

**验收**：`docs/protocol-spec.md` 开头有 normative 声明；三个 crate 的角色写回 `AGENTS.md`。

---

### P0.2 记号冻结表（1 日）→ `docs/protocol-spec.md` §2

对应 PLAN.md:48「核对 CCS、ACCS 字段、两轮 sum-check 起始/终点式、次数界、随机挑战生成顺序及折叠输出」。

每行必须给出**冻结动作**，三选一：`{按论文改名} / {保留代码记号 + spec 声明等价映射} / {判定为 bug → blocker}`。

| # | 项 | 论文 | `Nova/src/kilonova/` 代码位置 | 冻结动作 |
|---|---|---|---|---|
| N1 | ACCS 实例字段 | `(C,u,io,r⃗_x,r⃗_y,v_1..v_t,v_z)` | `relation.rs:57-65 FoldedInstance{comm_W,comm_M,u,X,r_x,r_y,v}` | 等价映射：`v` 是 **t+1=4** 项扁平 vec，`v[0..3]=v_j`、`v[3]=v_z`（`relation.rs:315-329` 固定返回 4 项） |
| N2 | `z` 布局 | `(w ‖ u ‖ io)` | `relation.rs:226-228 z_from_folded` = `[W_proj, [u], X].concat()` | **已符合，冻结**。（`folding/src/genericfolding.rs:392-401` 是 `(u ‖ io ‖ w)`，**同时违反论文与 kilonova**，记入 folding 降级理由） |
| N3 | σ / τ 语义 | `σ_j = Σ M̃_j(r⃗_x*,y⃗)z̃(y⃗)`（**新**实例，无 eq）；`σ'_j = Σ eq(r⃗_y',y⃗)M̃'_j(r⃗_x*,y⃗)`（**运行**实例，带 eq） | `nifs.rs:475-477`：`sigmas = compute_sigmas(W1,U1,…)`（运行侧），`taus = compute_taus(predicate_id,&z_new,…)`（新侧） | **命名交叉**：代码 `sigmas` ≡ 论文 `σ'`，代码 `taus` ≡ 论文 `σ`。冻结为「保留代码名 + spec 给映射表」，不改代码（改名会波及 `circuit/r1cs.rs` 全部 `assert_equal` 命名空间） |
| N4 | ε / θ 语义 | `ε = z̃(r⃗_y*)` 标量；`θ_j = M̃_j(r⃗_x*,r⃗_y*)` | `relation.rs:315-329`：`epsilons = [M̃'_0,M̃'_1,M̃'_2, z̃'(r⃗_y*)]`，`thetas = [M̃_0,M̃_1,M̃_2, z̃(r⃗_y*)]` | **交叉 + 重打包成 t+1**：代码 `epsilons` ≡ 论文 `(θ', ε')`，代码 `thetas` ≡ 论文 `(θ, ε)`。同 N3 处理 |
| N5 | 折叠挑战名 | **η** | `nifs.rs:511 rho_base` / `:512 rho_scalar = base_as_scalar(rho_base)` | 冻结 `ρ ≡ η`，spec 声明 |
| N6 | **权重 1 落在哪一侧** | `x* = x + η·x'`，其中 `x` 是**新** CCCS（`u=1`）、`x'` 是**运行** ACCS ⇒ `u* = 1 + η·u'` | `relation.rs:629-658 FoldedInstance::fold`：`u = self.u + rho_base`（`self` = 运行侧），`comm_W + U2.comm_W*rho_scalar`（`U2` = 新侧乘 ρ） ⇒ **运行侧权重 1、新侧权重 ρ，与论文相反** | ⚠️ **必须在 P0 给出判定**：这是「等价的重标定约定」还是「bug」？<br>判据：检查 base case（`circuit/mod.rs:273-291 synthesize_base_case` → `relation.rs from_r1cs_instance_witness`）产出的 `u` 与 `comm_M` 是否自洽于「运行侧权重 1」这一约定；若自洽则冻结为**约定差异**（论文 η 与代码 ρ 互为倒数重标定），否则进 blocker |
| N7 | Q 项的 γ 幂次 | 修订版 `γ^{t+1}` | `nifs.rs:168 gamma_pows = powers(gamma,4)`，`:198` 用 `gamma_pows[3]` = **γ³ = γ^t** | 判定：`compute_sum_x`（`relation.rs:384-387`）与 `f(x⃗)`（`nifs.rs:194-199`）是否**同一多项式**。若两者都用 γ³ 则内部自洽 ⇒ 冻结为「代码用 γ^t，与论文修订版差一个 γ 因子，属重标定」；若不一致 ⇒ blocker（PLAN.md:60 明确要求「起始/终点等式可从同一多项式直接推导」） |
| N8 | δ 幂次分配 | `g(y⃗) = Σδ^j R_j + δ^{t+1}S + δ^{t+1}Σδ^j T_j` | `nifs.rs:237 delta_pows = powers(delta,7)`，`:255-262` 用 `[0..2]=T'`（运行侧矩阵）、`[3]=S'`（运行侧 z）、`[4..6]=R`（新侧） | **第三种约定**。同 N7 判据：与 `compute_sum_y`(`relation.rs:415-439`) / `compute_cy`(`:441-473`) 逐一比对幂次 |
| N9 | 挑战点顺序 | 未明确 | `nifs.rs:91-93 canonical_point(point) = point.iter().rev()`；电路侧 `circuit/r1cs.rs:728, :853` 同样 `.rev().collect()` | **冻结变量序约定**：sumcheck 第 `i` 轮绑定的挑战对应 `r_x` 的第 `s_max-1-i` 位。native 与 gadget 已一致（PLAN.md:36 的 DoD 满足），但必须在 spec 里写明，否则 `eq_table`(`nifs.rs:329`) 与 `bits_le` 的对应关系无法复核 |
| N10 | 次数界 | X 轮 `d+1`、Y 轮 `2` | `nifs.rs:171 eval_points = [0,1,2,3]`（deg 3 = d+1, d=2）；`:240 eval_points = [0,1,2]`（deg 2） | **已符合，冻结** |
| N11 | 参数泛化度 | 通用 CCS（任意 t,d,μ,ν） | `t=3`（`relation.rs:315-329` 返回 4 项）、`d=2`、`μ=ν=1`（`nifs.rs:556-564` 硬编码 `sigmas.len()!=3 \|\| epsilons.len()!=4` 等长度检查） | 冻结为 P0 参数契约（写入 `configs/common.toml`），泛化推迟到 P3 |
| N12 | ι 编码 | `C_{M,j} := PCS.Com(pp; M̃_j(X,Y))`——**矩阵 MLE 的多项式承诺** | `relation.rs:92-98`：`ck_index[j] = CE::setup(INDEX_LABELS[j], shapes.len())`（**key size = K**），`comm_M[j] = commit(ck_index[j], one_hot_e_id, ZERO)` ⇒ **Pedersen 承诺到 K 维 λ 向量**（index-span） | **有意偏离，非 bug**：论文 §「Breaking the Barrier of Index Folding」本身提出 index-span。spec 必须写明二者**不等价**，并记录论文的代价声明：省 O((μ+ν)t) 次非原生群运算、换 PCD verifier 本地 O(t\|F⃗\|) 次群运算，且论文自述「**it is not an asymptotic improvement for every parameter choice**」 |
| N13 | 谓词选择 φ | Construction 2 要求电路内计算 `idx' ← φ(z_loc, z⃗)` 并检查 `F_idx(z,z_loc,z⃗)=1` | **不存在**：`circuit/mod.rs:322-449` 的 `step_predicate_id`/`incoming_predicate_id` 是宿主常量；`:345-358` 仅用 `enforce(local_matches·1 = 1)` 把 witness 绑到该常量 | 缺口 **G4**，进 blocker 清单；PLAN.md P4「固定谓词族与调度」必须承接 |
| N14 | 链路哈希 | `H(PCD-link, fvk, idx, z_i, λ_i', x_i')` | `circuit/mod.rs:246-271 synthesize_hash_check` = `RO(pp_digest, i, z0, zi, U, ri, trace_digest)` | 差异：**多了** `i`、`z0`、`trace_digest`；**少了** `idx`（谓词 id）。判定是否 blocker：少 `idx` 意味着链路哈希不承诺当前步用的是哪个谓词——但 `trace_digest` 间接承诺了整条迹（`mod.rs:241-244`），需在 spec 里论证充分性 |
| N15 | 迹摘要 | 未规定具体构造 | `mod.rs:241-244`：`(trace + (id+1))² + (id+1)`；电路镜像 `circuit/mod.rs:87-103` | ⚠️ **代数哈希，非密码学**：T 步后是 id 的 **2^T 次**多项式。spec 必须写明它只提供「电路内可低成本校验的迹承诺」，**不构成抗碰撞承诺**；是否需要换成 Poseidon 是 P4 的决定 |
| N16 | ZK | **Theorem 3 已把 zero-knowledge 划掉**（`\zkNIFS`→`\NIFS`，只保留 perfect completeness + computational knowledge soundness） | 未实现 ZK | 见 §3.5 |

**验收**（对齐 PLAN.md:59-60）：N1–N16 每行有冻结动作；N6/N7/N8 三项必须有**明确判定结论**
（等价重标定 or blocker），因为它们直接决定「起始/终点等式是否可从同一多项式推导」。

---

### P0.3 Transcript 与域分离冻结（1 日）→ `docs/protocol-spec.md` §3 ⚠️ 安全 blocker

对应 PLAN.md:48「随机挑战生成顺序」。

**冻结的挑战派生顺序**（`nifs.rs:441-542 prove`，与 `:544-626 verify` 一致）：

```
absorb_inputs(:37-50)
  → γ        (:462)
  → α⃗[s_max] (:463-465)
  → sumcheck X（每轮：absorb 4 个 eval → squeeze r_i）(:155-222)
  → δ        (:483)
  → sumcheck Y（每轮：absorb 3 个 eval → squeeze r_i）(:224-293)
  → ρ_base   (:511)，ρ_scalar = base_as_scalar(ρ_base) (:512)
```

**缺口（必须处置）**：`nifs.rs:37-50 absorb_inputs` 实际只吸收

```rust
ro.absorb(scalar_as_base::<E>(*pp_digest));
ro.absorb(E::Base::from(predicate_id as u64));
U2.absorb_in_ro(ro);                                        // 新实例
for comm in &structure.predicate_commitments(predicate_id) { comm.absorb_in_ro(ro); }  // 新索引 ι
```

⇒ **运行侧实例 `U1`（`comm_W, comm_M, u, X, r_x, r_y, v`）与运行侧索引编码 ι' 从未进入 transcript。**
论文要求 `RO(HFS-1, ι, ι', x, x')`。

**后果**：`γ/α/δ/ρ` 不依赖运行实例 ⇒ 替换 `U1` 不改变任何挑战。这不是记号问题，
是**知识可靠性漏洞**（PLAN.md:63「未解决的正确性/安全组合问题列为阻塞项」）。

**注意**：`AllocatedFoldedInstance::absorb_in_ro`（`circuit/r1cs.rs:600-623`）**确实**吸收全部字段，
但它只被链路哈希（`circuit/mod.rs:246-271`）使用；NIFS transcript 在电路里的镜像是
`circuit/r1cs.rs:652-666`，它吸收 `params`、`predicate_id_num`、`u`、incoming `comm_M` 三点坐标
——**与 native 逐条对应，因此 native 与 gadget 是一致的（满足 PLAN.md:36），但一起错。**

**域分离现状**：

| 实现 | 域分离 |
|---|---|
| 论文 | `HFS-1` / `HFS-2` / `HFS-3` + sumcheck 内部 `SC` 四个前缀 |
| `Nova/src/kilonova/` | **无任何标签**，裸 Poseidon `absorb`/`squeeze` |
| `kilonova/span/nifs.rs` | `absorb_inputs(ro, pp_digest, predicate_id, U2)`——**连 `structure` 参数都没有**，不吸收 predicate 承诺 ⇒ 与 direct 变体的 transcript **不同** |
| `folding/` | Merlin 标签，但 `get_and_append_challenge_vectors(label,len)` 用**同一 label** 连续取 `len` 次；两个 sumcheck 复用相同标签 |

**动作**：
1. spec §3 写出冻结的逐条 transcript 表（含标签常量、字节编码、squeeze 位宽 = `NUM_CHALLENGE_BITS = 128`）。
2. 判定「U1/ι' 未吸收」：**P0 内修复** 还是 **列为 blocker 交给 P3**。
3. 若修复，**三处必须同步改且字节级一致**：
   `nifs.rs:37-50`（direct native）、`circuit/r1cs.rs:652-666`（direct gadget）、
   `span/nifs.rs absorb_inputs` + `span/circuit/r1cs.rs` 对应处（span 两侧）。
4. 新增**跨实现 transcript 向量测试**：同一输入下断言 direct-native / direct-gadget /
   span-native 派生出相同的 `(γ, α⃗, δ, ρ)`。这是 PLAN.md:36 唯一可执行的验收方式。

**验收**：spec §3 完整；transcript 向量测试存在且通过；三处 `absorb_inputs` 的差异被显式记录。

---

### P0.4 声明—检查者—代码位置表（1 日）→ `docs/claim-check-map.md`

对应 PLAN.md:49「明确哪些终端声明由下一轮承接，哪些必须由最终 decider 检查」。

每行格式：`声明 | 生产者 | 检查者 | 代码位置 | 状态`。已定位的检查点：

| 声明 | 生产者 | 检查者 | 代码位置 |
|---|---|---|---|
| sumcheck X 起始式 `sum_x` | `relation.rs:384-387 compute_sum_x` | `nifs.rs:295-327 sumcheck_verify`（首轮 `evals[0]+evals[1] != claim ⇒ Err`） | native + `circuit/r1cs.rs:689 sum_x_match` |
| sumcheck X 终点式 `c_x` | `relation.rs:388-413 compute_cx` | `nifs.rs:~589 claim_x != cx ⇒ Err` | + `circuit/r1cs.rs:799 claim_x_match_cx` |
| sumcheck Y 起始式 `sum_y` | `relation.rs:415-439 compute_sum_y` | 同 `sumcheck_verify` | + `circuit/r1cs.rs:819 sum_y_match` |
| sumcheck Y 终点式 `c_y` | `relation.rs:441-473 compute_cy` | `nifs.rs:~604 claim_y != cy ⇒ Err` | + `circuit/r1cs.rs:938 claim_y_match_cy` |
| 辅助声明形状（len 3/3/4/4，轮数 = s_max / s_prime_max） | prover | `nifs.rs:556-564` | ⚠️ `folding/` **无此检查**，且 `mu` 从攻击者数据推断（`genericfolding.rs:91,202`） |
| 挑战点与证明一致 | prover | `nifs.rs:~325 point != proof.point ⇒ Err` | + `circuit/r1cs.rs` 逐轮 `ry_point_match_{i}` / `rx_point_match_{i}` |
| σ/τ/ε/θ 与矩阵求值一致 | `relation.rs compute_sigmas/taus/epsilons/thetas` | `nifs.rs` 隐含（`c_x`/`c_y` 比对） | + `circuit/r1cs.rs:739-779, :855-909` 各 `assert_equal` |
| 折叠关系满足 | `FoldedInstance::fold`/`FoldedWitness::fold` | `relation.rs:475-516 is_sat` | ⚠️ **需要私有 `lambda_scalar` 与 `W`** |
| `comm_W` 打开正确 | — | `is_sat`（`CE::commit(ck,&W.W,&W.r_W) == U.comm_W`） | `relation.rs:~495` |
| `comm_M` 打开正确 | — | `is_sat`：`commit_index_coeffs(&W.lambda_scalar) == U.comm_M` | `relation.rs:500-505` |
| `v` 一致 | — | `is_sat`：`compute_v_from_coeffs(...) == U.v` | `relation.rs:~510` |
| 链路哈希（输入/输出） | 宿主 | `circuit/mod.rs:373 check_hash` + `:400-406 AllocatedBit::nor(check_hash,is_base_case)` 强制为 0 | — |
| 谓词 id 绑定 | 宿主常量 | `circuit/mod.rs:348-358`（`enforce local_matches·1=1`）；`circuit/r1cs.rs:642-649` | — |
| 迹摘要递推 | `mod.rs:241-244` | `circuit/mod.rs:87-103`（**必须与 native 逐行等价**） | — |
| 步数递增 / IO 数 = 2 | — | `circuit/mod.rs` `i_new = i+1` enforce；`mod.rs:320-322 num_io != 2 ⇒ Err` | — |

**`assert_equal` 是真约束、不是 panic**（复核时容易误判），`circuit/r1cs.rs:80-91`：
```rust
cs.enforce(|| "assert equal",
  |lc| lc + CS::one(),
  |lc| lc + a.get_variable() - b.get_variable(),
  |lc| lc);
```

#### 必须标红的 5 个缺口

| 编号 | 缺口 | 证据 | 影响 |
|---|---|---|---|
| **G1** | 电路内**没有任何约束**把 `self.M[j]` 绑定到 `commit(running_lambda.lambda)`。`circuit/r1cs.rs:942-951` 只做 `M[j] = self.M[j] + incoming_points[j]·ρ`（且用 `.unwrap()`），`self.M` 与 `running_lambda` 各自是独立 witness 输入。该绑定**只在 native `is_sat`（`relation.rs:500-505`）检查，而 `is_sat` 需要私有 `lambda_scalar`** | `circuit/r1cs.rs:628-983` 全程无此约束 | 递归内部 λ 是**未绑定的 witness**；折叠链的索引承诺一致性只在递归**外部**成立 |
| **G2** | `RecursiveSNARK::verify`（`mod.rs:633-740`）需要 `r_W_primary` / `r_W_secondary` / `l_w_secondary`，并对三者调 `is_sat` ⇒ **验证者持有私有 witness** | `mod.rs:350-372` 结构体字段；`verify` 末尾 `rayon::join` 三个 `is_sat` | 最终验证**既不公开也不简洁**。kilonova **没有 `CompressedSNARK`**；Spartan 的 `RelaxedR1CSSNARK` 只在 `test_utils.rs:647,:662` 用于**单步** secondary 电路 |
| **G3** | `predicate_trace: &[usize]` 是 **verify 的输入参数**，verify 内部重算 `expected_trace_*` 与之比对 | `mod.rs:633-740` | 验证者被**告知**了谓词迹，而非从证明中恢复。PLAN.md P6「多前驱 PCD」需要这一点被修掉 |
| **G4** | 无电路内 φ（见 N13） | `circuit/mod.rs:322-449` | 谓词选择不在证明的约束系统内 ⇒ 调度不由证明承诺 |
| **G5** | 论文 ι = `PCS.Com(M̃_j)`，代码 ι = Pedersen commit 到 K 维 λ（见 N12）；span 变体更进一步：`span/relation.rs FoldedInstance` 用 **`lambda: Vec<E::Base>` 取代 `comm_M`** ⇒ **公开实例大小 O(K)**，且 `span/relation.rs:366-386 reconstruct_folded_index_commitments` 在电路内做 **O(t·K) 次非原生群运算**，`span/relation.rs is_sat` **没有 `comm_M` 检查** | `span/relation.rs`、`span/circuit/r1cs.rs` | Direct 与 Span 的**安全性质不同**（Span 把索引编码整个公开）。PLAN.md §7.2 的 ablation 必须把这一点写进指标解释，否则两条曲线不可比 |

**验收**（对齐 PLAN.md:59）：每个声明有唯一生产者 + ≥1 检查者；G1–G5 每条要么有代码位置、
要么进 §3.7 blocker 清单并注明推迟到哪个 P。

---

### P0.5 非 ZK 边界 + family digest 构造序（0.5 日）

对应 PLAN.md:50「明确…安全模型及非 ZK 边界」与 :51「family digest 的构造顺序」。

**(a) 非 ZK 边界**

- 论文 **Theorem 3 已划掉 zero-knowledge**（只保留 perfect completeness + computational
  knowledge soundness；所有 `\zkNIFS` 已改名 `\NIFS`），并要求**常数深度**（无界深度需 straightline extractability）。
- 代码侧泄漏点：`epsilons[3]` / `thetas[3]` = `z̃(r⃗_y*)` **明文**放在 `NIFS` 里
  （`nifs.rs:27-34`，`Serialize` 导出）；`FoldedWitness` 整体随 `RecursiveSNARK` 保存。
- ⚠️ **`folding/README.md` 与论文直接矛盾**：仍称 KiloNova 是
  「a high-speed recursive **zkSNARK**」，具「**zero-knowledge**, which ensures privacy among
  different provers」，并列出 「Achieve zero knowledge (In Progress)」。
  同时它把 non-uniform circuits 标为 「(In Progress)」、Recursive Circuit for CCS 与
  KiloNova PCD Constructions 标为 「(TODO)」——**均已过时**（`Nova/src/kilonova/` 已实现）。

**动作**：spec §4 写明「**KiloNova PoC 不提供 ZK**；递归实例与 NIFS 证明在随机点泄漏 `z` 的求值」；
改写 `folding/README.md`；同步 `AGENTS.md`。

**(b) family digest 构造序 —— 判定为「已解决」**

PLAN.md:51 要求「不得哈希一个含自身摘要的未定义对象」。**本地代码已满足**：

- `mod.rs:88-89`：`#[serde(skip, default = "OnceCell::new")] digest: OnceCell<E1::Scalar>`
  ⇒ `pp.digest()`（`:334-340`，经 `DigestComputer`）序列化 `self` 时**跳过 digest 字段**，不自指。
- 构造序（`mod.rs:252-339 setup`）：
  `predicates` → K 个 primary augmented shape + 1 个 secondary shape（不动点循环 `:267-306`）
  → `ck_primary`/`ck_secondary`（`:308-313`，尺寸由 `max_commitment_key_size` 决定）
  → `GlobalStructure::new`（`:314-315`）→ `num_io != 2 ⇒ Err`（`:320-322`）
  → `pp` 结构体 → `let _ = pp.digest()`（`:337`）。

**动作**：spec §5 把上述顺序写成规范条文并存档为「已解决」。

**但遗留一个必须判定的问题**：`structure_signature`（`mod.rs:124-144`）**只比维度、不比矩阵内容**
⇒ 两组维度相同但矩阵不同的 predicate 会有相同 signature，不动点可能在**矩阵内容仍在变化时提前退出**。
判定：blocker，还是「维度决定 shape、shape 决定 digest，矩阵内容不参与 shape 因此无害」？
—— 注意 `PredicateIndex.comm_M`（`relation.rs:92-98`）依赖 `shapes.len()`，
而 `GlobalStructure` 本身会进 `pp` 被 digest，所以**矩阵内容确实影响 digest**，
提前退出会导致 digest 与最终 structure 不一致。**倾向判定为 blocker。**

---

### P0.6 依赖与版本冻结（0.5 日）→ `versions.lock` + `configs/common.toml`

对应 PLAN.md:52-53。实测事实：

| 项 | 实测 |
|---|---|
| 工具链 | `rustc 1.92.0 (ded5c06cf 2025-12-08)`；**无 `rust-toolchain.toml`**（根 / `Nova/` / `folding/` 均无）；`Nova/Cargo.toml` 声明 `rust-version = "1.79.0"` |
| workspace | 根 `Cargo.toml` = `workspace = { members = ["NIFS-circuit", "Nova"] }`；**`folding/` 不在内**，有独立 `Cargo.lock` |
| git 依赖未 pin | `folding/Cargo.toml`：`subroutines`/`transcript` = `{git="https://github.com/EspressoSystems/hyperplonk"}`（**无 `rev=`**）；`spartan2` = `{git="https://github.com/Microsoft/Spartan2"}`（**无 `rev=`**） |
| **同一依赖锁到两个 rev** | 根 `Cargo.lock`：hyperplonk 仓包 → **`2a3b55c97ad8a5d6627108a2e7def2aeccb7f3b9`**；`folding/Cargo.lock`：**`8698369edfe82bd6617a9609602380f21cabd1da`**。`spartan2` → `d78a5044b16ff6b60341785829539f5d0ba2961b`（仅 folding） |
| **`folding/` 离线不可构建** | `~/.cargo/git/checkouts/hyperplonk-a69c2e7135c3fc68/` 只含 **`2a3b55c`**；`8698369` 与 Spartan2 **完全不存在** |
| `.gitignore` | 根文件仅 3 行且**全部根锚定**：`/target`、`/NIFS-circuit/target`、`/Nova/target`；**无 `/folding/target`** ⇒ `git ls-files folding/target \| wc -l` = **5620 个构建产物已入库** |
| CI | `folding/.github/workflows/rust.yml` **不跑 build/test/clippy**，只发一条 Telegram 消息 |
| 空 feature | `folding/Cargo.toml`：`extensive_sanity_checks = [ ]`（no-op，注释声称「useful for debugging」） |
| 无关重依赖 | `folding/` 携带 `bellpepper`、`bellpepper-core`、`spartan2`、`pasta_curves`、`ark-pallas`、`group`，仅供 `bellpepper/mod.rs:47-67 test_bellpepper` 那个与 KiloNova **无关**的 Spartan2 demo（`x³+x+1=11`） |
| 安全参数 | `constants.rs`：`NUM_CHALLENGE_BITS = 128`、`NUM_HASH_BITS = 250`、`BN_LIMB_WIDTH = 64`、`BN_N_LIMBS = 4` |
| 曲线 | `test_utils.rs`：`PrimaryEngine = PallasEngine`、`SecondaryEngine = VestaEngine` |

**动作**：
1. P0.1 已把 `folding/` 降级 ⇒ **不修**其离线构建问题，只在 `versions.lock` 记录两个 rev
   与「`folding/` 离线不可构建、需联网 fetch」的状态。
2. 为主线加 `rust-toolchain.toml`（pin 到实测 1.92.0，或降到声明的 1.79.0 并实测通过）。
3. `.gitignore` 追加 `/folding/target`、`.DS_Store`、`.idea/`、`.vscode/`、`*.iml`
   （与 `AGENTS.md`「Files Marked for Deletion」一致）。
4. `git rm -r --cached folding/target`（**破坏性操作，需用户确认后单独执行**，不在 P0 自动做）。
5. `configs/common.toml` 写参数契约（用**实测硬编码值**，不用 PLAN.md §5.1 的通用符号）：

```toml
[protocol]
t = 3            # relation.rs:315-329 固定返回 t+1=4 项
d = 2            # nifs.rs:240 Y 轮 eval_points = [0,1,2]
mu = 1           # 二元折叠：running ACCS
nu = 1           # 二元折叠：incoming CCCS
num_io = 2       # mod.rs:320-322 强制
deg_x = 3        # nifs.rs:171 eval_points = [0,1,2,3] = d+1
deg_y = 2

[crypto]
curves = "Pallas/Vesta"     # PLAN.md §5.2 的 BN254/Grumpkin 切换条件「P0 测试通过」未满足 ⇒ 不切换
num_challenge_bits = 128    # constants.rs
num_hash_bits = 250
bn_limb_width = 64
bn_n_limbs = 4
pcs = "IPA (ipa_pc::EvaluationEngine)"
ro = "Poseidon, 无域分离标签"   # ← P0.3 待修

[machine]
ram_gb = 16
mem_cap_gb = 12.8          # PLAN.md §5.2：物理内存 80%
timeout_min = 30
test_threads = 1           # 必须：并行会因内存压力被 jetsam 杀
profile = "release"        # 必须：debug 下单个 bootstrap 测试 7m41s 未完成
```

**验收**：`versions.lock` 里**每个 git 依赖都有 rev**；`cargo build --release` 与
`cargo test --release --lib kilonova`（除 6 个 IVC 测试）在离线 + 锁定 rev 下可复现。

---

### P0.7 冒烟测试报告 + blocker 清单（0.5 日）→ `docs/baseline-status.md`

对应 PLAN.md:53、:62-63。

**固定命令**（写进报告与 CI）：
```bash
cargo test -p nova-snark --release --lib kilonova -- --test-threads=1
```
`--release` 与 `--test-threads=1` 都是**必需**的（依据见 §1.2）。
PLAN.md:62 要求「不以 README 或泛型签名代替运行证据」——本节即为运行证据。

**Blocker 清单**（P0 出口必须逐条给处置：`修复 / 降级 / 推迟到 P?`）：

| # | Blocker | 证据 | 严重度 |
|---|---|---|---|
| **B1** | **递归层完全未验证**：6/6 端到端 IVC 链测试被 OOM 杀死；最小用例（1 步、K=3、玩具谓词）工作集 ≈30 GB | §1.2；调用点仅 `mod.rs:851,902`、`span/mod.rs:905,971,1028,1037` | 🔴 阻断 P1+ 全部 |
| **B2** | 内存爆炸机制：桶表 `2^s_max`/`2^s'_max` × 3 × K；`new_for_setup ≡ new` 使不动点每轮重建全量表；无表分支是死代码 | `relation.rs:119-120`、`:70-76`、`:128-148`；`mod.rs:267-306`、`:314-315` | 🔴 |
| **B3** | 电路规模自反馈：`eval_z` O(z_len)×2 + `eval_matrix_folded` O(K·nnz)×6；两曲线互喂；`structure_signature` 只比维度 | `circuit/r1cs.rs:340-359`、`:263-293`；`mod.rs:124-144` | 🔴 |
| **B4** | `U1` 与 ι' 未进 transcript | `nifs.rs:37-50`；gadget 镜像 `circuit/r1cs.rs:652-666` | 🔴 安全 |
| **B5** | 电路内 `M[j]` 未绑定 `commit(λ)`（G1） | `circuit/r1cs.rs:942-951`；唯一检查在 `relation.rs:500-505`（需私有 witness） | 🔴 安全 |
| **B6** | 无 `CompressedSNARK`，`verify` 需私有 witness（G2） | `mod.rs:350-372`、`:633-740` | 🟠 推迟 P7 |
| **B7** | 无电路内 φ（G4）；`predicate_trace` 由验证者输入（G3） | `circuit/mod.rs:322-449`；`mod.rs:633-740` | 🟠 推迟 P4/P6 |
| **B8** | `nifs.rs:649 assert!(scale == one)` ⇒ NIFS 单元测试的两个 predicate **矩阵元素完全相同**，只有维度不同（4 cons/4 vars vs 8 cons/8 vars）⇒ 从未测试「系数不同的跨谓词折叠」 | `nifs.rs:638-704 tiny_r1cs` | 🟠 |
| **B9** | `relation.rs:753 test_cross_predicate_fold_sat` 算出 `sigmas` 后 `let _ = sigmas;`（`:788`）**丢弃**，且**从不对折叠结果调用 `is_sat`**；只断言 `lambda_scalar[1]==3` 与 `comm_M == commit_index_coeffs(lambda_scalar)`（`:811`）⇒ 测试名与测试内容不符 | `relation.rs:753-812` | 🟠 |
| **B10** | `test_utils.rs:132-158` 全用**空矩阵** + `pp_digest=42` + 全零 witness ⇒ 通过的 16 个测试不检验任何折叠代数 | `test_utils.rs:129-194` | 🔴 |
| **B11** | `folding/` 的 `--no-default-features` 串行路径**算错**：`espresso/multilinear_polynomial.rs:75` 用 `data[i]`（应为 `data[i<<1]`，并行分支 `:80` 是对的）。bug 来自上游、被忠实 vendored；`Cargo.toml:33 default=["parallel"]` 掩盖了它 | `folding/src/espresso/multilinear_polynomial.rs:69-84` | 🟡 folding 已降级 |
| **B12** | `folding/` 的 `.zip()` 静默截断（长度不匹配不报错）；`ccs/util.rs:65-68,88-91` 构造 `num_vars = s` 但 `evaluations.len() = 2^{s+s'}` 的 `DenseMultilinearExtension`，违反 ark-poly 不变量，仅靠 zip 截断「碰巧能跑」 | `genericfolding.rs:287-305`；`ccs/util.rs:65-68,88-91,126-128` | 🟡 |
| **B13** | 5620 个构建产物入库 | `git ls-files folding/target \| wc -l` | 🟢 易修 |
| **B14** | `folding/` MLE 变量序与上游 HyperPlonk **相反**（前 `s'` 个是列 `y`，后 `s` 个是行 `x`），`ccs/util.rs:120` `let r_xy = [&r_y[..], &r_x[..]].concat()`；而 kilonova 用 `canonical_point` 的 `.rev()`（N9）⇒ **两套实现的变量序约定不同**，交叉验证代数恒等式时会假阳性失败 | `folding/src/ccs/util.rs:120`；`nifs.rs:91-93` | 🟡 影响 P0.2 的交叉验证 |

---

## 4. P0 出口标准（对齐 PLAN.md:57-63）

| PLAN.md 验收条 | 本地判据 | 当前状态 |
|---|---|---|
| 每个公开/私有字段和挑战均有唯一生产者与消费者 | `docs/claim-check-map.md` 覆盖 `FoldedInstance`(7 字段) / `FoldedWitness`(5) / `NIFS`(6) / `SumcheckProof`(2) / `KiloNovaAugmentedCircuitInputs`(15) 全部字段 + 4 个挑战 (γ,α⃗,δ,ρ) | ❌ 待写 |
| 两轮 sum-check 起始/终点等式可从同一多项式直接推导 | N7/N8 给出判定结论；`compute_sum_x`↔`sumcheck_prove_x`、`compute_sum_y`↔`sumcheck_prove_y`、`compute_cx`/`compute_cy`↔终点式，四对逐一比对幂次 | ❌ 待判定 |
| 折叠输出可直接作为下一轮 ACCS 输入；**序列化测试向量固定** | `NIFS`/`FoldedInstance` 已有 serde ⇒ 需产出**固定的 bincode/JSON 测试向量**并入库 | ❌ 待写 |
| 关键依赖测试可重跑；未实现能力列为缺口，不以 README 或泛型签名代替运行证据 | `docs/baseline-status.md` 含 §1.2 实测数据；B1–B14 逐条处置 | ⚠️ 数据已有，文档待写 |
| 未解决的正确性/安全组合问题列为阻塞项 | B4/B5（安全）、B1/B2/B3（可运行性）、B8/B9/B10（测试有效性）必须显式列出 | ✅ 本文已列 |
| native verifier 与 gadget 同一规范序列化、transcript 顺序、次数界、域分离（PLAN.md:36） | P0.3 的**跨实现 transcript 向量测试** | ❌ 待写 |
| `cargo fmt --check` + lint + 测试通过（PLAN.md:34） | `Nova/src/lib.rs:1-4` 有 `#![deny(warnings, unused, future_incompatible, nonstandard_style, rust_2018_idioms)]` 与 `#![forbid(unsafe_code)]` ⇒ lint 门槛已由代码强制 | ⚠️ 待跑 |

**P0 不通过的判据**：B1（递归层未验证）若未在 P0 内降级为「已定位 + 有可执行修复路径 + 有测量数据」，
则 P0 出口不成立——因为 PLAN.md:61「折叠输出可直接作为下一轮 ACCS 输入」**无法在本地被任何测试证明**。

---

## 5. 建议插入 P0.5「可运行性修复」（需用户决策）

PLAN.md 的 P0 是**纯冻结阶段、不改代码**。但 B1/B2/B3 意味着
**P1（实验骨架）、P4（K-scan）、P5（真实递归链）、P9（正式实验）全部无法启动**——
在 16 GB 机器上连 1 步 K=3 的玩具链都跑不完。

**两个选项：**

**选项 A（推荐）：P0 内做最小可运行性修复，不改协议语义。** 只动内存/规模，不动 transcript、不动记号：
1. `relation.rs:74-76` 让 `new_for_setup` 走 `with_runtime_tables = false`（**激活 `:128-148` 的死代码分支**）
   ⇒ 不动点循环只比维度、不建桶表。这是**一行改动**，且 `structure_signature` 本来就只读维度。
2. `row_buckets`/`col_buckets` 从 `Vec<Vec<(usize,Base)>>`（`2^s` 个 Vec 头）改为
   **CSR**（`indptr: Vec<u32>` + `entries: Vec<(u32,Base)>`）⇒ 开销从 `O(2^s · 24 B)` 降到 `O(nnz · 8 B)`。
   注意 `SparseMatrix` 本身**已经是 CSR**（`indptr`/`indices`/`data`），桶表是在它之上又建了一层稠密索引。
3. `circuit/r1cs.rs:340-359 eval_z` 从 O(z_len) 逐项改为 **O(s') 的树形/Horner 求值**
   （`z̃(r⃗_y) = Σ_i z_i·eq(i, r⃗_y)` 可按 `r⃗_y` 的位逐层折叠，代价 O(z_len) → O(z_len) 但**约束数**从
   `2·z_len` 降到 `z_len`，且 `eq_eval_bits` 的 BTreeMap 缓存可跨调用共享）。
4. `circuit/r1cs.rs:263-293 eval_matrix_folded` 只对**非零 λ** 的 predicate 求和。
   ⚠️ 但折叠后 λ 是稠密的（`relation.rs:547-589`：`lambda[predicate_id] += ρ`，多步后所有 K 个都非零）
   ⇒ 这是 index-span 的**固有代价**，只能在 spec 里写明，不能靠这条优化消除。
   真正的解法是论文的 sparse-PCS 路线（PLAN.md 的 `reference-basis-decider` 之外的选项），属 P4/P5。

预估 **+3–5 日**，产出可运行的 1 步 / 3 步 / K∈{2,4,8} 基线，P1 才有起点。

**选项 B：严格照 PLAN.md 把 P0 限制在冻结，B1–B3 列为 blocker 交给 P1。**
预估 P0 = 5 日，但 P1 会立刻被 B1 卡住，实质是把同样的工作推到 P1 并让 P1 超期。

---

## 6. 工期与顺序

| 任务 | 工期 | 依赖 |
|---|---|---|
| P0.1 判定规范实现 | 0.5 日 | — |
| P0.2 记号冻结表 N1–N16 | 1 日 | P0.1 |
| P0.3 Transcript / 域分离冻结 + 向量测试 | 1 日 | P0.1 |
| P0.4 声明—检查者表 + G1–G5 | 1 日 | P0.2, P0.3 |
| P0.5 非 ZK 边界 + digest 构造序 | 0.5 日 | P0.1 |
| P0.6 依赖与版本冻结 | 0.5 日 | P0.1 |
| P0.7 冒烟报告 + blocker 处置 | 0.5 日 | P0.2–P0.6 |
| **小计** | **5 日** | 符合 PLAN.md 的 3–5 日 |
| （可选）P0.5 可运行性修复 | +3–5 日 | 需用户决策 |

建议执行顺序：**P0.1 → P0.7 的测量部分（先拿到不动点迭代次数与峰值内存）→ P0.2/P0.3 并行 → P0.4 → P0.5/P0.6 → P0.7 定稿**。
把测量提前，是因为 N6/N7/N8 的判定和 B2/B3 的处置都依赖「不动点到底收敛到多大」这个数字。

---

## 7. 需要用户决策的 4 个问题

1. **选项 A vs B**（§5）：P0 是否允许最小可运行性修复（`new_for_setup` 一行改动 + CSR 桶表）？
2. **B4（U1/ι' 未进 transcript）**：P0 内修复，还是列 blocker 交 P3？
   修复会同时动 4 处（direct native/gadget、span native/gadget），并使**所有既有测试向量失效**。
3. **N6（权重 1 落在运行侧而非新侧）**：接受为「ρ ≡ η⁻¹ 的重标定约定」并冻结，还是判定为 bug？
   这决定 base case 的 `u` 语义，影响 P5 的递归链正确性论证。
4. **`git rm -r --cached folding/target`（5620 个文件）+ `.gitignore` 修复**：是否现在执行？
   属破坏性 git 操作，需明确授权。
