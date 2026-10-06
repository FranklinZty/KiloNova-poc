# KiloNova 原型开发与实验执行计划

版本：2026-09-21。状态：待执行；本文不表示任何模块已经实现或任何性能结论已经验证。

## 1. 目标、依据与边界

目标是交付可独立验证的固定谓词族 non-uniform 递归证明原型，并通过公平、可复现的实验确定其优势及失效区间。实验不能代替安全证明，也不保证获得某个会议录用。

依据：

- 当前论文：`/Users/franklinzty/LatexProjects/Paper-KiloNova/KiloNova.tex`。
- 审稿与修订材料：同目录 `review/s&p27.md`、`review/crypto26.md`、`review/sp27_revision_checklist.md`、`review/sp27rebuttal.md`。
- 上一轮对 Sonobe 的源码检查。候选底座为 `dev` 提交 `5ffe1fa91fbbb7ecf68cf226416ce82e4ea0155e`，不是随时间变化的分支头；尚未完成本地编译验证。
- 审稿 checklist 仅用于定位风险，旧行号和勾选状态不能代替当前源码、论文及协议复核；rebuttal 的承诺不是已实现证据。

必须交付：

1. 原生 R1CS/CCS、ACCS 和 holographic folding 的正确性参考实现。
2. 固定谓词族的真实 non-uniform 递归链与至少二叉 PCD；公共状态和调度语义受约束。
3. 至少一个原生高阶 CCS 工作负载完成递归与终端验证，不把 R1CS 转 CCS 称为原生高阶实现。
4. 独立最终 verifier，以及与其公开 statement 绑定的压缩证明；明确当前不宣称零知识。
5. 同库消融、同库 baseline、外部 baseline 和可重现 artifact。

不纳入第一版：完整 zkVM、通用内存一致性、任意动态电路注册、通用 CCS DSL、GPU、任意 DAG 调度器、未经证明的 ZK 扩展。

## 2. 开发组织与统一完成定义

建议按 11 个子周期推进。下列工期是熟悉 Rust/arkworks/递归证明的开发者的工作日估计，不是承诺；协议重推、依赖修复和安全论证时间可能超出估计。P0 后根据实测重新排期，不以截止日期替代验收。

每个周期交付一个固定 commit/tag、一份验收报告和可执行测试命令。报告至少包含：目标、实现范围、测试配置、结果、已知限制、未解决问题和下一周期入口条件。协议改动必须更新版本号和测试向量。

统一完成标准：

- `cargo fmt --check`、适用模块的 lint、单元测试和集成测试通过；第三方已知警告单独登记。
- 正例通过，规定的篡改负例拒绝；不得通过关闭检查、缩短安全参数或删去递归步骤获得通过。
- native verifier 与 gadget 使用同一规范序列化、transcript 顺序、次数界及域分离。
- 每个性能数字可追溯到配置、源码版本、输入摘要与原始运行记录。
- 实现者之外的一名复核者检查验收证据；人手不足时安排独立复核轮次，不宣称完成独立安全审计。

## 3. 子周期与验收门槛

### P0：协议与依赖冻结（3–5 日）

开发目标：确定唯一可执行规范，消除论文记号与代码接口之间的歧义。

工作内容：

- 核对 CCS、ACCS 字段、两轮 sum-check 起始/终点式、次数界、随机挑战生成顺序及折叠输出。
- 明确哪些终端声明由下一轮承接，哪些必须由最终 decider 检查；建立“声明—检查者—代码位置”表。
- 明确固定族、公共状态、调度、递归基例、最终 statement、安全模型及非 ZK 边界。
- 决定 augmented predicate 如何纳入预处理，解决递归参数/电路尺寸与 family digest 的构造顺序；不得哈希一个含自身摘要的未定义对象。
- 固定 Sonobe 及 baseline 提交、Rust、依赖锁文件、曲线、transcript、PCS 和安全配置；检查依赖许可证与集成方式。
- 在候选提交运行既有 CCS、HyperNova、ProtoGalaxy、CycleFold 测试；失败时记录并选择经验证快照，不盲目追踪最新分支。

交付物：`docs/protocol-spec.md`、`docs/claim-check-map.md`、`versions.lock`、`configs/common.toml`、依赖 smoke-test 报告。

验收标准：

- 每个公开字段、私有字段和挑战均有唯一生产者与消费者。
- 两轮 sum-check 的起始/终点等式可从同一多项式直接推导。
- 折叠输出可直接作为下一轮 ACCS 输入；序列化测试向量固定。
- 关键依赖测试可重跑；未实现的能力列为缺口，不以 README 或泛型签名代替运行证据。
- 未解决的正确性/安全组合问题列为阻塞项；可继续隔离的底层实现，但不得进入最终性能宣称。

### P1：公共基础设施与可复现实验骨架（3–5 日；依赖 P0）

开发目标：所有方案使用可追踪的同一输入定义和指标口径。

工作内容：建立工作负载清单、确定性输入生成器、计时/RSS/序列化计数器、独立 verifier 命令、结果 schema 和配置校验器。

交付物：`bench-runner`、`workloads/`、`configs/`、`results/schema.json`、环境探测与参数校验工具。

验收标准：

- 相同 seed 和配置产生相同语义输入与执行结果；不同前端允许 witness 不同，但语义轨迹摘要一致。
- 记录实际线程数、实际矩阵尺寸和 witness 元素数，而非只记录请求值。
- 每条记录有 success/failure/timeout/OOM 状态；失败不会被静默排除。
- 空运行、合成负载及已知字节缓冲区可校验计时边界和大小统计。

### P2：原生 CCS 构造与 ACCS 参考检查器（5–8 日；依赖 P1）

开发目标：真正支持高阶约束，并建立协议之外的慢速正确性 oracle。

工作内容：

- 新增 `NativeCcsBuilder`：稀疏矩阵、重复索引 multiset、固定系数模板、公共/私有布局、padding 和合法性检查。
- 实现 R1CS、五次幂关系和可调度数关系；不要仅调用 R1CS-to-CCS 转换。
- 实现独立 ACCS 关系检查器和小尺寸显式矩阵/MLE 求值器。
- 固定矩阵/变量布局适配，特别检查 Sonobe 布局与论文布局的转换。

交付物：CCS builder、ACCS 类型、原生 witness generator、参考求值测试。

验收标准：

- 对 d=2、3、5、8、16 的关系，各至少 100 个确定性随机小实例，与朴素计算一致。
- 五次幂约束实际使用重复 multiset 表达，不含为降到二次而引入的中间乘法 witness；报告与等价 R1CS 的差异。
- witness 篡改、越界矩阵索引、错误维度和非规范编码被拒绝；退化零矩阵、边界尺寸有测试。
- CCS embedding/padding 前后语义一致，开销可统计。

### P3：KiloNova 原生 folding 与负例测试（7–12 日；依赖 P2）

开发目标：实现不带递归的完整 HFS，允许不同矩阵索引进入 folding。

工作内容：两轮 sum-check、Fiat–Shamir、ACCS 更新、witness commitment 更新；先实现二元，再实现论文所需的多输入接口。保留直接索引表示，作为后续消融基线。

交付物：native prover/verifier、fold 输出检查器、协议向量、fuzz/property tests。

验收标准：

- 至少两个同维度但不同矩阵的谓词连续交替 folding 100 步，每一步输出均由参考 ACCS 检查器接受。
- 对 mu/nu 的合法组合测试；输入数量、长度、次数不匹配时明确拒绝。
- prover/verifier 所有挑战逐字节一致；篡改 sum-check 系数、评估值、承诺、字段顺序或 transcript 标签导致拒绝，或在明确指定的终端关系检查处拒绝。
- 负例报告注明检测层级：不能错误要求 deferred relation 声明在裸 folding verifier 中立即被拒绝，也不能让其逃过最终检查。
- 不以测试替代知识可靠性证明；安全规范存在未解决缺口时保留阻塞标记。

### P4：固定谓词族与 index-span（5–8 日；依赖 P3）

开发目标：让 non-uniform 成为受认证的协议状态，而非宿主程序分支。

工作内容：

- 建立 `PredicateFamily`、稳定谓词 ID、族摘要和矩阵编码；第一版统一公共接口、padded 维度和 CCS 模板。
- 输入谓词 k 使用单位向量 e_k；按协议挑战更新 span，运行实例 span 不强制为 one-hot。
- 实现显式折叠矩阵路径和固定基础矩阵加权求值路径，交叉核对。
- 记录支持集合并集增长及预处理/内存开销；不假定折叠矩阵永远保持原始稀疏度。

交付物：族预处理器、span 类型及 gadget 草案、non-uniform 原生样例。

验收标准：

- K=1、2、4、16 的逐步矩阵求值与 span 加权求值一致。
- 伪造 ID、修改族顺序、替换矩阵、使用非 one-hot 新输入、篡改 span 均由对应完整检查路径拒绝。
- 至少两种谓词真正改变连接结构，不仅改变公开输入或常数。
- 如需不同模板嵌入，给出语义保持测试和实际扩展成本；不能只补零便宣称兼容。

### P5：真实 non-uniform 递归链（10–15 日；依赖 P4）

开发目标：执行轨迹、索引表示与 accumulator 在递归电路中绑定。

工作内容：

- 实现 HFS verifier gadget、augmented predicate 族及必要的曲线循环辅助证明。
- 约束 family digest、初始/当前状态、步数、当前 ID、前驱实例及输出实例的一致性。
- 第一版采用明确的确定性调度；若支持外部调度，明确是存在轨迹声明还是指定轨迹声明，并实现相应绑定。
- 打通原生高阶应用到 augmented CCS 的路径；递归验证逻辑可以由 R1CS 嵌入，但不能把应用高阶约束全部降阶后称为高阶端到端实现。

交付物：`prove-chain`、`verify-reference`、递归电路分项统计、两谓词和多谓词链样例。

验收标准：

- K=2、4，T=1、16、64 的合法链全部通过，至少一个 d=5 原生应用完成递归闭环。
- 错误初始状态、跳步、重复/错误计数、调换步骤、错误谓词选择、断开的前后状态均被拒绝。
- 报告应用、sum-check、hash、span、witness group ops、辅助曲线证明的绝对约束数，避免重复计数。
- 不得将每步独立证明串联或宿主检查称为递归；最终检查必须认证整条链。

### P6：多前驱 PCD 与工作负载闭环（7–12 日；依赖 P5）

开发目标：完成树形执行，隔离 arity 与谓词数量的影响。

工作内容：实现二叉合并，再支持 a=4、8；绑定叶任务/位置、前驱顺序、子任务范围、节点输出和根声明。固定虚拟叶规则，明确节点语义与递归基例。

交付物：`prove-tree`、任务树生成器、根 statement 格式、树形正确性报告。

验收标准：

- 固定 64 个真实叶任务，a=2、4、8 均得到同一目标计算结果；padding/内部节点工作单独报告。
- 重复叶、遗漏叶、跨任务拼接、非法次序及伪造前驱均被拒绝；若任务允许重复输入，也必须区分输入相同与位置重复。
- 顺序执行总 CPU 工作量与并行墙钟延迟分开统计；单线程主结果不混入并行收益。
- 多输入 folding 的 mu/nu 与 PCD arity 的对应关系写入每份配置，不默认 a=mu+nu。

### P7：独立最终验证与压缩（10–20 日；依赖 P5，树形覆盖依赖 P6）

开发目标：最终 verifier 只依赖声明的公共材料和 proof，不需要 prover 私有状态。

工作内容：

- 先完成参考 decider，再实现论文的稀疏求值、PCS opening 和终端递归绑定。
- 明确 witness commitment、完整 assignment commitment、矩阵评估点/值及最终应用输出的关联。
- 分离同态顶层矩阵承诺与 row/col/val 辅助编码；后者不可无证明地逐项线性折叠。
- 实现单独进程的 prover/verifier 文件接口，记录公共预处理材料和 SRS。
- 如先采用逐基础矩阵认证求值的中间路线，标记为 `reference-basis-decider`；报告 K 依赖，不能将其复杂度冒充论文优化版本。

交付物：`compress`、`verify-final`、公开 proof 格式、终端检查映射、实际通信量核算。

验收标准：

- 清空 prover 私有 checkpoint 后，独立 verifier 仍可验证链和树证明；不得从未声明缓存读取 witness。
- 修改 family、最终输出、步数/任务规模、span、评估点、评估值、opening 或递归输出绑定均拒绝。
- 分别测量预加载材料的 warm verifier 和从文件加载的 cold verifier；计入矩阵重构/虚拟承诺计算等工作。
- 从消息格式逐项核算 proof 字节数，与实际序列化一致；明确 K、N、矩阵维度依赖。
- 论文优化若尚未实现或证明未闭合，只验收中间版本，不将完整压缩周期标为完成。

### P8：baseline 接入与公平性验收（7–12 日；工具接入可在 P2 后开始）

开发目标：保留各方案原有协议语义，形成两类比较。

工作内容：

- 同库：HyperNova、ProtoGalaxy、KiloNova-Direct、KiloNova-Span，以及正确约束的 dispatcher 路线。
- 外部：SuperNova 候选实现 Arecibo；KZH-Fold 作者实现。固定实际可运行提交及可比能力，不先假定支持全部链/树/高阶功能。
- HyperNova 原生高阶作为优先对照；所核查 Sonobe ProtoGalaxy 具体实例绑定 R1CS，高阶扩展另列版本并重新测试，不视为现成功能。
- Dispatcher 需约束全部选择逻辑；不得按 witness 执行 Rust 分支后复用不匹配的 key。
- 增加 `KiloNova-Span + reference decider` 与优化 decider 的同配置对比。

交付物：适配器、能力矩阵、同语义测试向量、公平性审查表。

验收标准：

- 每个 baseline 对同一应用轨迹给出相同公共结果，且真实验证通过。
- 同库比较统一兼容的曲线/承诺/transcript/安全参数；外部无法统一之处逐项披露，不把跨后端比值解释为纯协议收益。
- 不把固定 K=1 的电路冒充 K>1 任务的功能对等 baseline。
- SuperNova 串行工作不称为同 arity multifolding；PCD 对照只使用确实实现的能力。
- 简单 dispatcher 不冒称具有对数开销的通用电路；若未实现后者，在论文中保留理论讨论及局限。
- 某方案只有 folding 或 gadget 时，仅进入对应层级表；缺失数据用 N/A 和理由，不填零。

### P9：冻结参数、正式实验与结论审计（5–10 日，加批量机器时间；依赖 P7/P8）

开发目标：得到带不确定性和完整成本的实测结果。

工作内容：执行第 5–8 节实验矩阵；先跑 pilot 冻结配置与资源上限，再正式采样；分析 break-even、内存和最终验证成本。

交付物：不可变 raw JSONL、汇总表、绘图脚本、每张图的配置清单、结论—证据映射。

验收标准：

- 每个正式配置至少 3 个输入 seed；每个 seed 2 次不计时 warmup 和 10 次正式运行。预先标记的昂贵配置可降为每 seed 5 次，不能看到结果后选择性降采样。
- 每次成功运行都执行对应验证；失败/超时/OOM 全量保留。
- 主要表报告中位数、IQR、样本数；主要 speedup 提供配对统计及按 seed 分组的 bootstrap 区间，不把同 seed 重复视为独立工作负载。
- 主结果覆盖有利及不利区间；不删去 K 较大、T 较小或小电路下的劣势结果。
- 正式数据不沿用旧论文图中的数值；任何已有数字必须重新运行或标注为历史结果且不混合统计。

### P10：artifact、论文对齐与复现（3–5 日；依赖 P9）

开发目标：外部读者可验证范围、重跑最小例子并生成主要结果。

交付物：README、依赖锁、最小演示、完整实验命令、原始数据、图源、已知限制、论文对应 commit。

验收标准：

- 干净环境可运行小规模链/树/高阶例子和篡改拒绝测试。
- 独立复现至少一组端到端、一组 K 扫描和一组高阶 CCS 结果；功能与字节数一致。时间中位数偏差超过 15% 时调查并记录环境差异，不据此自动否定正确性或改写数据。
- 论文不再混淆 private checkpoint、公开未压缩状态、最终 proof；所有图有单位和完整参数。
- README 明确 non-ZK、固定谓词族、支持的递归结构和未实现模块；不将测试通过称为安全审计通过。

## 4. 基础架构与版本策略

建议模块边界（为未来原型布局，不要求修改 Sonobe 全仓接口）：

```text
prototype/
  crates/ccs-builder/       # 原生 CCS、布局和嵌入
  crates/kilonova-core/     # ACCS、HFS、参考关系检查
  crates/kilonova-pcd/      # family、span、递归链/树
  crates/kilonova-decider/  # 参考及优化终端验证
  crates/bench-runner/      # 输入、适配器、统一采样
  configs/ workloads/ tests/ docs/
  results/raw/ results/summary/ plots/
```

Sonobe 改动保持为小型补丁或固定 fork；禁止实验途中自动更新依赖。外部 baseline 可通过独立进程适配，避免为统一依赖版本而重写密码协议。

来源入口：

- Sonobe：<https://github.com/ethereum/sonobe>。
- 候选 CCS：<https://github.com/ethereum/sonobe/blob/5ffe1fa91fbbb7ecf68cf226416ce82e4ea0155e/crates/primitives/src/arithmetizations/ccs/mod.rs>。
- 候选 HyperNova：<https://github.com/ethereum/sonobe/blob/5ffe1fa91fbbb7ecf68cf226416ce82e4ea0155e/crates/fs/src/hypernova/mod.rs>。
- 候选 ProtoGalaxy：<https://github.com/ethereum/sonobe/blob/5ffe1fa91fbbb7ecf68cf226416ce82e4ea0155e/crates/fs/src/protogalaxy/mod.rs>。
- SuperNova 实现候选：<https://github.com/lurk-lang/arecibo>。
- KZH-Fold 作者实现：<https://github.com/h-hafezi/kzh_fold>。

上述链接是选择依据，不是已通过本计划验收的声明。

## 5. 统一参数契约

### 5.1 符号与配置规则

| 参数 | 唯一定义 | 默认值与扫描 |
|---|---|---|
| K | 固定谓词族大小 | 默认 16；1、2、4、8、16、32、64、128 |
| m_app | 应用 CCS 的约束行数，不含递归 verifier | 合成默认 2^12；2^10、2^12、2^14、2^16 |
| n_app | 应用完整 assignment 列数，含常数与公共输入 | 合成参考 n_app=m_app；真实应用由合成得到 |
| w_app | 私有 witness 字段元素数 | 单独记录，不与 n_app 混用 |
| m_aug,n_aug | augmented predicate 实际维度 | 合成后记录原始值和 padded 值；不得强制各方案相等 |
| d | CCS 实际最大乘积次数 | R1CS=2；原生高阶主点=5；扫描 2、3、5、8、16 |
| t | 每个 CCS 的矩阵数 | R1CS=3；高阶按模板记录，不能一律写 3 |
| q | CCS 乘积项数 | 按模板记录；度数隔离实验固定模板族中其余可控因素 |
| N_j,N_total | 各矩阵非零数及总数 | 实测，同时记录折叠后支持集合大小 |
| s | 合成矩阵每行非零项数 | 默认 3；扫描 1、3、8；不适用于被语义约束的真实电路 |
| T | 链中真实应用步数 | 默认 256；1、16、64、256、1024 |
| a | PCD 节点前驱数 | 默认 2；2、4、8；与 mu/nu 分开 |
| mu,nu | 每次 folding 的 ACCS/CCS 输入数 | 按协议实例显式填写，不从 K 或 a 猜测 |
| L | 树中真实叶任务数 | 默认 64；规模实验 64、256、1024 |
| threads | 实际计算线程数 | 主结果 1；扩展实验 8 且机器允许 |
| seeds | 语义输入种子 | 默认 101、202、303；所有可比方案共享 |

应用实验优先“同语义”，原生微基准优先“同关系/尺寸”。不能为了匹配 m_aug 而让某方案执行更多应用工作。所有 padding、dummy 节点与额外 witness 单列。

### 5.2 密码学与机器参数

- 同库参考曲线循环采用 BN254/Grumpkin，前提是 P0 测试通过。若外部 baseline 不支持，另列平台组，不偷偷换曲线。
- 不把曲线名称或 128-bit challenge 等同于严格 128-bit 整体安全；记录曲线安全依据、挑战长度、sum-check 次数及重复递归下的 soundness 预算，由 P0 冻结。
- 同库 witness commitment 优先使用共同支持的配置；压缩 PCS 与 witness commitment 分开登记。KZH 保留自己的 PCS，不为统一后端改变被比较方案。
- transcript 的 hash、参数生成方法、域分离、挑战编码及隐藏开关全部固定。实例化不能为了性能采用不安全轮数。
- 主机使用同一 Linux 裸机或明确固定的 VM；不混合 WSL/macOS/Linux 时间数据。记录 CPU 型号、核心、内存、OS/kernel、频率策略、编译器和 release flags。
- 线程、CPU affinity 和 rayon/BLAS 等隐含线程数受控；关闭其他重负载。是否启用 turbo 固定并记录。
- P0 根据专用机器 RAM 冻结资源 cap，建议内存 cap 为物理 RAM 的 80%，默认单次超时 30 分钟。全方案同标准；更长 cap 的扩展实验单列。
- SRS/key 的生成及来源单独记录。不能把不兼容的 SRS 视作共享预处理；不得把 setup 成本混入某个方案而从另一个方案剔除。

## 6. 工作负载与最小实验矩阵

### W1：可控合成关系

分别生成可满足的稀疏 R1CS 和原生高阶 CCS。公开生成算法，禁止把有效约束全部做成零约束。矩阵支持模式包含共享、部分重叠和低重叠三类，测量实际重叠率，避免预设“完全不相交”在大 K 下不可实现。

用途：隔离 K、m_app、d、稀疏度、arity 对 native 和递归开销的影响。合成结果不外推为真实 VM 性能。

### W2：高阶算术/哈希

- 五次幂链或明确规范的 MinRoot-style 算术内核；若没有实现真实 MinRoot 参数和语义，称为五次幂算术内核。
- 使用经核定参数的 Poseidon 工作负载；原生 CCS 和 R1CS 路径证明相同输入输出及相同轮数。
- 高阶 d 扫描使用合成关系，不任意修改实际 hash 的安全参数制造度数实验。

用途：展示原生高阶支持和相同计算的实际代价。分别报告应用压缩与递归额外开销。

### W3：有限状态 non-uniform 应用

实现固定大小字段寄存器状态，包含加法、乘法、选择、常数更新、哈希更新等谓词；明确这不是完整 ISA/zkVM。谓词选择与状态或绑定的任务轨迹一致。

族分布：均匀、90% hot predicate、连续分块；另设异质电路尺寸约 1:4:16，记录真实尺寸及最大尺寸 padding 成本。分布对照在相同 K、T、输入生成规范下进行。

用途：检验真实调度、共享状态及谓词切换收益，而非只证明彼此无关的随机电路。

### W4：混合谓词任务树

叶执行固定算术/哈希任务；内部节点验证并合并子任务摘要和约定结果。位置、数量与任务标识受约束。不同 a 使用相同真实叶任务，报告内部节点数量差异。

用途：区分多前驱 PCD 总工作量与并行延迟。

### 必做实验组

| 组 | 变化项 | 固定项／目的 |
|---|---|---|
| E1 正确性 | W1–W4、边界参数、所有负例 | 不计性能，验证声明闭环 |
| E2 K 扫描 | K=1..128（上述离散值） | m_app=2^12、d=2、T=256，含最终 verifier 和内存 |
| E3 规模扫描 | m_app=2^10..2^16（上述离散值） | K=16、d=2、T=64；较短链控制成本，明确不同于默认 |
| E4 交叉点 | K={1,8,32,64,128} × m_app={2^10,2^12,2^14} | T=64，其余固定；不跑全笛卡尔积 |
| E5 高阶 | d={2,3,5,8,16} | 同一合成模板族与输入规模；另做 W2 同语义对照 |
| E6 arity | a={2,4,8}，可选与 d={2,5,8,16} 交叉 | L=64；注明各方案实际支持范围 |
| E7 轨迹长度 | T={1,16,64,256,1024} | K=16，固定每步工作；测总成本及摊销 |
| E8 应用 | W3 三种分布及异质版本、W4 | 比较功能对等系统；尺寸自然产生 |
| E9 消融 | Direct / Span / reference decider / optimized decider | 同输入、同参数，每次只改变一个目标因素 |

运行预算不足时，先保留 E1、E2、E5、E7、E8 和 E9 的代表点，再削减压力规模与并行扩展；不能删去最终验证、内存或高阶闭环来保留漂亮曲线。

## 7. 统一指标与计时边界

### 7.1 分层指标

| 层级 | 必报指标 | 说明 |
|---|---|---|
| Setup | SRS/setup、族预处理时间、峰值 RSS、prover/verifier 材料字节数 | 一次性成本单列，注明是否可缓存 |
| Native folding | witness 生成、矩阵运算、两轮 SC、commit/MSM、transcript、span、合计时间 | 细分之和与合计核对；无法分解的剩余项单列 |
| Recursive | 首步/稳态步时间、全链时间、两条曲线约束数及 witness 大小 | 曲线不同的约束数分别报，不能无说明合并 |
| PCD | 总证明 CPU 时间、顺序墙钟、并行墙钟、根验证时间 | 同时报告叶数和内部节点数 |
| Compression | 压缩时间、峰值 RSS、实际 proof 大小 | 不藏在 setup 或 recursion 之外 |
| Final verification | warm/cold 时间、峰值 RSS、公共材料与 statement 大小 | 包含实际执行的 K 相关工作 |
| End-to-end | witness+recursive+compression 时间及总 RSS | setup 分别给排除/摊销结果 |

串行闭环时间约定：`T_online = T_witness + T_recursive + T_compress`。native folding 的时间若已包含在 recursive 中，不再相加。时间细分若有重叠区间不得直接求和。并行墙钟直接测量，不能用阶段 CPU 总和代替。

另报告复用 B 次时 `T_amortized = T_online + T_family_setup/B`；B=1、10、100 作为透明情景，不把某个高 B 作为唯一结果。验证频率敏感性单独分析。

### 7.2 大小指标

必须分别序列化计量：

1. 私有 prover checkpoint（含 witness，如存在）。
2. 公开未压缩递归状态/证明。
3. 最终压缩 proof。
4. 公共 statement、family/verifier 材料、SRS。

主单位为 bytes，显示 KiB 时明确除以 1024。字段元素数量另报。长度 K 的 span 是 K 相关状态；若压缩后不显式传输，解释如何绑定以及成本转移到哪里。不得用“一个 accumulator”推出“全部字节数对 K 常数”。

### 7.3 内存与统计

- 单次试验在独立进程运行，测全流程 peak RSS；阶段 RSS 在独立阶段进程或可明确区分的测量中报告，不能把各阶段峰值相加。
- 描述 streaming 与缓存策略；若保留全部 T 步 witness，则计入内存，不宣称常数内存。
- 同配置方案随机化执行顺序；输入种子配对，记录 warmup 和 cold-start 边界。
- 主要表使用中位数、IQR；吞吐量注明分母为真实应用步/叶任务，不含 dummy。
- speedup 以同层级、同工作负载的配对样本计算，报告样本数和置信区间；跨 backend 的比值加显著标签。
- 超时/OOM 作为结果保留；不能用超时上限作为精确时间参与均值。

## 8. 原始记录与成果图表

每次运行至少包含：

```text
run_id, timestamp, experiment_id, config_hash
scheme, implementation_commit, dependency_lock_hash, protocol_version
machine_id, rust_version, build_flags, threads, security_profile
workload, input_digest, seed, repetition, warmup
K, T, L, a, mu, nu, d, t, q
m_app, n_app, w_app, m_aug, n_aug, padding, N_total
setup_ms, witness_ms, recursive_ms, compression_ms
verify_warm_ms, verify_cold_ms, peak_rss_bytes
checkpoint_bytes, public_state_bytes, proof_bytes, statement_bytes, vk_bytes
verification_ok, status, error_message
```

不适用字段使用 null 并说明，不填 0。细粒度分项、矩阵非零数和两条曲线计数可使用嵌套对象。配置和原始记录只追加；修复后生成新 run_id，不覆盖旧记录。

论文最少提供六组证据：

1. 功能范围与端到端成本表。
2. K 扫描：递归成本、最终验证、公开状态/材料大小、内存。
3. Direct-vs-Span 绝对约束与时间分解，而非只有百分比饼图。
4. 原生高阶 CCS 对照及等价 R1CS 的真实尺寸。
5. T 扫描与 setup/压缩摊销交叉点。
6. 应用链/树结果，分别呈现总工作与延迟。

图标题/图注必须列出固定参数、是否含 setup/compression、单位、样本数和实现版本。范围内某点失败也应显示或在相邻表解释。

## 9. 关键风险、降级路径与禁止结论

| 风险 | 处理与降级 | 禁止的处理 |
|---|---|---|
| 稀疏编码与顶层承诺绑定未闭合 | 停留在 reference decider，明确未完成优化压缩 | 直接线性折叠 row/col/val 并假定正确 |
| 高阶递归 frontend 不通 | 补共同模板嵌入；临时仅报告 native 高阶结果 | 把 R1CS-only 递归说成完整高阶实现 |
| Sonobe dev 不稳定 | 固定已验证快照，记录最小补丁 | 正式实验中不断换分支 |
| 外部 baseline 不支持同参数/能力 | 单列平台或层级，记录 N/A | 自行补成新协议却仍称原方案 |
| 大 K 的 span/最终 verifier 更慢 | 报告交叉点与适用范围 | 仅挑小 K 结果或隐藏最终验证 |
| 最大尺寸 padding 吞掉 non-uniform 收益 | 报告异质规模及 padding，后续才考虑分桶新设计 | 将补齐成本剔除 |
| 时间不足 | 缩减扫描点、并行扩展和次要优化 | 省略递归绑定、最终验证或负例 |

允许的结论示例：“在指定曲线、固定谓词族和参数范围内，index-span 降低了某项递归开销，但引入 K 相关状态和终端成本。”

禁止的结论：全面优于所有 non-uniform 方案、完整 zkVM、未经证明的零知识、未测量的 1000 倍单价优势、对任意 K 的常数总证明/验证成本。

## 10. 发布门槛与阶段状态

阶段门槛：

- G1（P0–P4）：原生代数与不同索引 folding 正确；只能发布 native 原型结果。
- G2（P5–P6）：真实 non-uniform 递归链/树及高阶闭环；可发布递归层实验，但不得把参考检查当压缩 SNARK。
- G3（P7–P8）：独立最终验证、声明绑定及公平 baseline 完成；可进入完整正式实验。
- G4（P9–P10）：原始数据、统计、复现、论文范围对齐完成；达到研究 artifact 发布标准。

初始状态：P0–P10 均为未开始。只有验收报告中的命令、结果和版本可支持状态变更。本计划文件的创建不代表原型代码、测试或实验已经执行。
