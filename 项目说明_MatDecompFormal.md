# MatDecompFormal 项目说明（汇报版）

## 1. 项目定位与目标

`MatDecompFormal` 是一个基于 Lean 4 + Mathlib 的矩阵分解形式化项目，目标是把“矩阵分解存在性证明”从传统纸笔数学论证，转化为可机助检查、可复用、可扩展的形式化证明资产。

项目当前聚焦于以下主线：

- 构建一套通用的“变换 + 规约 + 归纳”证明框架，而不是只写某个分解的单点证明。
- 在该框架上实现并打通 `PLU` 分解的存在性证明（`Fin n` 版本与 `FinEnum` 泛化版本）。
- 积累可复用的组件库，包括三角性、置换性、分块代数、reindex 不变性等。

一句话总结：这是一个“以架构驱动的矩阵分解形式化工程”，不仅要证明结论，更要沉淀证明方法学。

---

## 2. 技术栈与工程配置

### 2.1 技术栈

- 语言与证明系统：Lean 4
- 数学库：Mathlib
- 构建工具：Lake

### 2.2 项目配置要点

`lakefile.toml` 中核心配置：

- 项目名：`MatDecompFormal`
- 依赖：`leanprover-community/mathlib`
- Lean 选项：禁用 `autoImplicit`，启用标准 linter 集

这意味着项目风格偏“显式类型驱动”，更适合长期维护与团队协作。

---

## 3. 总体架构设计

项目采用分层设计，核心目录如下：

- `MatDecompFormal/Abstractions`：抽象层（定义统一接口与组合子）
- `MatDecompFormal/Framework`：归纳引擎与宇宙层（把归纳原理工程化）
- `MatDecompFormal/Components`：可复用数学组件（性质、变换、规约、分块提升）
- `MatDecompFormal/Instances`：具体分解实例（当前主成果是 `PLU_new`）

对应关系可以概括为：

1. `Abstractions` 定义“做什么”（接口与语义）。
2. `Framework` 定义“怎么证明全域成立”（归纳机制）。
3. `Components` 定义“可复用积木”（代数与性质引理）。
4. `Instances` 定义“具体算法/定理落地”（如 PLU）。

这是典型的“高内聚、低耦合”形式化架构，便于后续扩展 QR、双对角化、秩标准型等主题。

---

## 4. 抽象层（Abstractions）核心设计

### 4.1 `DecompositionSchema`

通过 `Factors / property / equation` 三元组描述“一个分解是什么”，将“分解定义”与“分解存在性证明”解耦。

收益：

- 不同分解（PLU/QR/Rank form）可以复用统一表达框架。
- 上层定理陈述更稳定，底层算法可替换。

### 4.2 `Transformation`

`Transformation` 不是裸函数，而是“目标导向变换”：

- `Goal`：变换希望达到的状态
- `find`：若目标不满足，构造一个具体变换参数
- `find_spec`：证明该参数确实能达成目标

并提供了 `compose` 与 `compose_sequential` 组合子，支持把多个局部步骤拼成一个宏步骤。

### 4.3 `ReductionMethod`

封装“可切片问题”的代数规约三件套：

- `IsSliceable`：何时允许切片
- `slice`：提取子问题
- `reconstruct`：用子问题解回拼原问题
- `reconstruct_slice_eq`：回拼正确性

这是“归纳可执行化”的关键抽象。

### 4.4 `ReductionStrategy`

把 `Transformation` 与 `ReductionMethod` 绑定，并显式携带：

- 目标与可切片条件一致性
- 度量函数 `μ / μ_slice`
- 单调性与严格进展性证明

它是从“局部算法动作”走向“全局归纳可用”的桥梁。

---

## 5. 框架层（Framework）核心设计

### 5.1 宇宙建模：`FinRectUniverse` 与 `FinSqUniverse`

项目使用 Σ 类型表示“跨尺寸矩阵宇宙”，把维度直接放到对象层。

优势：

- 规约后维度变化在类型层显式可见。
- 避免大量隐式类型推断失败。
- 便于统一写跨尺寸归纳。

### 5.2 核心归纳引擎：`induction_by_reduction`

在通用宇宙 `X` 上进行良基归纳：

- 若落入基例集合，直接证明。
- 否则通过 `reach` 找到可规约状态，递归证明切片，再 `lift` 回来。

这把“数学归纳叙事”变成了可复用的工程接口。

### 5.3 子类型归纳：`induction_on_subtype` / `SubtypeInductionInstance`

真实分解往往只在“正维度矩阵”上做复杂步骤。框架支持：

- 全宇宙上陈述目标性质
- 子类型上执行核心规约逻辑
- 统一处理“零维/基例”与“正维归纳步”

`UniverseDecompositionFin.lean` 的扁平化实例结构大幅降低了实例接入成本。

---

## 6. 组件层（Components）能力清单

### 6.1 性质库（Properties）

- 置换矩阵：`IsPermutation` 及乘法封闭、swap 构造、分块对角等价
- 三角性质：`IsUpperTriangular` / `IsUnitLowerTriangular` 及分块保持
- Reindex 不变性：对置换、三角性等性质的传输引理
- Rank 正规形定义：`rankStdBlock` 与 `IsRankNormalForm`
- 行阶梯形定义：`RowEchelon`（当前仍含 `sorry`，详见第 9 节）

### 6.2 规约方法（Reductions）

- `SchurMethod`：主元可逆时做舒尔补规约
- `ZeroColumnMethod`：首列全零时走回退规约
- `SubmatrixMethod`：通用右下子矩阵规约
- `ReductionMethod.try_else`：将“主流程 + 回退流程”组合成统一规约器

### 6.3 变换（Transformations）

- `PivotTransform`：通过交换行制造非零主元
- `AnnihilateColumn` / `AnnihilateRow`：列/行消元基本变换
- `BidiagStepTransform`：组合变换接口（用于双对角化步骤）

### 6.4 分块提升库（BlockLifting）

提供 `fromBlocks` 乘法展开与通用提升器，核心作用是：

- 把“子问题分解已成立”提升到“原问题分解成立”
- 统一处理 reindex 前后、块矩阵代数细节

这部分是 `PLU` 中 `lift_from_slice` 证明可落地的关键。

---

## 7. 当前主成果：PLU 形式化证明链路

主实现文件：`MatDecompFormal/Instances/PLU_new.lean`

### 7.1 定理结果

项目当前已给出两个核心存在性定理：

- `exists_plu_decomposition_fin`：`Fin n` 索引方阵的 PLU 存在性
- `exists_plu_decomposition`：`FinEnum` 索引方阵的 PLU 存在性（由前者泛化得到）

### 7.2 证明结构（高层）

1. 定义 `PLU_Schema`（因子类型 + 性质 + 方程）。
2. 定义 `PLU_Reduction_fin = SchurMethod.try_else ZeroColumnMethod`。
3. 定义 `PLU_Transform_fin`，确保可切片条件可达成。
4. 定义 `PLU_Strategy_fin`，绑定度量与进展证明。
5. 证明 `transport`（沿策略关系传输 PLU 性质）。
6. 证明 `lift_from_slice`（子问题 PLU 提升到原问题）。
7. 组装 `PLU_Instance` 到 `SubtypeInductionInstance`。
8. 调用框架归纳定理，得到全维度存在性。
9. 通过 `orderIsoOfFinEnum` 与 reindex 不变性桥接到 `FinEnum` 世界。

### 7.3 方法价值

- 算法分支（主元可逆/不可逆）在规约层显式建模。
- 证明不依赖硬编码尺寸，能按宇宙归纳自动扩展。
- 给后续 QR、双对角化等实例提供模板。

---

## 8. 构建与验证状态

在当前代码快照下执行 `lake build`：

- 结果：构建成功（`Build completed successfully`）。
- 现象：存在较多 style 警告（主要是行宽超限）。
- 现象：`RowEchelon.lean` 中 `sorry` 产生警告，但不阻塞构建。

结论：项目主干可编译，核心 PLU 证明链路可通过构建验证。

---

## 9. 当前完成度与已知技术债

### 9.1 已完成（可汇报为“里程碑”）

- 通用抽象层已成型（Schema/Transformation/Reduction/Strategy）。
- 框架层归纳引擎已成型（含 subtype 归纳实例化接口）。
- PLU 主线已打通（`Fin` 与 `FinEnum` 两个层面）。
- 分块代数与性质传输有较完整支撑。

### 9.2 待完善（可汇报为“下一阶段任务”）

- `Components/Properties/RowEchelon.lean` 仍有 `sorry`。
- `Instances/QR.lean`、`Instances/Bidiag.lean` 当前为空文件。
- `Instances/temp/` 与 `Core(deprecated)/` 保留较多历史实验文件。
- 部分文件 style 警告较多（超长行）。

### 9.3 风险提示

- 若后续要做“零 `sorry` 可信性展示”，需优先清理 `RowEchelon`。
- 若要对外演示“多分解统一框架”，需补齐 QR/Bidiag 的一个最小可运行实例。

---

## 10. 对外汇报可用的项目亮点

可重点强调以下四点：

1. 理论贡献：提出了可复用的“变换-规约-归纳”形式化框架，而非单一结论证明。
2. 工程贡献：通过分层架构控制复杂度，证明资产可组合、可维护。
3. 结果贡献：已完成 PLU 分解存在性从 `Fin n` 到 `FinEnum` 的桥接证明。
4. 扩展潜力：QR、双对角化、秩标准型都可在同框架下接入。

---

## 11. 典型演示脚本（答辩/组会可直接用）

### 11.1 一分钟项目定位

“这个项目不是只证明一个 PLU 定理，而是抽象出一套可复用的矩阵分解形式化框架。我们先把框架打通，再把 PLU 全链路落地，验证框架有效，后续再扩展到 QR 和双对角化。”

### 11.2 三分钟技术路线

“我们把分解问题分成四层：抽象层定义 schema 和 strategy，框架层给出 subtype 良基归纳引擎，组件层提供规约和分块代数积木，实例层只需组装并证明 transport/lift/reach/base。PLU 使用 Schur + ZeroColumn 的 try-else 规约，最后通过 FinEnum 保序同构完成泛化。”

### 11.3 命令行演示

```bash
lake build
```

如需聚焦主成果文件，可展示：

```bash
sed -n '830,990p' MatDecompFormal/Instances/PLU_new.lean
```

---

## 12. 下一步建议（按优先级）

1. 清理 `RowEchelon` 中 `sorry`，完成基础性质闭环。
2. 在 `QR.lean` 或 `Bidiag.lean` 实现一个最小实例，验证框架跨算法可复用性。
3. 整理 `temp/` 与 `deprecated` 目录，形成“稳定主线 + 实验分支”结构。
4. 补充面向论文/汇报的基准示例（例如 2x2/3x3 的可读证明轨迹）。

---

## 13. 一页式结论（可作为汇报收尾）

`MatDecompFormal` 已完成从“框架设计”到“PLU 实例落地”的关键跨越。  
目前项目具备可编译、可展示、可扩展三项核心属性：  

- 可编译：主干 `lake build` 成功；
- 可展示：PLU 存在性定理链路完整；
- 可扩展：抽象与归纳基础设施已具备复用条件。  

下一阶段重点是补齐 QR/Bidiag 实例与清理遗留 `sorry`，将项目从“单实例成功”推进到“多实例统一框架”的成熟形态。
