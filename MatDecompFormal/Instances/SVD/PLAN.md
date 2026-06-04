# SVD via the Rectangular Descent Framework

本目录用于推进奇异值分解（SVD）形式化：

```lean
A = U * S * Vᴴ
```

其中 `U`、`V` 是酉矩阵，`S` 是矩形对角且奇异值非负的矩阵。该目录已经存在于
`MatDecompFormal/Instances/SVD`，因此本次不再创建第二个同名目录；本文件作为
SVD 路线的落盘计划。

## 1. Target

优先完成复数版本：

```lean
theorem exists_svd
    {m n : Type*}
    [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    [LinearOrder m] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasSVD A
```

其中：

```lean
def HasSVD (A : Matrix m n ℂ) : Prop :=
  ∃ U : Matrix m m ℂ, ∃ V : Matrix n n ℂ, ∃ S : Matrix m n ℂ,
    IsUnitaryMatrix U ∧
    IsUnitaryMatrix V ∧
    IsRectangularDiagonalNonnegative S ∧
    A = U * S * Vᴴ
```

`RCLike` 推广作为后续目标。若 mathlib 的 Hermitian/normal 谱定理支持足够弱的标量
假设，再把复数版本中可复用的定义和引理推广。

## 2. Mandatory Framework Route

最终公开定理必须通过项目的矩形递降模板推出，而不是只给直接归纳证明：

```lean
RectStrategyData
mkRectSubtypeInductionInstanceFromStrategy
RectSubtypeInductionInstance.prove_for_matrix
```

公开定理链应形如：

```lean
exists_svd_framework
exists_svd_framework_oracle
exists_svd_framework_headBasisData
exists_svd
```

在谱理论、奇异向量、正交基补全等步骤尚未完全消解前，公开 theorem 名称必须诚实暴露
剩余 oracle/hook 条件。

## 3. Descent Shape

对非空行列索引的矩形矩阵 `A : Matrix m n ℂ`：

1. 从右 Gram 矩阵 `Aᴴ * A` 取得右奇异向量和奇异值 `σ ≥ 0`。
2. 构造右酉基 `V₁`，使选定右奇异向量成为 head column。
3. 对 `A v` 的方向构造左 head vector，并补全为左酉基 `U₁`。
4. 变换：

   ```lean
   B = U₁ᴴ * A * V₁
   ```

5. 证明 head-tail ready：

   ```lean
   B.toBlocks₁₁ = σ
   B.toBlocks₁₂ = 0
   B.toBlocks₂₁ = 0
   ```

6. 对 `B.toBlocks₂₂` 递归。
7. 通过 block-diagonal 酉扩张 lift 回 `B`。
8. 通过 two-sided unitary transport 回 `A`。

递归 measure 使用矩形框架的正维递降，语义上对应：

```lean
min (Fintype.card m) (Fintype.card n)
```

## 4. File Layout

```text
MatDecompFormal/Instances/SVD.lean
MatDecompFormal/Instances/SVD/Details.lean
MatDecompFormal/Instances/SVD/Strategy.lean
MatDecompFormal/Instances/SVD/Direct.lean
MatDecompFormal/Instances/SVD/Spectral.lean
MatDecompFormal/Instances/SVD/Existence.lean
MatDecompFormal/Instances/SVD/PLAN.md
```

文件职责：

- `Details.lean`: `HasSVD`、矩形对角非负谓词、空行/空列 base case。
- `Strategy.lean`: head-tail 索引、ready 谓词、two-sided unitary transform、slice。
- `Direct.lean`: transport hook 与 block lift hook。
- `Spectral.lean`: `Aᴴ * A` 谱理论、右奇异向量、左奇异向量、酉基补全。
- `Existence.lean`: 装配 `RectStrategyData`，暴露 framework-routed theorem。
- `SVD.lean`: 对外聚合 import。

## 5. Predicate and Data Contracts

矩形对角非负数据先用 data-oriented 表达，避免过早绑定行列索引之间的顺序关系：

```lean
structure RectangularDiagonalData (S : Matrix m n ℂ) where
  r : Type
  row : r → m
  col : r → n
  sigma : r → ℝ
  sigma_nonneg : ∀ k, 0 ≤ sigma k
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  entry_eq :
    ∀ i j,
      S i j =
        ∑ k : r, if row k = i ∧ col k = j then (sigma k : ℂ) else 0
```

ready 谓词应表达 head-tail 变换后的 block 形状：

```lean
def SVDBlockReady (A : Matrix m n ℂ) : Prop :=
  let A' := Matrix.reindex (headTailEquiv (α := m)) (headTailEquiv (α := n)) A
  ∃ σ : ℝ, 0 ≤ σ ∧
    A'.toBlocks₁₁ = (fun _ _ : Unit => (σ : ℂ)) ∧
    A'.toBlocks₁₂ = 0 ∧
    A'.toBlocks₂₁ = 0
```

## 6. Oracle Boundary

最小 one-step oracle：

```lean
structure SVDSimilarityOracle
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  U : Matrix m n ℂ → Matrix m m ℂ
  V : Matrix m n ℂ → Matrix n n ℂ
  unitary_U : ∀ A, IsUnitaryMatrix (U A)
  unitary_V : ∀ A, IsUnitaryMatrix (V A)
  descentReady : ∀ A, SVDDescentReady m n ((U A)ᴴ * A * (V A))
```

谱理论完成后，逐步将 oracle 消解为：

1. right Gram spectral data；
2. singular vector pair；
3. head basis data；
4. unconditional `exists_svd`。

## 7. Implementation Order

1. 固定 `Details.lean` 的目标谓词、矩形对角数据和空维 base case。
2. 固定 `Strategy.lean` 的矩形递降 skeleton。
3. 在 `Direct.lean` 证明 two-sided unitary transport。
4. 在 `Direct.lean` 证明 block-ready matrix 的 tail-SVD lift。
5. 在 `Existence.lean` 装配矩形框架，先得到 conditional theorem。
6. 在 `Spectral.lean` 用 `Aᴴ * A` 谱理论消解 one-step oracle。
7. 最后暴露无条件 `exists_svd`，并确认其证明路径经过矩形框架。

## 8. Acceptance Checks

```bash
lake build MatDecompFormal.Instances.SVD
lake build MatDecompFormal.Instances
printf 'import MatDecompFormal.Instances.SVD\n#check MatDecompFormal.Instances.exists_svd\n' | lake env lean --stdin
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/SVD -S
rg -n "prove_for_matrix|exists_svd_framework" MatDecompFormal/Instances/SVD -S
```

## 9. Current Status Notes

- 目录和最小文件结构已经存在。
- 本计划要求 SVD 保持 rectangular descent route。
- 若后续 Lean 文件已有进展，更新本节记录已完成 milestone；不要让 theorem 名称隐藏尚未消解的
  oracle/hook 条件。
