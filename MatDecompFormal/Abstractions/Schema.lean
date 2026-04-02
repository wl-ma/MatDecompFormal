import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Data.FinEnum

namespace MatDecompFormal.Abstractions

/-!
# 分解模式 (Decomposition Schema)

本文件明确区分项目中的两层分解表面：

* `DecompositionSchema` / `HasDecomposition`
  是 **internal canonical surface**。它们服务于 `Fin` 世界中的构造、规约、
  归纳和主证明，是项目内部的标准工作层。
* `DecompositionSchema'` / `HasDecomposition'`
  是 **external presentation surface**。它们服务于 `FinEnum` 索引下的对外结果
  表达，通常由 internal `_fin` 结果经由 reindex/bridge 得到。

这两层不是并行的主接口：`Fin` 层负责完成主要证明工作，`FinEnum` 层负责给出
统一的对外展示与最终结果包装。
-/

/--
`DecompositionSchema` 是项目的 **internal canonical schema surface**。

它面向 `Fin m × Fin n` 矩阵，承载项目内部的主要工作流：
构造、规约、归纳、以及 `_fin` 版本的主 existence theorem。

*   `m`, `n`: 矩阵的行数和列数。
*   `R`: 矩阵元素的环类型。
*   `Factors`: 分解后因子的类型。
*   `property`: 描述分解后因子所需满足的性质。
*   `equation`: 描述分解因子与原矩阵之间的代数关系。
-/
structure DecompositionSchema (m n : ℕ) (R : Type*) [CommRing R] where
  /-- 分解后各个因子的类型。例如 `Matrix (Fin m) (Fin m) R × Matrix (Fin m) (Fin n) R` 用于 QR。 -/
  Factors : Type*
  /-- 描述分解后因子所需满足的性质。 -/
  property : Factors → Prop
  /-- 描述分解因子与原矩阵之间的代数关系。 -/
  equation : Matrix (Fin m) (Fin n) R → Factors → Prop

/--
`HasDecomposition sch A` 是 internal canonical existence proposition。

它是项目统一存在性层在 `Fin` 内部证明世界中的最小落脚点：实例语义包装
（例如 `HasPLU_fin`、`HasQR_fin`）都应建立在它之上。
-/
def HasDecomposition {m n R} [CommRing R]
    (sch : DecompositionSchema m n R) (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ (factors : sch.Factors), sch.property factors ∧ sch.equation A factors

/--
`DecompositionSchema'` 是 **external presentation schema surface**。

它面向一般 `FinEnum` 索引的矩阵，用于表达 internal `_fin` 结果桥接后的
对外 schema 视图，而不是替代 `DecompositionSchema` 的第二套内部工作接口。

*   `ι`, `κ`: 矩阵的行和列索引类型，要求是有限且可枚举的 (`FinEnum`)。
*   `R`: 矩阵元素的环类型。
*   `Factors`: 分解后因子的类型。
*   `property`: 描述分解后因子所需满足的性质。
*   `equation`: 描述分解因子与原矩阵之间的代数关系。
-/
structure DecompositionSchema' (ι κ : Type*) (R : Type*)
    [FinEnum ι] [FinEnum κ] [CommRing R] where
  /-- 分解后各个因子的类型。例如 `Matrix ι ι R × Matrix ι κ R` 用于 QR 分解。 -/
  Factors : Type*
  /-- 描述分解后因子所需满足的性质。 -/
  property : Factors → Prop
  /-- 描述分解因子与原矩阵之间的代数关系。 -/
  equation : Matrix ι κ R → Factors → Prop

/--
`HasDecomposition' sch A` 是 external presentation existence proposition。

它用于对外陈述 `FinEnum` 索引下的分解存在性，通常应被理解为 internal
existence result 经过规范桥接后的展示层命题。
-/
def HasDecomposition' {ι κ R} [FinEnum ι] [FinEnum κ] [CommRing R]
    (sch : DecompositionSchema' ι κ R) (A : Matrix ι κ R) : Prop :=
  ∃ (factors : sch.Factors), sch.property factors ∧ sch.equation A factors

end MatDecompFormal.Abstractions
