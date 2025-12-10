import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import MatDecompFormal.Framework.FinEnum

namespace MatDecompFormal.Components.Properties

open Matrix FinEnum

/-!
# 三角矩阵属性 (Triangular Matrix Properties) - v3.0 (BlockTriangular-based)

本文件定义了上三角、下三角和单位下三角矩阵的属性。

这个版本的设计完全基于 Mathlib 的 `Matrix.BlockTriangular` 概念，
以确保与 Mathlib 生态系统的最大兼容性并避免类型类实例冲突。

`BlockTriangular A b` 意味着如果 `b j < b i`，则 `A i j = 0`。
我们通过使用由 `FinEnum` 提供的规范映射 `FinEnum.equiv : ι → Fin (card ι)`
作为分块函数 `b`，来定义通用的三角属性。
-/

section Triangular

-- 声明所有定义共享的类型和类型类实例。
variable {ι R : Type*} [FinEnum ι] [Zero R]

/--
`IsUpperTriangular A` 是一个谓词，判断矩阵 `A` 是否为上三角矩阵。

它被定义为相对于 `FinEnum.equiv` 映射下的 `BlockTriangular`。
-/
def IsUpperTriangular (A : Matrix ι ι R) : Prop :=
  BlockTriangular A (@equiv ι _)

/--
`IsLowerTriangular A` 是一个谓词，判断矩阵 `A` 是否为下三角矩阵。

一个矩阵是下三角的，当且仅当它的转置是上三角的。
-/
def IsLowerTriangular (A : Matrix ι ι R) : Prop :=
  IsUpperTriangular Aᵀ

/--
`IsUnitLowerTriangular A` 是一个谓词，判断矩阵 `A` 是否为一个单位下三角矩阵。
-/
def IsUnitLowerTriangular [One R] (A : Matrix ι ι R) : Prop :=
  IsLowerTriangular A ∧ A.diag = 1

-- ==================================================================
-- Basic Properties
-- ==================================================================

variable [One R] [DecidableEq ι]

/-- 单位矩阵 `1` 是上三角矩阵。 -/
lemma isUpperTriangular_one : IsUpperTriangular (1 : Matrix ι ι R) := by
  -- 证明现在变得非常直接，因为 Mathlib 已经为我们做好了工作。
  dsimp [IsUpperTriangular]
  -- `BlockTriangular.one` 是 Mathlib 中的标准引理。
  apply blockTriangular_one

/-- 单位矩阵 `1` 是下三角矩阵。 -/
lemma isLowerTriangular_one : IsLowerTriangular (1 : Matrix ι ι R) := by
  dsimp [IsLowerTriangular]
  rw [Matrix.transpose_one]
  exact isUpperTriangular_one

/-- 单位矩阵 `1` 是单位下三角矩阵。 -/
lemma isUnitLowerTriangular_one : IsUnitLowerTriangular (1 : Matrix ι ι R) := by
  constructor
  · exact isLowerTriangular_one
  · simp [Matrix.diag_one]

end Triangular

end MatDecompFormal.Components.Properties
