import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import MatDecompFormal.Framework.FinEnum

namespace MatDecompFormal.Components.Properties

open MatDecompFormal.Framework
open Matrix FinEnum

/-!
# 三角矩阵属性 (Triangular Matrix Properties)

本文件定义了上三角、下三角和单位下三角矩阵的属性。

这些定义是基于 Mathlib 的通用概念 `Matrix.BlockTriangular` 构建的。
`BlockTriangular A b` 意味着如果 `b j < b i`，则 `A i j = 0`。
通过选择合适的分块函数 `b`，我们可以精确地表达出我们需要的三角属性。
-/

section Triangular

-- 声明所有定义共享的类型和类型类实例。
variable {ι R : Type*} [FinEnum ι] [Zero R]

-- (最好将 Triangular.lean 的内容移到这里或一个更基础的文件)
def IsUpperTriangular {ι R} [Preorder ι] [Zero R] (A : Matrix ι ι R) : Prop :=
  ∀ ⦃i j⦄, j < i → A i j = 0

-- 步骤 3: 证明与 Mathlib 的连接
lemma isUpperTriangular_iff_blockTriangular {ι R} [FinEnum ι] [Zero R]
    (A : Matrix ι ι R) :
    IsUpperTriangular A ↔ BlockTriangular A (@equiv ι _) := by
  -- 这里的 IsUpperTriangular 会自动找到 Preorder.ofFinEnum 实例
  classical
  let _ : Preorder ι := Preorder.ofFinEnum ι
  rfl


/--
`IsLowerTriangular A` 是一个谓词，判断矩阵 `A` 是否为下三角矩阵。

一个矩阵是下三角的，当且仅当它的转置是上三角的。
这是定义下三角最简洁和最标准的方式。
-/
def IsLowerTriangular (A : Matrix ι ι R) : Prop :=
  IsUpperTriangular Aᵀ

/--
`IsUnitLowerTriangular A` 是一个谓词，判断矩阵 `A` 是否为一个单位下三角矩阵。

一个方阵 `A` 被称为单位下三角矩阵，如果：
1. 它是下三角的 (`IsLowerTriangular A`)。
2. 它的主对角线上的所有元素都为 1 (`A.diagonal = 1`)。
-/
def IsUnitLowerTriangular [One R] (A : Matrix ι ι R) : Prop :=
  IsLowerTriangular A ∧ A.diag = 1

end Triangular

end MatDecompFormal.Components.Properties
