import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Diagonal


namespace MatDecompFormal.Components.Properties

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

/--
`IsUpperTriangular A` 是一个谓词，判断矩阵 `A` 是否为上三角矩阵。

我们通过 `BlockTriangular` 来定义它。分块函数 `b` 我们选择 `FinEnum.equiv ι`，
它将索引 `ι` 映射到 `Fin (card ι)`。
因此，条件 `(equiv ι) j < (equiv ι) i` 意味着索引 `j` 在枚举顺序上先于 `i`。
`A i j = 0` 在 `j` 先于 `i` 时成立，这正是上三角矩阵的定义（即 `i > j → A i j = 0`）。
-/
def IsUpperTriangular (A : Matrix ι ι R) : Prop :=
  BlockTriangular A equiv

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
