import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Basis

namespace MatDecompFormal.Components.Properties

open FinEnum

/-!
# 秩标准型属性 (Rank Normal Form Property)

本文件定义了矩阵的“秩标准型”及其对应的属性。

1.  **`rankStdBlock`**: 一个构造函数，用于生成一个给定秩 `r` 的标准型矩阵。
    这个矩阵在左上角有一个 `r × r` 的单位矩阵，其余所有元素均为零。

2.  **`IsRankNormalForm`**: 一个谓词，用于判断一个给定的矩阵 `A` 是否等于
    某个秩 `r` 的标准型矩阵。

这个属性是秩分解 (Rank Factorization) 或史密斯标准型 (Smith Normal Form)
等分解算法的最终目标 `Goal`。它可以被用在 `DecompositionSchema` 的
`equation` 字段中，来描述分解的目标状态。
-/

section RankNormalForm

-- 声明所有定义共享的类型和类型类实例。
variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Zero R] [One R]

/--
`rankStdBlock r` 构造一个 `ι × κ` 的秩标准型矩阵，其有效秩为 `r`。

这个矩阵在由前 `r` 个行索引和前 `r` 个列索引构成的块中是一个单位矩阵，
而在其他位置全为零。索引的“前后”顺序由 `FinEnum.equiv` 给出。

*   `r`: 矩阵的秩。
-/
def rankStdBlock (r : ℕ) : Matrix ι κ R :=
  fun i j ↦ if  (equiv i).val < r
              ∧ (equiv j).val < r
              ∧ (equiv i).val = (equiv j).val
            then 1
            else 0

/--
`IsRankNormalForm` 是一个谓词，它判断一个矩阵 `A` 是否为某个秩 `r` 的标准型。

一个矩阵 `A` 被认为是秩标准型，如果存在一个秩 `r`（该秩不能超过矩阵的维度），
使得 `A` 精确地等于 `rankStdBlock r`。
-/
def IsRankNormalForm (A : Matrix ι κ R) : Prop :=
  ∃ r, r ≤ card ι ∧ r ≤ card κ ∧ A = rankStdBlock r

end RankNormalForm

end MatDecompFormal.Components.Properties
