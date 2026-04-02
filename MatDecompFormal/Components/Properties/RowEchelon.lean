import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Order.Basic
import MatDecompFormal.Framework.FinEnum

namespace MatDecompFormal.Components.Properties

open FinEnum Matrix MatDecompFormal.Framework

/-!
# 行阶梯形属性 (Row Echelon Form Property)

本文件定义了矩阵的“行阶梯形”辅助对象。当前文件仍未收口，
保留为内部模块，不进入公共导出面。
-/

section NonZeroIndex

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Zero R] [DecidableEq R]

/--
`NonZeroIndex A i` 计算矩阵 `A` 的第 `i` 行中第一个非零元素的列索引。

为了在通用的 `FinEnum` 类型 `κ` 上实现查找，我们利用 `κ` 与 `Fin (card κ)`
的等价关系，在 `Fin` 类型上执行 `Fin.find`，然后将结果映射回 `κ`。

*   `A`: 输入矩阵。
*   `i`: 行索引。
*   **返回**: `WithTop κ` 类型的值。如果找到主元，则为 `some j`；
    如果该行为全零行，则为 `⊤` (即 `none`)。
-/
noncomputable def NonZeroIndex (A : Matrix ι κ R) (i : ι) : WithTop κ :=
  let finEnum_κ : FinEnum κ := inferInstance
  let eκ : κ ≃ Fin (FinEnum.card κ) := finEnum_κ.equiv
  let row_vec : Fin (card κ) → R := fun j ↦ A i (eκ.symm j)
  let find_result : WithTop (Fin (card κ)) := Fin.find (fun j ↦ row_vec j ≠ 0)
  find_result.map eκ.symm

namespace NonZeroIndex

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Zero R] [DecidableEq R] (A : Matrix ι κ R)

lemma eq_top_iff {i} : NonZeroIndex A i = ⊤ ↔ ∀ j, A i j = 0 := by
  dsimp [NonZeroIndex]
  rw [WithTop.map_eq_top_iff]
  sorry

lemma ne_top_iff {i} : NonZeroIndex A i ≠ ⊤ ↔ ∃ j, NonZeroIndex A i = some j := sorry

lemma eq_some_iff {i} {j₀} :
    NonZeroIndex A i = some j₀ ↔
      (∀ j, (@equiv κ) j < (@equiv κ) j₀ → A i j = 0) ∧ A i j₀ ≠ 0 := by
  dsimp [NonZeroIndex]
  sorry

end NonZeroIndex

end NonZeroIndex

section IsRowEchelon

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Zero R] [DecidableEq R]

noncomputable local instance : LinearOrder ι := LinearOrder.ofFinEnum ι
noncomputable local instance : LinearOrder κ := LinearOrder.ofFinEnum κ

end IsRowEchelon

end MatDecompFormal.Components.Properties
