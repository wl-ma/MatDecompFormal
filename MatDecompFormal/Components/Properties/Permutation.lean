import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Swap

namespace MatDecompFormal.Components.Properties

open Matrix

/-!
# 置换矩阵属性 (Permutation Matrix Property)

本文件定义了 `IsPermutation` 属性，并证明了其基本性质。
一个矩阵是置换矩阵，如果它等价于某个 `Equiv.Perm` 的矩阵表示。
-/

section IsPermutation

variable {ι R : Type*} [CommRing R]

/--
`IsPermutation A` 是一个谓词，判断矩阵 `A` 是否为一个置换矩阵。
-/
def IsPermutation [DecidableEq ι] (A : Matrix ι ι R) : Prop :=
  ∃ (σ : Equiv.Perm ι), A = (Equiv.toPEquiv σ).toMatrix

/--
由 `Equiv.swap` 构造的行（列）交换矩阵是一个置换矩阵。
-/
lemma isPermutation_swap [DecidableEq ι] (i j : ι) : IsPermutation (swap R i j) := by
  dsimp [IsPermutation]
  use (Equiv.swap i j)
  rfl

/--
置换矩阵的集合在矩阵乘法下是封闭的。
-/
@[simp]
lemma isPermutation_mul {A B : Matrix ι ι R} [FinEnum ι]
    (hA : IsPermutation A) (hB : IsPermutation B) : IsPermutation (A * B) := by
  rcases hA with ⟨σA, rfl⟩
  rcases hB with ⟨σB, rfl⟩
  dsimp [IsPermutation]
  use (σB * σA)
  rw [← PEquiv.toMatrix_trans, Equiv.Perm.mul_def, Equiv.toPEquiv_trans]


end IsPermutation

end MatDecompFormal.Components.Properties
