import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import MatDecompFormal.Abstractions.Transformation

namespace MatDecompFormal.Components.Transformations.Elementary

open Matrix

/-!
# 行消元变换 (Row Annihilation Transformation)

本文件定义了 `AnnihilateRowTransform`，这是一个在 `Fin n` 世界中实现的
`Transformation` 实例，其目标是通过右乘高斯变换将矩阵第一行主元之右的所有元素变为零。
-/

section GaussUtilsRight

variable {n m : ℕ} {R : Type*} [Fintype (Fin m)] [DecidableEq (Fin m)] [Field R]
variable [NeZero m]

def gaussTransRight (l : Fin m → R) : Matrix (Fin m) (Fin m) R :=
  1 - vecMulVec (Pi.single 0 1) l

def gaussTransRightGL (l : Fin m → R) (hl : l 0 = 0) : GL (Fin m) R where
  val := gaussTransRight l
  inv := 1 + vecMulVec (Pi.single 0 1) l
  val_inv := by simp [gaussTransRight, mul_add, mul_one, sub_mul, one_mul,
                      vecMulVec_mul_vecMulVec, hl, zero_smul, sub_zero, sub_add_cancel]
  inv_val := by simp [gaussTransRight, mul_sub, mul_one, add_mul, one_mul,
                      vecMulVec_mul_vecMulVec, hl, zero_smul, add_zero, add_sub_cancel_right]

lemma mul_gaussTransRight_apply (A : Matrix (Fin n) (Fin m) R)
    (l : Fin m → R) (i : Fin n) (j : Fin m) :
    (A * gaussTransRight l) i j = A i j - A i 0 * l j := by
  simp [gaussTransRight]
  rw [Matrix.mul_sub, Matrix.mul_one, mul_vecMulVec]
  simp [vecMulVec]

end GaussUtilsRight

/--
`AnnihilateRowTransform` 是一个 `Transformation` 实例，它通过右乘高斯变换
来消去第一行中主元 `A 0 0` 之右的所有元素。

*   `h_pivot_nz`: 一个关键的前提假设，断言如果第一行有非零元需要被消去，
    那么主元 `A 0 0` 必须是非零的。
-/
noncomputable def AnnihilateRowTransform (n m : ℕ) (R : Type*) [NeZero n] [NeZero m]
    [Field R] [DecidableEq R]
    (h_pivot_nz : ∀ (A : Matrix (Fin n) (Fin m) R), (∃ j, j ≠ 0 ∧ A 0 j ≠ 0) → A 0 0 ≠ 0) :
    Abstractions.Transformation (Matrix (Fin n) (Fin m) R) where
  T := Fin m → R
  Goal := fun A ↦ ∀ j, j ≠ 0 → A 0 j = 0
  decGoal := by infer_instance
  apply := fun l A ↦ A * gaussTransRight l
  find := fun A h_goal_not_met ↦
    let h_exists_nonzero := by push_neg at h_goal_not_met; exact h_goal_not_met
    let pivot_nz := h_pivot_nz A h_exists_nonzero
    fun j ↦ if j = 0 then 0 else A 0 j / A 0 0
  find_spec := by
    intro A h_goal_not_met
    dsimp only; intro j hj_ne_zero
    let h_exists_nonzero := by push_neg at h_goal_not_met; exact h_goal_not_met
    let pivot_nz := h_pivot_nz A h_exists_nonzero
    let l := fun j' ↦ if j' = 0 then 0 else A 0 j' / A 0 0
    rw [mul_gaussTransRight_apply A l 0 j]
    have l_j_def : l j = A 0 j / A 0 0 := by simp [l, hj_ne_zero]
    rw [l_j_def]
    field_simp [pivot_nz]; rw [sub_self, mul_zero]


end MatDecompFormal.Components.Transformations.Elementary
