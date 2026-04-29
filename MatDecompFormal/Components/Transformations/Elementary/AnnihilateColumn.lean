import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import MatDecompFormal.Abstractions.Transformation

namespace MatDecompFormal.Components.Transformations.Elementary

open Matrix

/-!
# Column Annihilation Transformation

This file defines `AnnihilateColumnTransform`, a `Transformation` instance implemented
in the `Fin n` world. Its goal is to use Gaussian elimination to zero all entries
below the pivot in the first column of the matrix.
-/

section GaussUtils

variable {n m : ℕ} {R : Type*} [Fintype (Fin n)] [DecidableEq (Fin n)] [Field R]
variable [NeZero n]

def gaussTrans (l : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  1 - vecMulVec l (Pi.single 0 1)

def gaussTransGL (l : Fin n → R) (hl : l 0 = 0) : GL (Fin n) R where
  val := gaussTrans l
  inv := 1 + vecMulVec l (Pi.single 0 1)
  val_inv := by simp [gaussTrans, mul_add, mul_one, sub_mul, one_mul, vecMulVec_mul_vecMulVec,
                      single_dotProduct, hl, mul_zero, zero_smul, sub_zero, sub_add_cancel]
  inv_val := by simp [gaussTrans, mul_sub, mul_one, add_mul, one_mul, vecMulVec_mul_vecMulVec,
                      single_dotProduct, hl, mul_zero, zero_smul, add_zero, add_sub_cancel_right]

lemma gaussTrans_mul_apply (A : Matrix (Fin n) (Fin m) R) (l : Fin n → R) (i : Fin n) (j : Fin m) :
    (gaussTrans l * A) i j = A i j - l i * A 0 j := by
  simp [gaussTrans]
  rw [Matrix.sub_mul, Matrix.one_mul, vecMulVec_mul]
  simp [vecMulVec]

end GaussUtils

/--
`AnnihilateColumnTransform` is a `Transformation` instance that uses Gaussian
transformations to eliminate all entries below the pivot `A 0 0` in the first column.

*   `h_pivot_nz`: a key assumption asserting that if the first column has a nonzero
    entry that must be eliminated, then the pivot `A 0 0` must be nonzero.
-/
noncomputable def AnnihilateColumnTransform (n m : ℕ) (R : Type*) [NeZero n] [NeZero m]
    [Field R] [DecidableEq R]
    (h_pivot_nz : ∀ (A : Matrix (Fin n) (Fin m) R), (∃ i, i ≠ 0 ∧ A i 0 ≠ 0) → A 0 0 ≠ 0) :
    Abstractions.Transformation (Matrix (Fin n) (Fin m) R) where
  T := Fin n → R
  Goal := fun A ↦ ∀ i, i ≠ 0 → A i 0 = 0
  decGoal := by infer_instance
  apply := fun l A ↦ gaussTrans l * A
  find := fun A h_goal_not_met ↦
    let h_exists_nonzero := by push_neg at h_goal_not_met; exact h_goal_not_met
    let pivot_nz := h_pivot_nz A h_exists_nonzero
    fun i ↦ if i = 0 then 0 else A i 0 / A 0 0
  find_spec := by
    intro A h_goal_not_met
    dsimp only; intro i hi_ne_zero
    let h_exists_nonzero := by push_neg at h_goal_not_met; exact h_goal_not_met
    let pivot_nz := h_pivot_nz A h_exists_nonzero
    let l := fun i' ↦ if i' = 0 then 0 else A i' 0 / A 0 0
    rw [gaussTrans_mul_apply A l i 0]
    have l_i_def : l i = A i 0 / A 0 0 := by simp [l, hi_ne_zero]
    rw [l_i_def]
    field_simp [pivot_nz]; rw [sub_self, mul_zero]


end MatDecompFormal.Components.Transformations.Elementary
