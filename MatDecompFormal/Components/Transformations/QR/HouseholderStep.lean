import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace MatDecompFormal.Components.Transformations.QR.HouseholderStep

open Matrix

/-!
# Householder Step For QR

This file contains the QR-specific internal Householder step on square real
matrices of size `(k + 1)`.

Within the current repository structure, this module is the transformation-level
component consumed by the completed QR instance pipeline:

* only `ℝ`;
* only the internal `Fin` layer;
* only the first-column Householder step.

It deliberately stays under `Components.Transformations.QR`: this file does not
formalize a reusable general Householder library, but the specific step shape
and sliceability interface consumed by the QR instance. Reduction, lifting,
transport, and the external bridge remain in the QR instance modules that
package this step into the full QR existence line.
-/

section RealHouseholder

variable {k : ℕ}

/-- The QR first-column sliceability goal on `(k+1)×(k+1)` real matrices. -/
def FirstColumnSliceable (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : Prop :=
  ∀ i, i ≠ 0 → A i 0 = 0

/-- The first column of a square matrix, viewed as a vector. -/
def firstColumn (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : Fin (k + 1) → ℝ :=
  fun i => A i 0

/-- The first standard basis vector in `ℝ^(k+1)`. -/
def e₀ : Fin (k + 1) → ℝ :=
  Pi.single 0 1

/-- Squared Euclidean norm of the first column. -/
def firstColumnSqNorm (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : ℝ :=
  firstColumn A ⬝ᵥ firstColumn A

/-- Euclidean norm of the first column. -/
noncomputable def firstColumnNorm (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : ℝ :=
  Real.sqrt (firstColumnSqNorm A)

/--
The Householder direction used by the QR first step.

We use the classical `x - ‖x‖ e₀` choice as the canonical internal direction
for the current QR step interface.
-/
noncomputable def direction (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : Fin (k + 1) → ℝ :=
  firstColumn A - firstColumnNorm A • e₀

/-- The scalar denominator `uᵀu` attached to the Householder direction. -/
noncomputable def directionDenom (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : ℝ :=
  direction A ⬝ᵥ direction A

/--
The Householder reflector candidate attached to the first column of `A`.

When the direction vanishes, we fall back to the identity matrix. This keeps the
construction total and keeps the QR step interface uniform.
-/
noncomputable def reflector (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  if _h : directionDenom A = 0 then
    1
  else
    1 - (2 / directionDenom A) • vecMulVec (direction A) (direction A)

/-- Apply the Householder reflector candidate on the left. -/
noncomputable def apply (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  reflector A * A

/-- The rank-one matrix built from the Householder direction. -/
noncomputable def directionOuter (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  vecMulVec (direction A) (direction A)

lemma directionOuter_transpose
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    (directionOuter A)ᵀ = directionOuter A := by
  simp [directionOuter, transpose_vecMulVec]

lemma directionOuter_mul_directionOuter
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    directionOuter A * directionOuter A = directionDenom A • directionOuter A := by
  rw [directionOuter, vecMulVec_mul_vecMulVec]
  simp [directionDenom, vecMulVec_smul]

lemma reflector_transpose
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    (reflector A)ᵀ = reflector A := by
  rw [reflector]
  split_ifs with hA
  · simp
  · simp [transpose_vecMulVec]

lemma reflector_mul_reflector
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    reflector A * reflector A = 1 := by
  by_cases hA : directionDenom A = 0
  · simp [reflector, hA]
  · let c : ℝ := 2 / directionDenom A
    let P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := directionOuter A
    have hP2 : P * P = directionDenom A • P := by
      simpa [P] using directionOuter_mul_directionOuter A
    have h_reflector : reflector A = 1 - c • P := by
      simp [reflector, hA, c, P, directionOuter]
    calc
      reflector A * reflector A = (1 - c • P) * (1 - c • P) := by
        rw [h_reflector]
      (1 - c • P) * (1 - c • P)
          = 1 - c • P - c • P + c • c • (P * P) := by
              simp [sub_eq_add_neg, add_mul, mul_add]
              abel_nf
      _ = 1 - c • P - c • P + (c ^ 2 * directionDenom A) • P := by
            rw [hP2]
            simp [pow_two, smul_smul, mul_assoc]
      _ = 1 := by
            have hc : c ^ 2 * directionDenom A = 2 * c := by
              dsimp [c]
              field_simp [hA]
            rw [hc]
            ext i j
            simp [sub_eq_add_neg, two_mul, add_left_comm, add_comm]
            ring

lemma reflector_orthogonal
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    (reflector A)ᵀ * reflector A = 1 := by
  rw [reflector_transpose, reflector_mul_reflector]

lemma e₀_dot_firstColumn (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    e₀ ⬝ᵥ firstColumn A = A 0 0 := by
  classical
  rw [dotProduct, Finset.sum_eq_single 0]
  · simp [e₀, firstColumn]
  · intro i _ hi
    simp [e₀, hi, firstColumn]
  · simp [e₀, firstColumn]

lemma firstColumn_dot_e₀ (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    firstColumn A ⬝ᵥ e₀ = A 0 0 := by
  rw [dotProduct_comm]
  exact e₀_dot_firstColumn A

lemma direction_dot_firstColumn
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    direction A ⬝ᵥ firstColumn A =
      firstColumnSqNorm A - firstColumnNorm A * A 0 0 := by
  rw [direction, sub_dotProduct, smul_dotProduct]
  simp [firstColumnSqNorm, e₀_dot_firstColumn]

lemma firstColumnSqNorm_nonneg (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    0 ≤ firstColumnSqNorm A := by
  classical
  unfold firstColumnSqNorm
  rw [dotProduct]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

lemma firstColumnNorm_sq
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    firstColumnNorm A ^ 2 = firstColumnSqNorm A := by
  simpa [pow_two, firstColumnNorm] using Real.sq_sqrt (firstColumnSqNorm_nonneg A)

lemma directionDenom_eq_two_mul
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    directionDenom A =
      2 * (firstColumnSqNorm A - firstColumnNorm A * A 0 0) := by
  have he0 : e₀ (k := k) ⬝ᵥ e₀ (k := k) = 1 := by
    classical
    rw [dotProduct, Finset.sum_eq_single 0]
    · simp [e₀]
    · intro i _ hi
      simp [e₀, hi]
    · simp [e₀]
  have hnorm : firstColumnNorm A * firstColumnNorm A = firstColumnSqNorm A := by
    simpa [pow_two] using firstColumnNorm_sq A
  rw [directionDenom, direction, sub_dotProduct, dotProduct_sub, smul_dotProduct]
  rw [dotProduct_sub, dotProduct_smul]
  rw [firstColumn_dot_e₀, e₀_dot_firstColumn, dotProduct_smul, he0]
  ring_nf
  rw [show firstColumn A ⬝ᵥ firstColumn A = firstColumnSqNorm A by rfl]
  rw [hnorm.symm]
  simp [smul_eq_mul]
  ring_nf

lemma two_mul_direction_dot_firstColumn
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    2 * (direction A ⬝ᵥ firstColumn A) = directionDenom A := by
  rw [direction_dot_firstColumn, directionDenom_eq_two_mul]

lemma direction_eq_zero_of_directionDenom_eq_zero
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : directionDenom A = 0) :
    direction A = 0 := by
  rw [directionDenom] at hA
  exact (dotProduct_self_eq_zero.mp hA)

lemma firstColumn_eq_norm_smul_e₀_of_directionDenom_eq_zero
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : directionDenom A = 0) :
    firstColumn A = firstColumnNorm A • e₀ := by
  have hdir : direction A = 0 := direction_eq_zero_of_directionDenom_eq_zero A hA
  rw [direction, sub_eq_zero] at hdir
  exact hdir

lemma sliceable_of_firstColumn_eq_smul_e₀
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (c : ℝ)
    (hA : firstColumn A = c • e₀) :
    FirstColumnSliceable A := by
  intro i hi
  have hentry := congrFun hA i
  simp [firstColumn, e₀, hi] at hentry
  exact hentry

lemma firstColumn_apply_eq_mulVec
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    firstColumn (apply A) = reflector A *ᵥ firstColumn A := by
  funext i
  simp [firstColumn, apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]

lemma reflector_mulVec_firstColumn
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    reflector A *ᵥ firstColumn A = firstColumnNorm A • e₀ := by
  rw [reflector]
  by_cases hA : directionDenom A = 0
  · simp [hA, firstColumn_eq_norm_smul_e₀_of_directionDenom_eq_zero A hA]
  · have hvec :
        vecMulVec (direction A) (direction A) *ᵥ firstColumn A =
          (direction A ⬝ᵥ firstColumn A) • direction A := by
      simpa using
        (vecMulVec_mulVec (direction A) (direction A) (firstColumn A))
    have hscale :
        (2 / directionDenom A) * (direction A ⬝ᵥ firstColumn A) = 1 := by
      have htwo : 2 * (direction A ⬝ᵥ firstColumn A) = directionDenom A :=
        two_mul_direction_dot_firstColumn A
      field_simp [hA]
      linarith
    calc
      reflector A *ᵥ firstColumn A
          = firstColumn A -
              (2 / directionDenom A) •
                (vecMulVec (direction A) (direction A) *ᵥ firstColumn A) := by
                  simp [reflector, hA, sub_mulVec, smul_mulVec]
      _ = firstColumn A -
            ((2 / directionDenom A) * (direction A ⬝ᵥ firstColumn A)) • direction A := by
              rw [hvec]
              simp [smul_smul]
      _ = firstColumn A - direction A := by simp [hscale]
      _ = firstColumnNorm A • e₀ := by
            rw [direction]
            abel_nf

lemma firstColumn_after_apply
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    firstColumn (apply A) = firstColumnNorm A • e₀ := by
  rw [firstColumn_apply_eq_mulVec, reflector_mulVec_firstColumn]

lemma sliceable_after_apply
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    FirstColumnSliceable (apply A) := by
  apply sliceable_of_firstColumn_eq_smul_e₀ (c := firstColumnNorm A)
  exact firstColumn_after_apply A

lemma firstColumn_eq_head_smul_e₀
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : FirstColumnSliceable A) :
    firstColumn A = A 0 0 • e₀ := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [firstColumn, e₀]
  · simp [firstColumn, e₀, hi, hA i hi]

lemma firstColumnSqNorm_of_sliceable
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : FirstColumnSliceable A) :
    firstColumnSqNorm A = (A 0 0) ^ 2 := by
  rw [firstColumnSqNorm, firstColumn_eq_head_smul_e₀ A hA]
  classical
  rw [dotProduct, Finset.sum_eq_single 0]
  · simp [e₀, pow_two]
  · intro i _ hi
    simp [e₀, hi]
  · simp [e₀]

lemma firstColumnNorm_of_sliceable_of_nonneg_head
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : FirstColumnSliceable A) (hhead : 0 ≤ A 0 0) :
    firstColumnNorm A = A 0 0 := by
  rw [firstColumnNorm, firstColumnSqNorm_of_sliceable A hA]
  simpa [abs_of_nonneg hhead] using Real.sqrt_sq_eq_abs (A 0 0)

lemma direction_eq_zero_of_sliceable_of_nonneg_head
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : FirstColumnSliceable A) (hhead : 0 ≤ A 0 0) :
    direction A = 0 := by
  rw [direction, firstColumn_eq_head_smul_e₀ A hA,
    firstColumnNorm_of_sliceable_of_nonneg_head A hA hhead]
  simp

lemma directionDenom_eq_zero_of_sliceable_of_nonneg_head
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : FirstColumnSliceable A) (hhead : 0 ≤ A 0 0) :
    directionDenom A = 0 := by
  rw [directionDenom, direction_eq_zero_of_sliceable_of_nonneg_head A hA hhead]
  simp

lemma reflector_eq_one_of_sliceable_of_nonneg_head
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : FirstColumnSliceable A) (hhead : 0 ≤ A 0 0) :
    reflector A = 1 := by
  rw [reflector]
  split_ifs with h
  · rfl
  · exact (h (directionDenom_eq_zero_of_sliceable_of_nonneg_head A hA hhead)).elim

lemma apply_eq_self_of_sliceable_of_nonneg_head
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : FirstColumnSliceable A) (hhead : 0 ≤ A 0 0) :
    apply A = A := by
  rw [apply, reflector_eq_one_of_sliceable_of_nonneg_head A hA hhead]
  simp

lemma sliceable_after_apply_of_sliceable_of_nonneg_head
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (_hA : FirstColumnSliceable A) (_hhead : 0 ≤ A 0 0) :
    FirstColumnSliceable (apply A) := by
  exact sliceable_after_apply A

end RealHouseholder

end MatDecompFormal.Components.Transformations.QR.HouseholderStep
