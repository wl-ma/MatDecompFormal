import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Abstractions.Strategy
import MatDecompFormal.Components.BlockLifting
import MatDecompFormal.Components.Properties.Reindex
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Components.Transformations.QR.HouseholderStep
import MatDecompFormal.Framework.Fin

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Abstractions
open MatDecompFormal.Components
open MatDecompFormal.Components.Properties
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Components.Transformations.QR.HouseholderStep

/-!
# QR Core

This file contains the QR instance's internal `Fin`-level mathematical core:
the internal `Fin` surface, first-step interface, reduction layer, lifting
layer, strategy, and transport lemmas.
-/

section Internal

variable {n : ℕ}

/-- Orthogonality predicate used by the internal `Fin` QR schema on `ℝ`. -/
def IsOrthogonalMatrix_fin (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Qᵀ * Q = 1

/--
Internal canonical QR schema on square `Fin n` real matrices.
-/
def QR_Schema_fin (n : ℕ) : DecompositionSchema n n ℝ where
  Factors := Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ
  property := fun (Q, R') => IsOrthogonalMatrix_fin (n := n) Q ∧ IsUpperTriangular R'
  equation := fun A (Q, R') => A = Q * R'

/-- Internal QR existence proposition on the unified minimal existence surface. -/
def HasQR_fin (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  HasDecomposition (QR_Schema_fin n) A

end Internal

section FirstStep

variable {k : ℕ}

/-- The internal QR first-column goal for the first Householder step. -/
abbrev QR_FirstColumnGoal_fin :=
  FirstColumnSliceable (k := k)

/-- The reflector matrix used by the first internal QR step. -/
noncomputable abbrev QR_HouseholderReflector_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  reflector (k := k) A

/-- The transformed matrix produced by the first internal QR step. -/
noncomputable abbrev QR_HouseholderStep_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  apply (k := k) A

/--
Matrices ready for QR slicing are exactly those whose first column is already
cleared below the head entry.

This is the reduction entry condition consumed by `QR_Reduction_fin`.
-/
abbrev QR_ReadyForSlice_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : Prop :=
  QR_FirstColumnGoal_fin A

/--
The internal Householder step lands in the QR reduction entry condition.
-/
lemma QR_HouseholderStep_ready_for_slice
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    QR_ReadyForSlice_fin (k := k) (QR_HouseholderStep_fin (k := k) A) := by
  simpa [QR_HouseholderStep_fin, QR_ReadyForSlice_fin, QR_FirstColumnGoal_fin] using
    sliceable_after_apply (k := k) A

/--
Sanity check for the QR Householder step:
if the first column is already in QR sliceable form and the leading entry is
nonnegative, the first step acts as the identity.
-/
lemma QR_HouseholderStep_eq_self_of_ready
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : QR_ReadyForSlice_fin (k := k) A) (hhead : 0 ≤ A 0 0) :
    QR_HouseholderStep_fin (k := k) A = A := by
  simpa [QR_HouseholderStep_fin, QR_ReadyForSlice_fin] using
    apply_eq_self_of_sliceable_of_nonneg_head (k := k) A hA hhead

end FirstStep

section Reduction

variable {k : ℕ}

/--
The recursive QR slice is the right-bottom `k × k` submatrix obtained after the
first row and first column have been split off.
-/
abbrev QR_Slice_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (_hA : QR_ReadyForSlice_fin (k := k) A) : Matrix (Fin k) (Fin k) ℝ :=
  A.submatrix Fin.succ Fin.succ

/--
QR's internal reduction on `(k+1)×(k+1)` real matrices.
-/
noncomputable def QR_Reduction_fin (k : ℕ) :
    ReductionMethod (k + 1) (k + 1) k k ℝ :=
  SubmatrixMethod k k ℝ (QR_ReadyForSlice_fin (k := k))

/-- The QR reduction slices exactly by taking the right-bottom submatrix. -/
@[simp] lemma QR_Reduction_slice_eq
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : (QR_Reduction_fin k).IsSliceable A) :
    (QR_Reduction_fin k).slice A hA = QR_Slice_fin (k := k) A hA := by
  rfl

/--
Viewed through the reduction interface, a sliceable QR matrix recurses on the
`HasQR_fin` goal for its right-bottom slice.
-/
lemma qr_ready_gives_reduction_goal
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : QR_ReadyForSlice_fin (k := k) A) :
    HasQR_fin (QR_Slice_fin (k := k) A hA) =
      HasQR_fin ((QR_Reduction_fin k).slice A hA) := by
  rfl

/--
The step output is a valid input for the QR reduction method.
-/
lemma QR_HouseholderStep_sliceable_for_reduction
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    (QR_Reduction_fin k).IsSliceable (QR_HouseholderStep_fin (k := k) A) := by
  exact QR_HouseholderStep_ready_for_slice (k := k) A

/--
The recursive QR slice produced after one internal Householder step.
-/
noncomputable abbrev QR_HouseholderStepSlice_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (QR_Reduction_fin k).slice
    (QR_HouseholderStep_fin (k := k) A)
    (QR_HouseholderStep_sliceable_for_reduction (k := k) A)

end Reduction

section Lifting

variable {k : ℕ}

/--
QR works in a lexicographically ordered block world when lifting from the slice
back to the original `(k+1) × (k+1)` matrix.
-/
noncomputable abbrev QR_BlockMatrix_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) ℝ :=
  Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A

/-- The `1 × 1` top-left block of the QR lifting matrix context. -/
noncomputable abbrev QR_Block11_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin 1) (Fin 1) ℝ :=
  (QR_BlockMatrix_fin (k := k) A).toBlocks₁₁

/-- The `1 × k` top-right block carried unchanged through QR lifting. -/
noncomputable abbrev QR_Block12_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin 1) (Fin k) ℝ :=
  (QR_BlockMatrix_fin (k := k) A).toBlocks₁₂

/-- The `k × 1` lower-left block, which vanishes under `QR_ReadyForSlice_fin`. -/
noncomputable abbrev QR_Block21_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin k) (Fin 1) ℝ :=
  (QR_BlockMatrix_fin (k := k) A).toBlocks₂₁

/-- The `k × k` lower-right recursive block used by the QR slice. -/
noncomputable abbrev QR_Block22_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  (QR_BlockMatrix_fin (k := k) A).toBlocks₂₂

/--
When a matrix is ready for QR slicing, its lower-left block in the lifting
decomposition is zero.
-/
lemma qr_ready_block21_zero
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : QR_ReadyForSlice_fin (k := k) A) :
    QR_Block21_fin (k := k) A = 0 := by
  ext i j
  fin_cases j
  have h_entry : A i.succ 0 = 0 := hA i.succ (Fin.succ_ne_zero i)
  simpa [QR_Block21_fin, QR_BlockMatrix_fin, Matrix.toBlocks₂₁, Matrix.reindex_apply,
    finSuccEquivSumLex] using h_entry

/--
The lower-right block in the lifting world is definitionally the same recursive
slice used by `QR_Reduction_fin`.
-/
lemma qr_block22_eq_slice
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : QR_ReadyForSlice_fin (k := k) A) :
    QR_Block22_fin (k := k) A = QR_Slice_fin (k := k) A hA := by
  simpa [QR_Block22_fin, QR_BlockMatrix_fin, QR_Slice_fin,
    finSuccEquivSumLex, finSuccEquivSum] using
    (submatrix_succ_eq_toBlocks₂₂ (A := A) (n := k) (m := k)).symm

/--
Lift a recursive orthogonal factor `Q₂₂` into a whole-matrix QR factor by
putting `1` in the leading block and `Q₂₂` in the bottom-right block.
-/
noncomputable abbrev QR_LiftQ_fin
    (Q₂₂ : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.reindex (finSuccEquivSumLex k).symm (finSuccEquivSumLex k).symm
    (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 Q₂₂)

/--
Lift a recursive upper-triangular factor `R₂₂` into a whole-matrix QR factor by
reusing the original top row and the ready-for-slice zero left column.
-/
noncomputable abbrev QR_LiftR_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (R₂₂ : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.reindex (finSuccEquivSumLex k).symm (finSuccEquivSumLex k).symm
    (fromBlocks (QR_Block11_fin (k := k) A) (QR_Block12_fin (k := k) A) 0 R₂₂)

/--
Orthogonality of the lifted global `Q` follows from orthogonality of the slice
factor `Q₂₂`.
-/
lemma qr_liftQ_orthogonal
    (Q₂₂ : Matrix (Fin k) (Fin k) ℝ)
    (hQ₂₂ : IsOrthogonalMatrix_fin (n := k) Q₂₂) :
    IsOrthogonalMatrix_fin (n := k + 1) (QR_LiftQ_fin (k := k) Q₂₂) := by
  have h_blk :
      (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 Q₂₂ :
        Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) ℝ)ᵀ *
        (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 Q₂₂) = 1 := by
    calc
      (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 Q₂₂ :
          Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) ℝ)ᵀ *
          (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 Q₂₂)
          =
          fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (Q₂₂ᵀ * Q₂₂) := by
            rw [fromBlocks_transpose]
            simp [fromBlocks_multiply]
      _ = fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (1 : Matrix (Fin k) (Fin k) ℝ) := by
            rw [hQ₂₂]
      _ = 1 := by
            simp
  dsimp [IsOrthogonalMatrix_fin, QR_LiftQ_fin]
  calc
    (Matrix.reindex (finSuccEquivSumLex k).symm (finSuccEquivSumLex k).symm
        (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 Q₂₂))ᵀ *
        Matrix.reindex (finSuccEquivSumLex k).symm (finSuccEquivSumLex k).symm
          (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 Q₂₂)
        =
        Matrix.reindex (finSuccEquivSumLex k).symm (finSuccEquivSumLex k).symm
          (((fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 Q₂₂ :
              Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) ℝ)ᵀ) *
            (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 Q₂₂)) := by simp
    _ = 1 := by
      simpa using congrArg
        (Matrix.reindex (finSuccEquivSumLex k).symm (finSuccEquivSumLex k).symm) h_blk

/--
Upper triangularity of the lifted global `R` follows from the upper-triangular
recursive factor together with the ready-for-slice zero left column.
-/
lemma qr_liftR_upper_triangular
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (R₂₂ : Matrix (Fin k) (Fin k) ℝ)
    (hR₂₂ : IsUpperTriangular R₂₂) :
    IsUpperTriangular (QR_LiftR_fin (k := k) A R₂₂) := by
  let e : Fin (k + 1) ≃ (Fin 1) ⊕ₗ (Fin k) := finSuccEquivSumLex k
  have h_mono : StrictMono e := by
    simpa [e] using finSuccEquivSumLex_strictMono k
  have hA₁₁_ut : IsUpperTriangular (QR_Block11_fin (k := k) A) := by
    simpa [QR_Block11_fin] using
      (isUpperTriangular_of_subsingleton (A := QR_Block11_fin (k := k) A))
  have hR_blk :
      IsUpperTriangular
        ((fromBlocks (QR_Block11_fin (k := k) A) (QR_Block12_fin (k := k) A) 0 R₂₂ :
            Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ).reindex toLex toLex :
          Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) ℝ) := by
    simpa using
      (isUpperTriangular_fromBlocks_toLex (n₁ := 1) (n₂ := k)
        (A₁₁ := QR_Block11_fin (k := k) A)
        (A₁₂ := QR_Block12_fin (k := k) A)
        (A₂₂ := R₂₂) hA₁₁_ut hR₂₂)
  have hR_re : IsUpperTriangular (Matrix.reindex e e (QR_LiftR_fin (k := k) A R₂₂)) := by
    simpa [QR_LiftR_fin, e] using hR_blk
  exact (isUpperTriangular_reindex (e := e) (h_mono := h_mono)
    (A := QR_LiftR_fin (k := k) A R₂₂)).2 hR_re

/--
QR's lifting equation now factors through the generic two-factor zero-block
lifting core from `BlockLifting`.
-/
lemma qr_lift_equation
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : QR_ReadyForSlice_fin (k := k) A)
    (Q₂₂ R₂₂ : Matrix (Fin k) (Fin k) ℝ)
    (h_slice_eq : QR_Slice_fin (k := k) A hA = Q₂₂ * R₂₂) :
    A = QR_LiftQ_fin (k := k) Q₂₂ * QR_LiftR_fin (k := k) A R₂₂ := by
  have hA₂₁ : QR_Block21_fin (k := k) A = 0 := qr_ready_block21_zero (k := k) A hA
  have hA₂₂ : QR_Block22_fin (k := k) A = Q₂₂ * R₂₂ := by
    rw [qr_block22_eq_slice (k := k) A hA]
    exact h_slice_eq
  simpa [QR_LiftQ_fin, QR_LiftR_fin, QR_Block11_fin, QR_Block12_fin, QR_Block21_fin,
    QR_Block22_fin, QR_BlockMatrix_fin] using
    (lift_two_factor_from_zero_block21 (R := ℝ) (k := k) A Q₂₂ R₂₂ hA₂₁ hA₂₂)

/--
QR-specific lifting: from a QR decomposition of the recursive slice and a
ready-for-slice matrix, build a QR decomposition of the whole matrix.
-/
lemma lift_from_slice_qr_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : QR_ReadyForSlice_fin (k := k) A)
    (h_slice : HasQR_fin (QR_Slice_fin (k := k) A hA)) :
    HasQR_fin A := by
  rcases h_slice with ⟨⟨Q₂₂, R₂₂⟩, ⟨hQ₂₂, hR₂₂⟩, h_slice_eq⟩
  refine ⟨⟨QR_LiftQ_fin (k := k) Q₂₂, QR_LiftR_fin (k := k) A R₂₂⟩, ?_, ?_⟩
  · constructor
    · exact qr_liftQ_orthogonal (k := k) Q₂₂ hQ₂₂
    · exact qr_liftR_upper_triangular (k := k) A R₂₂ hR₂₂
  · dsimp [HasQR_fin, QR_Schema_fin]
    exact qr_lift_equation (k := k) A hA Q₂₂ R₂₂ h_slice_eq

end Lifting

section Strategy

variable {k : ℕ}

/--
QR's strategy-level transform is the single internal Householder step. The
strategy goal is exactly the QR ready-for-slice condition consumed by the
reduction layer.
-/
noncomputable def QR_Transform_fin (k : ℕ) :
    Transformation (Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) where
  T := PUnit
  Goal := QR_ReadyForSlice_fin (k := k)
  decGoal := by
    classical
    exact Classical.decPred _
  apply := fun _ A => QR_HouseholderStep_fin (k := k) A
  find := fun _A _h_not => PUnit.unit
  find_spec := by
    intro A h_not
    simpa using QR_HouseholderStep_ready_for_slice (k := k) A

/--
From the strategy viewpoint, one QR step lands directly in the reduction's
sliceability goal, with no extra translation layer.
-/
lemma QR_Transform_apply_is_sliceable
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (t : (QR_Transform_fin k).T) :
    (QR_Reduction_fin k).IsSliceable ((QR_Transform_fin k).apply t A) := by
  cases t
  exact QR_HouseholderStep_sliceable_for_reduction (k := k) A

/--
Strategy-facing lifting hook: once the reduction slice has QR, the whole matrix
has QR as well.
-/
lemma QR_Strategy_lift_from_slice_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : (QR_Reduction_fin k).IsSliceable A)
    (h_slice : HasQR_fin ((QR_Reduction_fin k).slice A hA)) :
    HasQR_fin A := by
  simpa [QR_Reduction_fin, QR_Reduction_slice_eq] using
    lift_from_slice_qr_fin (k := k) A hA h_slice

/--
Complete internal QR strategy on `(k+1) × (k+1)` real matrices.
-/
noncomputable def QR_Strategy_fin (k : ℕ) :
    ReductionStrategy (k + 1) (k + 1) k k ℝ where
  transform := QR_Transform_fin k
  reduction := QR_Reduction_fin k
  goal_is_sliceable := rfl
  μ := fun _A => k + 1
  μ_slice := fun _A => k
  μ_mono := by
    intro A t
    cases t
    simp
  slice_progress := by
    intro A hA
    simp

/--
The QR strategy recurses from size `k + 1` to size `k` after slicing.
-/
lemma QR_Strategy_slice_dimension_drop
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : (QR_Strategy_fin k).reduction.IsSliceable A) :
    (QR_Strategy_fin k).μ_slice ((QR_Strategy_fin k).reduction.slice A hA) <
      (QR_Strategy_fin k).μ A := by
  simp [QR_Strategy_fin]

end Strategy

section Transport

variable {k : ℕ}

/--
Transport keeps the upper-triangular factor and absorbs the Householder
reflector into the orthogonal factor.
-/
noncomputable abbrev QR_TransportQ_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (Q : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  QR_HouseholderReflector_fin (k := k) A * Q

/--
The transported orthogonal factor remains orthogonal because the Householder
reflector is itself orthogonal.
-/
lemma qr_transportQ_orthogonal
    (A Q : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hQ : IsOrthogonalMatrix_fin (n := k + 1) Q) :
    IsOrthogonalMatrix_fin (n := k + 1) (QR_TransportQ_fin (k := k) A Q) := by
  dsimp [QR_TransportQ_fin, IsOrthogonalMatrix_fin] at hQ ⊢
  have hH :
      (QR_HouseholderReflector_fin (k := k) A)ᵀ *
        QR_HouseholderReflector_fin (k := k) A = 1 := by
    simpa [QR_HouseholderReflector_fin] using reflector_orthogonal (k := k) A
  calc
    (QR_HouseholderReflector_fin (k := k) A * Q)ᵀ *
        (QR_HouseholderReflector_fin (k := k) A * Q)
        =
        Qᵀ *
          (((QR_HouseholderReflector_fin (k := k) A)ᵀ *
              QR_HouseholderReflector_fin (k := k) A) * Q) := by
              simp [Matrix.transpose_mul, mul_assoc]
    _ = Qᵀ * (1 * Q) := by
          rw [hH]
    _ = Qᵀ * Q := by simp
    _ = 1 := hQ

/--
Transport equation: the Householder reflector is involutive, so a QR
decomposition of the step output pulls back to one of the original matrix.
-/
lemma qr_transport_equation
    (A Q R : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (h_step_eq : QR_HouseholderStep_fin (k := k) A = Q * R) :
    A = QR_TransportQ_fin (k := k) A Q * R := by
  have hHH :
      QR_HouseholderReflector_fin (k := k) A *
        QR_HouseholderReflector_fin (k := k) A = 1 := by
    simpa [QR_HouseholderReflector_fin] using reflector_mul_reflector (k := k) A
  calc
    A = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) * A := by simp
    _ = (QR_HouseholderReflector_fin (k := k) A *
          QR_HouseholderReflector_fin (k := k) A) * A := by rw [hHH]
    _ = QR_HouseholderReflector_fin (k := k) A *
          QR_HouseholderStep_fin (k := k) A := by
            simp [QR_HouseholderStep_fin, apply, mul_assoc]
    _ = QR_HouseholderReflector_fin (k := k) A * (Q * R) := by rw [h_step_eq]
    _ = QR_TransportQ_fin (k := k) A Q * R := by
          simp [QR_TransportQ_fin, mul_assoc]

/--
QR transport main theorem: if the Householder-step output has a QR
decomposition, then the original matrix has one as well.
-/
lemma transport_qr_fin
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (h_step : HasQR_fin (QR_HouseholderStep_fin (k := k) A)) :
    HasQR_fin A := by
  rcases h_step with ⟨⟨Q, R⟩, ⟨hQ, hR⟩, hEq⟩
  refine ⟨⟨QR_TransportQ_fin (k := k) A Q, R⟩, ?_, ?_⟩
  · constructor
    · exact qr_transportQ_orthogonal (k := k) A Q hQ
    · exact hR
  · exact qr_transport_equation (k := k) A Q R hEq

/--
Strategy-facing transport hook: any QR decomposition reached along the QR
strategy relation can be pulled back to the original matrix.
-/
lemma QR_Strategy_transport_fin
    {A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (hr : (QR_Strategy_fin k).r B A)
    (hB : HasQR_fin B) :
    HasQR_fin A := by
  rcases hr with rfl | ⟨t, rfl⟩
  · exact hB
  · cases t
    exact transport_qr_fin (k := k) A hB

end Transport

end MatDecompFormal.Instances
