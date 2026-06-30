/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Instances.QR.Details
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace MatDecompFormal.Instances

open Matrix
open InnerProductSpace
open MatDecompFormal.Framework
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Components.Properties

/-!
# QR Strategy Core

This file contains the active strategy-side core used by the current QR
framework driver.
-/

/-- The subtype of non-head indices of `ι`, used as the tail index type for QR descent. -/
abbrev QRTailIdx (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { a : ι // a ≠ headElem (α := ι) }

/-- `QRReady ι A` holds when the lower-left block of `A` (reindexed by `headTailEquiv`) is zero,
i.e., the head column of `A` is already in upper-triangular position. -/
def QRReady
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Zero R]
    (A : Matrix ι ι R) : Prop :=
  let A' := Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A
  A'.toBlocks₂₁ = 0

noncomputable instance qrReadyDecidable
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Zero R] :
    DecidablePred (fun A : Matrix ι ι R => QRReady ι A) := by
  classical
  intro A
  unfold QRReady
  infer_instance

lemma qrReady_of_upperTriangular
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Zero R]
    (A : Matrix ι ι R) (hA : IsUpperTriangular A) :
    QRReady ι A := by
  ext i j
  cases j
  have hlt : headElem (α := ι) < (i : ι) :=
    lt_of_le_of_ne (headElem_le (α := ι) (i : ι)) i.2.symm
  simpa [QRReady, Matrix.toBlocks₂₁, Matrix.reindex_apply,
    headTailEquiv_symm_apply_inl, headTailEquiv_symm_apply_inr] using hA hlt

noncomputable abbrev qrHeadColumnVec
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (A.col (headElem (α := ι)))

noncomputable abbrev qrHeadAxisVec
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    EuclideanSpace ℝ ι :=
  EuclideanSpace.basisFun ι ℝ (headElem (α := ι))

lemma qrReady_of_headColumnVec_eq_zero
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ)
    (hcol : qrHeadColumnVec ι A = 0) :
    QRReady ι A := by
  ext i j
  cases j
  have hentry : A i.1 (headElem (α := ι)) = 0 := by
    have := congrArg (fun v => v i.1) hcol
    simpa [qrHeadColumnVec, Matrix.col] using this
  simpa [QRReady, Matrix.toBlocks₂₁, Matrix.reindex_apply,
    headTailEquiv_symm_apply_inl, headTailEquiv_symm_apply_inr] using hentry

lemma qrHeadColumnVec_ne_zero_of_not_qrReady
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ¬ QRReady ι A) :
    qrHeadColumnVec ι A ≠ 0 := by
  intro hcol
  exact hA (qrReady_of_headColumnVec_eq_zero ι A hcol)

noncomputable abbrev qrHeadUnitVec
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (_hA : ¬ QRReady ι A) : EuclideanSpace ℝ ι :=
  (‖qrHeadColumnVec ι A‖ : ℝ)⁻¹ • qrHeadColumnVec ι A

lemma qrHeadUnitVec_norm
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ¬ QRReady ι A) :
    ‖qrHeadUnitVec ι A hA‖ = 1 := by
  have hne := qrHeadColumnVec_ne_zero_of_not_qrReady ι A hA
  simpa [qrHeadUnitVec] using (norm_smul_inv_norm hne)

lemma qrHeadAxisVec_norm
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    ‖qrHeadAxisVec ι‖ = 1 := by
  simpa [qrHeadAxisVec] using (EuclideanSpace.basisFun ι ℝ).norm_eq_one (headElem (α := ι))

noncomputable abbrev qrHeadReflector
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ¬ QRReady ι A) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  ((ℝ ∙ (qrHeadAxisVec ι - qrHeadUnitVec ι A hA))ᗮ).reflection

lemma qrHeadReflector_apply_axis
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ¬ QRReady ι A) :
    qrHeadReflector ι A hA (qrHeadAxisVec ι) = qrHeadUnitVec ι A hA := by
  have hnorms : ‖qrHeadAxisVec ι‖ = ‖qrHeadUnitVec ι A hA‖ := by
    rw [qrHeadAxisVec_norm, qrHeadUnitVec_norm]
  simpa [qrHeadReflector] using
    (Submodule.reflection_sub (v := qrHeadAxisVec ι) (w := qrHeadUnitVec ι A hA) hnorms)

noncomputable def qrHeadBasis
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ¬ QRReady ι A) :
    OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) :=
  (EuclideanSpace.basisFun ι ℝ).map (qrHeadReflector ι A hA)

lemma qrHeadBasis_apply_head
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ¬ QRReady ι A) :
    qrHeadBasis ι A hA (headElem (α := ι)) = qrHeadUnitVec ι A hA := by
  simpa [qrHeadBasis, qrHeadAxisVec] using qrHeadReflector_apply_axis ι A hA

noncomputable abbrev qrHeadOrthogonalStep
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ¬ QRReady ι A) : Matrix ι ι ℝ :=
  ((EuclideanSpace.basisFun ι ℝ).toBasis.toMatrix (qrHeadBasis ι A hA))ᵀ

lemma qrHeadOrthogonalStep_isOrthogonal
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ¬ QRReady ι A) :
    IsOrthogonalMatrix (qrHeadOrthogonalStep ι A hA) := by
  let Q : Matrix ι ι ℝ :=
    (EuclideanSpace.basisFun ι ℝ).toBasis.toMatrix (qrHeadBasis ι A hA)
  have hmem : Q ∈ Matrix.orthogonalGroup ι ℝ :=
    (EuclideanSpace.basisFun ι ℝ).toMatrix_orthonormalBasis_mem_orthogonal (qrHeadBasis ι A hA)
  have hQ : IsOrthogonalMatrix Q := by
    rw [Matrix.mem_orthogonalGroup_iff'] at hmem
    exact hmem
  simpa [qrHeadOrthogonalStep, Q] using isOrthogonalMatrix_transpose hQ

lemma qrHeadOrthogonalStep_spec
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ¬ QRReady ι A) :
    QRReady ι (qrHeadOrthogonalStep ι A hA * A) := by
  classical
  let e : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) := EuclideanSpace.basisFun ι ℝ
  let b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) := qrHeadBasis ι A hA
  let v : ι → EuclideanSpace ℝ ι := fun j => WithLp.toLp 2 (A.col j)
  let Q : Matrix ι ι ℝ := e.toBasis.toMatrix b
  let Rm : Matrix ι ι ℝ := b.toBasis.toMatrix v
  let head : ι := headElem (α := ι)
  have horth : IsOrthogonalMatrix Q := by
    have hmem : Q ∈ Matrix.orthogonalGroup ι ℝ :=
      e.toMatrix_orthonormalBasis_mem_orthogonal b
    rw [Matrix.mem_orthogonalGroup_iff'] at hmem
    exact hmem
  have hQQ : (Qᵀ * Q) * Rm = Rm := by
    have hmul := congrArg (fun M => M * Rm) horth
    simpa [IsOrthogonalMatrix, Matrix.mul_assoc] using hmul
  have hQR : qrHeadOrthogonalStep ι A hA * A = Rm := by
    calc
      qrHeadOrthogonalStep ι A hA * A = Qᵀ * A := by rfl
      _ = Qᵀ * (Q * Rm) := by
        have hmul : Q * Rm = A := by
          change e.toBasis.toMatrix b * b.toBasis.toMatrix v = A
          have := e.toBasis.toMatrix_mul_toMatrix (b' := b.toBasis) (b'' := v)
          simpa [Q, Rm, v] using this
        rw [hmul]
      _ = (Qᵀ * Q) * Rm := by rw [Matrix.mul_assoc]
      _ = Rm := hQQ
  rw [hQR]
  ext i j
  cases j
  have hneVec := qrHeadColumnVec_ne_zero_of_not_qrReady ι A hA
  have hneNorm : ‖qrHeadColumnVec ι A‖ ≠ 0 := by
    simpa using hneVec
  have hhead : b head = qrHeadUnitVec ι A hA :=
    qrHeadBasis_apply_head ι A hA
  have hvec : qrHeadColumnVec ι A = ‖qrHeadColumnVec ι A‖ • b head := by
    calc
      qrHeadColumnVec ι A
          = ‖qrHeadColumnVec ι A‖ • ((‖qrHeadColumnVec ι A‖ : ℝ)⁻¹ • qrHeadColumnVec ι A) := by
              rw [smul_smul, mul_inv_cancel₀ hneNorm, one_smul]
      _ = ‖qrHeadColumnVec ι A‖ • b head := by simp [qrHeadUnitVec, hhead]
  have hzero : b.toBasis.repr (v head) i = 0 := by
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    change inner ℝ (b i) (qrHeadColumnVec ι A) = 0
    rw [hvec, inner_smul_right]
    simp [head, OrthonormalBasis.inner_eq_zero, i.2]
  simpa [QRReady, Matrix.toBlocks₂₁, Matrix.reindex_apply,
    headTailEquiv_symm_apply_inl, headTailEquiv_symm_apply_inr,
    Module.Basis.toMatrix_apply, Rm, v, head] using hzero

noncomputable def qrDirectOrthogonalTransform
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    MatDecompFormal.Abstractions.Transformation (Matrix ι ι ℝ) where
  T := { Q : Matrix ι ι ℝ // IsOrthogonalMatrix Q ∧ IsOrthogonalMatrix Qᵀ }
  Goal := QRReady ι
  decGoal := by infer_instance
  apply := fun Q A => Q.1 * A
  find := fun A hA =>
    ⟨qrHeadOrthogonalStep ι A hA,
      qrHeadOrthogonalStep_isOrthogonal ι A hA,
      isOrthogonalMatrix_transpose (qrHeadOrthogonalStep_isOrthogonal ι A hA)⟩
  find_spec := by
    intro A hA
    simpa using qrHeadOrthogonalStep_spec ι A hA

noncomputable def qrHeadTailSubmatrixReduction
    (ι : Type*)
    [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Zero R] :
    MatDecompFormal.Abstractions.ReductionMethod ι ι (QRTailIdx ι) (QRTailIdx ι) R :=
  SubmatrixMethod
    (headTailEquiv (α := ι))
    (headTailEquiv (α := ι))
    (QRReady ι)

noncomputable def qrHeadTailSubmatrixStrategyCore : SquareStrategyCore ℝ where
  SliceIdx := fun {ι} fι dι oι nι => @QRTailIdx ι fι oι nι
  sliceFintype := by
    intro ι fι dι oι nι
    infer_instance
  sliceDecEq := by
    intro ι fι dι oι nι
    infer_instance
  sliceLinearOrder := by
    intro ι fι dι oι nι
    infer_instance
  strategy := by
    intro ι fι dι oι nι
    refine
      { transform := qrDirectOrthogonalTransform ι
        reduction := qrHeadTailSubmatrixReduction ι
        goal_is_sliceable := by
          funext A
          rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (QRTailIdx ι)
        μ_mono := ?_
        slice_progress := ?_ }
    · intro A t
      simp
    · intro A hA
      have hlt : Fintype.card (QRTailIdx ι) < Fintype.card ι := by
        simpa [QRTailIdx] using
          (Fintype.card_subtype_lt
            (p := fun a : ι => a ≠ headElem (α := ι))
            (x := headElem (α := ι))
            (by simp))
      simpa using hlt
  μ_eq := by
    intro ι fι dι oι nι A
    rfl
  μ_slice_eq := by
    intro ι fι dι oι nι B
    rfl



end MatDecompFormal.Instances
