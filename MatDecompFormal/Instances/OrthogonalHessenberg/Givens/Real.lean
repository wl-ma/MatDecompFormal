/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.OrthogonalHessenberg.Real
import MatDecompFormal.Instances.QR.Givens

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Real Givens Orthogonal Hessenberg Step

This file instantiates the boundary-column Hessenberg descent template with
the real Givens sweep from the QR development.  The sweep acts on a matrix whose
active head column is the protected boundary column.
-/

/-- Matrix whose head column is the active boundary column. -/
noncomputable def givensRealBoundaryColumnMatrix
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    Matrix x_sub.1.ι x_sub.1.ι ℝ := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact fun i j => if j = headElem (α := x_sub.1.ι) then x_sub.1.c i () else 0

/-- Givens sweep matrix that sends the boundary column to head-axis form. -/
noncomputable def givensRealBoundarySweepH
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    Matrix x_sub.1.ι x_sub.1.ι ℝ := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact
    qrGivensSweepQ
      (qrGivensTailList x_sub.1.ι)
      (givensRealBoundaryColumnMatrix x_sub)

/-- Boundary-step factor.  The boundary template uses `Qᵀ * c`, while the QR
Givens sweep proves `H * c` is ready, so we set `Q = Hᵀ`. -/
noncomputable def givensRealBoundaryStepQ
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    Matrix x_sub.1.ι x_sub.1.ι ℝ :=
  (givensRealBoundarySweepH x_sub)ᵀ

theorem givens_real_boundary_step_orthogonal
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    IsOrthogonalMatrix (givensRealBoundaryStepQ x_sub) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact isOrthogonalMatrix_transpose
    (isOrthogonalMatrix_qrGivensSweepQ
      (qrGivensTailList x_sub.1.ι)
      (givensRealBoundaryColumnMatrix x_sub))

lemma givensRealBoundarySweep_ready
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
    QRReady x_sub.1.ι
      (givensRealBoundarySweepH x_sub * givensRealBoundaryColumnMatrix x_sub) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  simpa [givensRealBoundarySweepH, qrGivensSweepQ] using
    qrGivensSweep_ready (givensRealBoundaryColumnMatrix x_sub)

lemma givensRealBoundarySweep_column_zero
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ)
    (i : x_sub.1.ι)
    (hi : letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
      i ≠ headElem (α := x_sub.1.ι)) :
    letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
    (givensRealBoundarySweepH x_sub * givensRealBoundaryColumnMatrix x_sub)
        i (headElem (α := x_sub.1.ι)) = 0 := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  let k : QRTailIdx x_sub.1.ι := ⟨i, hi⟩
  have hready := givensRealBoundarySweep_ready x_sub
  have hentry :
      (Matrix.reindex (headTailEquiv (α := x_sub.1.ι))
          (headTailEquiv (α := x_sub.1.ι))
          (givensRealBoundarySweepH x_sub * givensRealBoundaryColumnMatrix x_sub)).toBlocks₂₁
          k () = 0 := by
    simpa [QRReady] using congrFun (congrFun hready k) ()
  simpa [Matrix.toBlocks₂₁, Matrix.reindex_apply, k] using hentry

lemma givensRealBoundarySweep_mul_column_zero
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ)
    (i : x_sub.1.ι)
    (hi : letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
      i ≠ headElem (α := x_sub.1.ι)) :
    (givensRealBoundarySweepH x_sub * x_sub.1.c) i () = 0 := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  have hentry := givensRealBoundarySweep_column_zero x_sub i hi
  simpa [Matrix.mul_apply, givensRealBoundaryColumnMatrix] using hentry

theorem givens_real_boundary_step_ready
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    HessenbergBoundaryReady
      (orthogonalHessenbergBoundarySimilarityObject
        (x_sub : HessenbergBoundaryUniverse.{u} ℝ)
        (givensRealBoundaryStepQ x_sub)) := by
  classical
  intro _hne i hi
  simpa [orthogonalHessenbergBoundarySimilarityObject, givensRealBoundaryStepQ] using
    givensRealBoundarySweep_mul_column_zero x_sub i hi

/-- Real orthogonal Givens boundary-step oracle. -/
noncomputable def givensOrthogonalBoundaryStepOracle :
    OrthogonalHessenbergBoundaryStepOracle.{u} where
  Q := givensRealBoundaryStepQ
  orthogonal_Q := givens_real_boundary_step_orthogonal
  ready := givens_real_boundary_step_ready

/-- Real orthogonal Hessenberg reduction via Givens rotations. -/
theorem exists_orthogonal_hessenberg_reduction_givens
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    HasOrthogonalHessenberg A :=
  exists_orthogonal_hessenberg_reduction_of_oracle
    givensOrthogonalBoundaryStepOracle A

end MatDecompFormal.Instances
