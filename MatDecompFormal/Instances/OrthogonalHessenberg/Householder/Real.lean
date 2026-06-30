/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.OrthogonalHessenberg.Real
import MatDecompFormal.Instances.QR.Householder

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Real Householder Orthogonal Hessenberg Step

This file instantiates the boundary-column Hessenberg descent template with the
real Householder step already used by the QR development.  We apply that step to
a matrix whose active head column is exactly the protected boundary column.
-/

/-- Matrix whose head column is the active boundary column. -/
noncomputable def householderRealBoundaryColumnMatrix
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    Matrix x_sub.1.ι x_sub.1.ι ℝ := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact fun i j => if j = headElem (α := x_sub.1.ι) then x_sub.1.c i () else 0

/-- The left Householder transform that clears the boundary column. -/
noncomputable def householderRealBoundarySweepH
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    Matrix x_sub.1.ι x_sub.1.ι ℝ := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  by_cases hready : QRReady x_sub.1.ι (householderRealBoundaryColumnMatrix x_sub)
  · exact 1
  · exact qrHeadOrthogonalStep x_sub.1.ι (householderRealBoundaryColumnMatrix x_sub) hready

/-- Boundary-step factor.  The boundary template uses `Qᵀ * c`, while the QR
Householder step proves `H * c` is ready, so we set `Q = Hᵀ`. -/
noncomputable def householderRealBoundaryStepQ
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    Matrix x_sub.1.ι x_sub.1.ι ℝ :=
  (householderRealBoundarySweepH x_sub)ᵀ

theorem householder_real_boundary_step_orthogonal
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    IsOrthogonalMatrix (householderRealBoundaryStepQ x_sub) := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  by_cases hready : QRReady x_sub.1.ι (householderRealBoundaryColumnMatrix x_sub)
  · simp [householderRealBoundaryStepQ, householderRealBoundarySweepH, hready,
      isOrthogonalMatrix_one]
  · simpa [householderRealBoundaryStepQ, householderRealBoundarySweepH, hready] using
      isOrthogonalMatrix_transpose
        (qrHeadOrthogonalStep_isOrthogonal x_sub.1.ι (householderRealBoundaryColumnMatrix x_sub)
          hready)

lemma householderRealBoundarySweep_ready
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
    QRReady x_sub.1.ι
      (householderRealBoundarySweepH x_sub * householderRealBoundaryColumnMatrix x_sub) := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  by_cases hready : QRReady x_sub.1.ι (householderRealBoundaryColumnMatrix x_sub)
  · simp [householderRealBoundarySweepH, hready]
  · simpa [householderRealBoundarySweepH, hready] using
      qrHeadOrthogonalStep_spec x_sub.1.ι (householderRealBoundaryColumnMatrix x_sub)
        hready

lemma householderRealBoundarySweep_column_zero
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ)
    (i : x_sub.1.ι)
    (hi : letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
      i ≠ headElem (α := x_sub.1.ι)) :
    letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
    (householderRealBoundarySweepH x_sub * householderRealBoundaryColumnMatrix x_sub)
        i (headElem (α := x_sub.1.ι)) = 0 := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  let k : QRTailIdx x_sub.1.ι := ⟨i, hi⟩
  have hready := householderRealBoundarySweep_ready x_sub
  have hentry :
      (Matrix.reindex (headTailEquiv (α := x_sub.1.ι))
          (headTailEquiv (α := x_sub.1.ι))
          (householderRealBoundarySweepH x_sub *
            householderRealBoundaryColumnMatrix x_sub)).toBlocks₂₁
          k () = 0 := by
    simpa [QRReady] using congrFun (congrFun hready k) ()
  simpa [Matrix.toBlocks₂₁, Matrix.reindex_apply, k] using hentry

lemma householderRealBoundarySweep_mul_column_zero
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ)
    (i : x_sub.1.ι)
    (hi : letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
      i ≠ headElem (α := x_sub.1.ι)) :
    (householderRealBoundarySweepH x_sub * x_sub.1.c) i () = 0 := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  have hentry := householderRealBoundarySweep_column_zero x_sub i hi
  simpa [Matrix.mul_apply, householderRealBoundaryColumnMatrix] using hentry

theorem householder_real_boundary_step_ready
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    HessenbergBoundaryReady
      (orthogonalHessenbergBoundarySimilarityObject
        (x_sub : HessenbergBoundaryUniverse.{u} ℝ)
        (householderRealBoundaryStepQ x_sub)) := by
  classical
  intro _hne i hi
  simpa [orthogonalHessenbergBoundarySimilarityObject, householderRealBoundaryStepQ] using
    householderRealBoundarySweep_mul_column_zero x_sub i hi

/-- Real orthogonal Householder boundary-step oracle. -/
noncomputable def householderOrthogonalBoundaryStepOracle :
    OrthogonalHessenbergBoundaryStepOracle.{u} where
  Q := householderRealBoundaryStepQ
  orthogonal_Q := householder_real_boundary_step_orthogonal
  ready := householder_real_boundary_step_ready

/-- Real orthogonal Hessenberg reduction via Householder reflections. -/
theorem exists_orthogonal_hessenberg_reduction_householder
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    HasOrthogonalHessenberg A :=
  exists_orthogonal_hessenberg_reduction_of_oracle
    householderOrthogonalBoundaryStepOracle A

end MatDecompFormal.Instances
