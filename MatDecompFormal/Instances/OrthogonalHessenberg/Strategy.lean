/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.OrthogonalHessenberg.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Orthogonal/Unitary Hessenberg Strategy

The hard numerical step is isolated as a unitary boundary step oracle.  It is
the unitary analogue of `HessenbergBoundaryStepOracle`: the matrix update is
`Qᴴ * A * Q`, and the boundary column is updated by `Qᴴ`.
-/

/-- Boundary object obtained by applying a unitary similarity. -/
noncomputable def unitaryHessenbergBoundarySimilarityObject
    (x : HessenbergBoundaryUniverse.{u} ℂ)
    (Q : Matrix x.ι x.ι ℂ) : HessenbergBoundaryUniverse.{u} ℂ :=
  { ι := x.ι
    A := Qᴴ * x.A * Q
    c := Qᴴ * x.c }

/-- One-step unitary boundary oracle for Hessenberg reduction. -/
structure UnitaryHessenbergBoundaryStepOracle where
  Q :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℂ,
      Matrix x_sub.1.ι x_sub.1.ι ℂ
  unitary_Q :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℂ,
      IsUnitaryMatrix (Q x_sub)
  ready :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℂ,
      HessenbergBoundaryReady
        (unitaryHessenbergBoundarySimilarityObject
          (x_sub : HessenbergBoundaryUniverse.{u} ℂ) (Q x_sub))

/-- A unitary boundary oracle forgets to the ordinary invertible boundary oracle. -/
noncomputable def hessenbergBoundaryStepOracleOfUnitary
    (oracle : UnitaryHessenbergBoundaryStepOracle.{u}) :
    HessenbergBoundaryStepOracle.{u, 0} ℂ where
  P := fun x_sub => oracle.Q x_sub
  Pinv := fun x_sub => (oracle.Q x_sub)ᴴ
  inverse_P := fun x_sub => hasMatrixInverse_of_isUnitaryMatrix (oracle.unitary_Q x_sub)
  ready := by
    intro x_sub
    simpa [unitaryHessenbergBoundarySimilarityObject,
      hessenbergBoundarySimilarityObject] using oracle.ready x_sub

end MatDecompFormal.Instances
