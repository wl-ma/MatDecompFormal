/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.LU.Direct
import MatDecompFormal.Instances.LU.NonrecursiveCriterion

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# LU Existence

This file assembles the no-pivot LU theorem through the square decomposition
driver. The final public theorem is conditional on a determinant-style
no-zero-pivot criterion, proved equivalent to the recursive pivot-readiness
predicate consumed by the driver.
-/

section Target

variable {R : Type*} [DivisionRing R]

/-- Universe-level conditional LU target. -/
def LU_P (x : SquareUniverse R) : Prop :=
  LURecursivePivotReady x.A → HasLU x.A

/-- Positive-universe conditional LU target. -/
def LU_P_sub (x_sub : PosSquareUniverse R) : Prop :=
  LU_P (x_sub : SquareUniverse R)

@[simp] theorem lu_P_compat (x_sub : PosSquareUniverse R) :
    LU_P_sub x_sub ↔ LU_P (x_sub : SquareUniverse R) :=
  Iff.rfl

/-- Universe-level base case for conditional LU. -/
theorem lu_base_univ (x : SquareUniverse R) :
    ((∀ (x_sub : PosSquareUniverse R), (x_sub : SquareUniverse R) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      LU_P x := by
  intro hx _hReady
  exact base_lu_zero_dim_sq
    (squareSubtypeBaseDimEqZero x hx)

/-- Assembled LU strategy data for the no-pivot Schur-complement core. -/
noncomputable def lu_strategy_data : SquareStrategyData R LU_P :=
  mkSquareStrategyData
    lu_strategy_core
    lu_strategy_proof

/-- Square subtype-induction instance for conditional LU. -/
noncomputable def lu_framework_inst : SquareSubtypeInductionInstance R :=
  mkSquareSubtypeInductionInstanceFromStrategy
    LU_P
    lu_base_univ
    lu_strategy_data

/-- Framework-routed LU decomposition theorem under internal recursive pivot readiness. -/
theorem exists_lu_of_noPivotReady
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : LURecursivePivotReady A) :
    HasLU A := by
  have hP :
      (lu_framework_inst : SquareSubtypeInductionInstance R).P
        (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := lu_framework_inst) (A := A)
  exact hP hA

end Target

section PublicCriterion

variable {R : Type*} [Field R]

/-- Fin-indexed LU decomposition theorem under nonzero proper leading principal minors. -/
theorem exists_lu_of_nonzeroProperLeadingPrincipalMinors
    {n : Nat} (A : Matrix (Fin n) (Fin n) R)
    (hA : HasNonzeroProperLeadingPrincipalMinors A) :
    HasLU A :=
  exists_lu_of_noPivotReady A
    (luRecursivePivotReady_of_nonzeroProperLeadingPrincipalMinors A hA)

/-- Framework-routed LU decomposition theorem under the non-recursive no-pivot criterion. -/
theorem exists_lu_of_nonzeroLUSchurPivots
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : HasNonzeroLUSchurPivots A) :
    HasLU A :=
  exists_lu_of_noPivotReady A
    ((hasNonzeroLUSchurPivots_iff_recursivePivotReady (A := A)).1 hA)

/--
Public LU decomposition theorem under the determinant-style no-zero-pivot
criterion. The proof enters the descent driver through
`hasNoZeroLUPivots_iff_recursivePivotReady`, so users do not need to state the
internal recursive readiness predicate.
-/
theorem exists_lu
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : HasNoZeroLUPivots A) :
    HasLU A :=
  exists_lu_of_noPivotReady A
    ((hasNoZeroLUPivots_iff_recursivePivotReady (A := A)).1 hA)

/-- Compatibility name for the public determinant no-zero-pivot theorem. -/
theorem exists_lu_of_noZeroPivots
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : HasNoZeroLUPivots A) :
    HasLU A :=
  exists_lu A hA

end PublicCriterion

end MatDecompFormal.Instances
