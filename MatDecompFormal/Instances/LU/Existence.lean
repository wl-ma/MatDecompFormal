import MatDecompFormal.Instances.LU.Direct

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# LU Existence

This file assembles the no-pivot LU theorem through the square decomposition
driver. The theorem is conditional on `LURecursivePivotReady`, which encodes the
nonzero recursive pivots required for LU without row permutations.
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

/--
Framework-routed LU decomposition theorem under recursive no-pivot readiness.
-/
theorem exists_lu_of_noPivotReady
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : LURecursivePivotReady A) :
    HasLU A := by
  let inst : SquareSubtypeInductionInstance R := lu_framework_inst
  have hP :
      inst.P
        (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := inst) A
  exact hP hA

end Target

end MatDecompFormal.Instances
