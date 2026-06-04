import MatDecompFormal.Instances.Schur.Direct
import MatDecompFormal.Instances.Schur.Spectral

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Schur Triangularization: Framework Entry

This file assembles the Schur descent strategy through the square universe
driver:

```lean
SquareStrategyData
mkSquareSubtypeInductionInstanceFromStrategy
SquareSubtypeInductionInstance.prove_for_matrix
```
-/

/-- Universe-level base case for the Schur target. -/
theorem schur_base_univ
    {K : Type u} [Field K] (x : SquareUniverse K) :
    ((∀ (x_sub : PosSquareUniverse K), (x_sub : SquareUniverse K) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      Schur_P x := by
  intro hx
  exact base_schur_zero_dim_sq
    (squareSubtypeBaseDimEqZero x hx)

noncomputable def schur_strategy_data
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        SchurStepOracle K ι)
    (hooks : SchurDescentHooks K oracle) :
    SquareStrategyData K Schur_P :=
  mkSquareStrategyData
    (schur_strategy_core K oracle)
    (schur_strategy_proof K oracle hooks)

noncomputable def schur_framework_inst
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        SchurStepOracle K ι)
    (hooks : SchurDescentHooks K oracle) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstanceFromStrategy
    Schur_P
    schur_base_univ
    (schur_strategy_data K oracle hooks)

/--
Conditional framework-routed Schur triangularization theorem.

This theorem is already assembled through the square descent driver. The
remaining mathematical work is to construct the one-step oracle and the
transport/lift hooks listed in `PLAN.md`.
-/
theorem exists_schur_framework
    {K : Type u} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        SchurStepOracle K κ)
    (hooks : SchurDescentHooks K oracle)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasSchur A := by
  have hP :
      (schur_framework_inst K oracle hooks).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := schur_framework_inst K oracle hooks) A
  exact hP

/--
Framework-routed Schur theorem conditional on the one-step similarity oracle and
the concrete transport/lift hooks constructed in `Direct.lean`.
-/
theorem exists_schur_framework_oracle
    {K : Type u} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        SchurStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasSchur A := by
  exact exists_schur_framework oracle (schur_descent_hooks K oracle) A

/--
Schur triangularization over an algebraically closed field, routed through the
project square descent framework.
-/
theorem exists_schur
    {K : Type u} [Field K] [IsAlgClosed K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasSchur A := by
  exact exists_schur_framework_oracle
    (schur_step_oracle_of_isAlgClosed K) A

end MatDecompFormal.Instances
