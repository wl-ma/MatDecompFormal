import MatDecompFormal.Instances.Tridiagonalization.Direct
import MatDecompFormal.Instances.OrthogonalHessenberg.Existence

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Tridiagonalization Framework Entry

This file assembles unitary tridiagonalization through the strict square
descent framework:

```lean
SquareStrategyData
mkSquareSubtypeInductionInstanceFromStrategy
SquareSubtypeInductionInstance.prove_for_matrix
```

The theorem is currently conditional on the one-step unitary lift-ready oracle.
-/

/-- Universe-level base case for the tridiagonalization target. -/
theorem tridiagonalization_base_univ (x : SquareUniverse ℂ) :
    ((∀ (x_sub : PosSquareUniverse ℂ), (x_sub : SquareUniverse ℂ) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      Tridiagonalization_P x := by
  intro hx hHerm
  have hzero : Fintype.card x.ι = 0 :=
    squareSubtypeBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  letI : Subsingleton x.ι := by infer_instance
  exact base_unitaryTridiagonalization_subsingleton x.A hHerm

noncomputable def tridiagonalization_strategy_data
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        TridiagonalizationSimilarityOracle ι) :
    SquareStrategyData ℂ Tridiagonalization_P :=
  mkSquareStrategyData
    (tridiagonalization_strategy_core oracle)
    (tridiagonalization_strategy_proof oracle)

noncomputable def tridiagonalization_framework_inst
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        TridiagonalizationSimilarityOracle ι) :
    SquareSubtypeInductionInstance ℂ :=
  mkSquareSubtypeInductionInstanceFromStrategy
    Tridiagonalization_P
    tridiagonalization_base_univ
    (tridiagonalization_strategy_data oracle)

/--
Framework-routed unitary tridiagonalization theorem conditional on a one-step
unitary similarity oracle.
-/
theorem exists_unitary_tridiagonalization_framework
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        TridiagonalizationSimilarityOracle κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A := by
  have hP :
      (tridiagonalization_framework_inst oracle).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := tridiagonalization_framework_inst oracle) A
  exact hP hA

/--
Plan-facing framework theorem stated in terms of the exact lift-ready step
oracle. Concrete Householder/Givens constructions should build this oracle.
-/
theorem exists_unitary_tridiagonalization_framework_stepOracle
    (stepOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        TridiagonalizationStepOracle κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A := by
  let oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        TridiagonalizationSimilarityOracle κ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      tridiagonalizationSimilarityOracleOfStepOracle κ (stepOracle (κ := κ))
  exact exists_unitary_tridiagonalization_framework oracle A hA

/--
Framework theorem stated in terms of the concrete head-tail block readiness
oracle.  The separate `blockLift` argument is the local block algebra showing
that the explicit first-column readiness lifts a tail tridiagonalization to the
parent problem.
-/
theorem exists_unitary_tridiagonalization_framework_blockReadyOracle
    (blockLift :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        TridiagonalizationBlockLiftTheorem κ)
    (blockOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        TridiagonalizationBlockReadyOracle κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A := by
  let stepOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        TridiagonalizationStepOracle κ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      tridiagonalizationStepOracleOfBlockReadyOracle κ
        (blockLift (κ := κ)) (blockOracle (κ := κ))
  exact exists_unitary_tridiagonalization_framework_stepOracle stepOracle A hA

/--
Hermitian tridiagonalization obtained from the unitary Hessenberg descent.

This theorem is still framework-routed: the Hessenberg reduction is produced by
the boundary-column descent driver, and Hermitian upper Hessenberg form is then
converted to tridiagonal form.
-/
theorem exists_unitary_tridiagonalization_of_unitaryHessenbergOracle
    (oracle : UnitaryHessenbergBoundaryStepOracle.{u})
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A :=
  hasUnitaryTridiagonalization_of_hasUnitaryHessenberg hA
    (exists_unitary_hessenberg_reduction oracle A)

end MatDecompFormal.Instances
