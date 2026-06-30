/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Hessenberg.Direct

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Hessenberg Framework Entry

This file assembles Hessenberg reduction through the square universe driver:

```lean
SquareStrategyData
mkSquareSubtypeInductionInstanceFromStrategy
SquareSubtypeInductionInstance.prove_for_matrix
```

The theorem is currently conditional on the one-step similarity oracle. The
oracle's readiness field contains the block-lift proof required by the strict
descent-template plan.
-/

/-- Universe-level base case for the Hessenberg target. -/
theorem hessenberg_base_univ {R : Type u} [Semiring R] (x : SquareUniverse R) :
    ((∀ (x_sub : PosSquareUniverse R), (x_sub : SquareUniverse R) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      Hessenberg_P x := by
  intro hx
  have hzero : Fintype.card x.ι = 0 :=
    squareSubtypeBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  letI : Subsingleton x.ι := by infer_instance
  exact base_hessenberg_subsingleton x.A

noncomputable def hessenberg_strategy_data
    {R : Type u} [Semiring R]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        HessenbergSimilarityOracle R ι) :
    SquareStrategyData R Hessenberg_P :=
  mkSquareStrategyData
    (hessenberg_strategy_core oracle)
    (hessenberg_strategy_proof oracle)

noncomputable def hessenberg_framework_inst
    {R : Type u} [Semiring R]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        HessenbergSimilarityOracle R ι) :
    SquareSubtypeInductionInstance R :=
  mkSquareSubtypeInductionInstanceFromStrategy
    Hessenberg_P
    hessenberg_base_univ
    (hessenberg_strategy_data oracle)

/--
Framework-routed Hessenberg reduction theorem.

This is the strict-template theorem: the result is obtained by the square
descent driver, with the one-step similarity construction and readiness/lift
proof made explicit in the oracle.
-/
theorem exists_hessenberg_reduction_framework
    {R : Type u} [Semiring R]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        HessenbergSimilarityOracle R κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) :
    HasHessenberg A := by
  have hP :
      (hessenberg_framework_inst oracle).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := hessenberg_framework_inst oracle) A
  exact hP

/--
Framework-routed theorem using the plan-facing one-step oracle. This is the
interface targeted by the concrete field-level column-zeroing construction.
-/
theorem exists_hessenberg_reduction_framework_stepOracle
    {R : Type u} [Semiring R]
    (stepOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        HessenbergStepOracle R κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) :
    HasHessenberg A := by
  let oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        HessenbergSimilarityOracle R κ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      hessenbergSimilarityOracleOfStepOracle R κ (stepOracle (κ := κ))
  exact exists_hessenberg_reduction_framework oracle A

end MatDecompFormal.Instances
