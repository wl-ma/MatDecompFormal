/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Bidiagonalization.Direct

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Bidiagonalization: Framework Entry

This file assembles oracle-routed unitary bidiagonalization through the
project's rectangular descent framework.
-/

variable {𝕜 : Type v} [RCLike 𝕜]

/-- Universe-level base case for the bidiagonalization target. -/
theorem bidiagonalization_base_univ (x : RectUniverse 𝕜) :
    ((∀ (x_sub : PosRectUniverse 𝕜), (x_sub : RectUniverse 𝕜) ≠ x) ∨
      rectSubtypeμ x ≤ rectSubtypeμBase) →
      Bidiagonalization_P 𝕜 x := by
  intro hx
  rcases rectSubtypeBaseDimEqZero x hx with hrow | hcol
  · letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hrow
    exact base_bidiagonalization_empty_rows x.A
  · letI : IsEmpty x.κ := Fintype.card_eq_zero_iff.mp hcol
    exact base_bidiagonalization_empty_cols x.A

/-- Universe-level base case for the fixed-right-head bidiagonalization target. -/
theorem bidiagonalization_fixedRightHead_base_univ (x : RectUniverse 𝕜) :
    ((∀ (x_sub : PosRectUniverse 𝕜), (x_sub : RectUniverse 𝕜) ≠ x) ∨
      rectSubtypeμ x ≤ rectSubtypeμBase) →
      BidiagonalizationFixedRightHead_P 𝕜 x := by
  intro hx
  rcases rectSubtypeBaseDimEqZero x hx with hrow | hcol
  · by_cases hn : Nonempty x.κ
    · exact Or.inl ⟨hn, by
        letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hrow
        rw [bidiagonal_matrix_eq_zero_of_isEmpty_rows x.A]
        exact hasUnitaryBidiagonalizationFixedRightHead_zero⟩
    · exact Or.inr (not_nonempty_iff.mp hn)
  · exact Or.inr (Fintype.card_eq_zero_iff.mp hcol)

noncomputable def bidiagonalization_strategy_data
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationStepOracle 𝕜 m n)
    (hooks : BidiagonalizationDescentHooks oracle) :
    RectStrategyData 𝕜 (Bidiagonalization_P 𝕜) :=
  mkRectStrategyData
    (bidiagonalization_strategy_core 𝕜 oracle)
    (bidiagonalization_strategy_proof oracle hooks)

noncomputable def bidiagonalization_framework_inst
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationStepOracle 𝕜 m n)
    (hooks : BidiagonalizationDescentHooks oracle) :
    RectSubtypeInductionInstance 𝕜 :=
  mkRectSubtypeInductionInstanceFromStrategy
    (Bidiagonalization_P 𝕜)
    bidiagonalization_base_univ
    (bidiagonalization_strategy_data oracle hooks)

noncomputable def bidiagonalization_boundary_strategy_data
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationBoundaryStepOracle 𝕜 m n)
    (hooks : BidiagonalizationBoundaryDescentHooks oracle) :
    RectStrategyData 𝕜 (BidiagonalizationFixedRightHead_P 𝕜) :=
  mkRectStrategyData
    (bidiagonalization_boundary_strategy_core 𝕜 oracle)
    (bidiagonalization_boundary_strategy_proof oracle hooks)

noncomputable def bidiagonalization_boundary_framework_inst
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationBoundaryStepOracle 𝕜 m n)
    (hooks : BidiagonalizationBoundaryDescentHooks oracle) :
    RectSubtypeInductionInstance 𝕜 :=
  mkRectSubtypeInductionInstanceFromStrategy
    (BidiagonalizationFixedRightHead_P 𝕜)
    bidiagonalization_fixedRightHead_base_univ
    (bidiagonalization_boundary_strategy_data oracle hooks)

/-- Framework-routed unitary bidiagonalization theorem from explicit proof hooks. -/
theorem exists_unitary_bidiagonalization_framework
    (oracle :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        BidiagonalizationStepOracle 𝕜 p q)
    (hooks : BidiagonalizationDescentHooks oracle)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) :
    HasUnitaryBidiagonalization A := by
  have hP :
      (bidiagonalization_framework_inst oracle hooks).P (RectUniverse.ofMatrix A) :=
    RectSubtypeInductionInstance.prove_for_matrix
      (inst := bidiagonalization_framework_inst oracle hooks) A
  exact hP

/--
Framework-routed boundary-aware fixed-right-head target from explicit proof
hooks.
-/
theorem exists_unitary_bidiagonalization_fixedRightHead_framework
    (oracle :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        BidiagonalizationBoundaryStepOracle 𝕜 p q)
    (hooks : BidiagonalizationBoundaryDescentHooks oracle)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) :
    BidiagonalizationFixedRightHead_P 𝕜 (RectUniverse.ofMatrix A) := by
  have hP :
      (bidiagonalization_boundary_framework_inst oracle hooks).P
        (RectUniverse.ofMatrix A) :=
    RectSubtypeInductionInstance.prove_for_matrix
      (inst := bidiagonalization_boundary_framework_inst oracle hooks) A
  exact hP

/--
Framework-routed unitary bidiagonalization through the boundary-aware
fixed-right-head driver.
-/
theorem exists_unitary_bidiagonalization_boundary_framework
    (oracle :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        BidiagonalizationBoundaryStepOracle 𝕜 p q)
    (hooks : BidiagonalizationBoundaryDescentHooks oracle)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) :
    HasUnitaryBidiagonalization A := by
  exact bidiagonalization_P_of_fixedRightHead_P 𝕜 (RectUniverse.ofMatrix A)
    (exists_unitary_bidiagonalization_fixedRightHead_framework oracle hooks A)

/-- Framework-routed unitary bidiagonalization theorem conditional on the one-step oracle. -/
theorem exists_unitary_bidiagonalization_oracle
    (oracle :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        BidiagonalizationStepOracle 𝕜 p q)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) :
    HasUnitaryBidiagonalization A := by
  exact exists_unitary_bidiagonalization_framework oracle
    (bidiagonalization_descent_hooks oracle) A

/--
Framework-routed unitary bidiagonalization conditional on a boundary-aware
fixed-right-head one-step oracle.
-/
theorem exists_unitary_bidiagonalization_boundary_oracle
    (oracle :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        BidiagonalizationBoundaryStepOracle 𝕜 p q)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) :
    HasUnitaryBidiagonalization A := by
  exact exists_unitary_bidiagonalization_boundary_framework oracle
    (bidiagonalization_boundary_descent_hooks oracle) A

/-- Framework-routed real orthogonal bidiagonalization conditional on a real one-step oracle. -/
theorem exists_orthogonal_bidiagonalization_oracle
    (oracle :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        BidiagonalizationStepOracle ℝ p q)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℝ) :
    HasOrthogonalBidiagonalization A := by
  exact hasOrthogonalBidiagonalization_of_hasUnitary
    (exists_unitary_bidiagonalization_oracle oracle A)

end MatDecompFormal.Instances
