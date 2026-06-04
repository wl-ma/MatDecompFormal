import MatDecompFormal.Instances.Gauss.Direct
import MatDecompFormal.Instances.Gauss.Elementary

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Gauss Rank Normal Form: Framework Entry

This file assembles Gauss/rank normal form through the rectangular descent
driver.
-/

variable {R : Type v} [Semiring R]

/-- Universe-level base case for the Gauss/rank-normal-form target. -/
theorem gauss_base_univ (x : RectUniverse R) :
    ((∀ (x_sub : PosRectUniverse R), (x_sub : RectUniverse R) ≠ x) ∨
      rectSubtypeμ x ≤ rectSubtypeμBase) →
      GaussRank_P x := by
  intro hx
  rcases rectSubtypeBaseDimEqZero x hx with hrow | hcol
  · letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hrow
    exact base_gauss_empty_rows x.A
  · letI : IsEmpty x.κ := Fintype.card_eq_zero_iff.mp hcol
    exact base_gauss_empty_cols x.A

noncomputable def gauss_strategy_data
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n)
    (hooks : GaussRankDescentHooks oracle) :
    RectStrategyData R GaussRank_P :=
  mkRectStrategyData
    (gauss_strategy_core oracle)
    (gauss_strategy_proof oracle hooks)

noncomputable def gauss_framework_inst
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n)
    (hooks : GaussRankDescentHooks oracle) :
    RectSubtypeInductionInstance R :=
  mkRectSubtypeInductionInstanceFromStrategy
    GaussRank_P
    gauss_base_univ
    (gauss_strategy_data oracle hooks)

/--
Framework-routed Gauss/rank-normal-form theorem conditional on the one-step
Gauss elimination oracle.
-/
theorem exists_gauss_rank_normal_form_framework
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n)
    (hooks : GaussRankDescentHooks oracle)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasGaussRankNormalForm A := by
  have hP :
      (gauss_framework_inst oracle hooks).P (RectUniverse.ofMatrix A) :=
    RectSubtypeInductionInstance.prove_for_matrix
      (inst := gauss_framework_inst oracle hooks) A
  exact hP

/--
Framework-routed Gauss/rank-normal-form theorem using the concrete proof hooks.
The remaining input is exactly the one-step Gauss elimination oracle.
-/
theorem exists_gauss_rank_normal_form_oracle
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasGaussRankNormalForm A :=
  exists_gauss_rank_normal_form_framework oracle (gauss_descent_hooks oracle) A

section Concrete

variable {R : Type v} [DivisionRing R]

/--
Gauss/rank-normal-form existence over a division ring, routed through the
rectangular descent driver and the concrete elementary one-step oracle.
-/
theorem exists_gauss_rank_normal_form
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasGaussRankNormalForm A :=
  exists_gauss_rank_normal_form_oracle
    (R := R)
    (fun {p q} _ _ _ _ _ _ _ _ => gaussRankStepOracle R p q)
    A

end Concrete

end MatDecompFormal.Instances
