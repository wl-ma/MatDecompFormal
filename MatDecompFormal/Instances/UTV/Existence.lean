import MatDecompFormal.Instances.SVD.Spectral
import MatDecompFormal.Instances.Gauss.Existence
import MatDecompFormal.Instances.UTV.Direct

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# UTV Decomposition: Framework Entry

This file assembles UTV through the rectangular universe driver:

```lean
RectStrategyData
mkRectSubtypeInductionInstanceFromStrategy
RectSubtypeInductionInstance.prove_for_matrix
```
-/

variable {R : Type u} [Semiring R]

/--
Generic framework-routed triangular equivalence conditional on the Gauss
one-step oracle.

This is the generic UTV/equivalence route from the plan. The remaining
mathematical input is exactly the field-level Gauss elimination oracle; the
public theorem name keeps that dependency explicit.
-/
theorem exists_triangular_equivalence_framework_oracle
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasTriangularEquivalence A := by
  exact hasTriangularEquivalence_of_gauss
    (exists_gauss_rank_normal_form_oracle oracle A)

/--
Generic triangular equivalence over a division ring, routed through the
rectangular Gauss descent framework and the concrete elementary-step oracle.
-/
theorem exists_triangular_equivalence
    {R : Type u} [DivisionRing R]
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasTriangularEquivalence A := by
  exact exists_triangular_equivalence_framework_oracle
    (R := R)
    (fun {p q} _ _ _ _ _ _ _ _ => gaussRankStepOracle R p q)
    A

/-- Universe-level base case for the UTV target. -/
theorem utv_base_univ (x : RectUniverse ℂ) :
    ((∀ (x_sub : PosRectUniverse ℂ), (x_sub : RectUniverse ℂ) ≠ x) ∨
      rectSubtypeμ x ≤ rectSubtypeμBase) →
      UTV_P x := by
  intro hx
  rcases rectSubtypeBaseDimEqZero x hx with hrow | hcol
  · letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hrow
    exact base_utv_empty_rows x.A
  · letI : IsEmpty x.κ := Fintype.card_eq_zero_iff.mp hcol
    exact base_utv_empty_cols x.A

noncomputable def utv_strategy_data
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n)
    (hooks : UTVDescentHooks oracle) :
    RectStrategyData ℂ UTV_P :=
  mkRectStrategyData
    (utv_strategy_core oracle)
    (utv_strategy_proof oracle hooks)

noncomputable def utv_framework_inst
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n)
    (hooks : UTVDescentHooks oracle) :
    RectSubtypeInductionInstance ℂ :=
  mkRectSubtypeInductionInstanceFromStrategy
    UTV_P
    utv_base_univ
    (utv_strategy_data oracle hooks)

/-- Framework-routed UTV theorem with explicit proof hooks. -/
theorem exists_utv_framework
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n)
    (hooks : UTVDescentHooks oracle)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasUTV A := by
  have hP :
      (utv_framework_inst oracle hooks).P (RectUniverse.ofMatrix A) :=
    RectSubtypeInductionInstance.prove_for_matrix
      (inst := utv_framework_inst oracle hooks) A
  exact hP

/-- Framework-routed UTV theorem conditional only on the one-step oracle. -/
theorem exists_utv_framework_oracle
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasUTV A := by
  exact exists_utv_framework oracle (utv_descent_hooks oracle) A

/-- One-step UTV oracle obtained from the already formalized SVD head-basis data. -/
noncomputable def utv_step_oracle
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    UTVSimilarityOracle m n :=
  utvSimilarityOracleOfSVDBlockReady m n
    (svdBlockReadyOracleOfHeadSingularVectorData m n
      (svdHeadSingularVectorDataOfHeadBasisData m n (svdHeadBasisData m n)))

/-- Unconditional complex UTV decomposition through the rectangular descent framework. -/
theorem exists_utv
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasUTV A := by
  exact exists_utv_framework_oracle
    (fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        utv_step_oracle (m := p) (n := q))
    A

end MatDecompFormal.Instances
