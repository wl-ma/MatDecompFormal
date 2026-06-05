import MatDecompFormal.Instances.Smith.Direct
import MatDecompFormal.Instances.Gauss.Existence

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Smith Normal Form: Framework Entry

This file assembles the Smith normal-form target through the rectangular
universe driver. The hard PID/Euclidean one-step reduction is left as the
explicit `SmithStepOracle`, matching the first implementation stage in the plan.
-/

variable {R : Type u} [CommSemiring R]

/--
Rank-normal-form route to Smith normal form, conditional on the Gauss one-step
oracle. This discharges the plan's field/rank-normal-form bridge while keeping
the remaining Gauss elimination oracle explicit.
-/
theorem exists_smith_normal_form_rank_oracle
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A := by
  exact hasSmithNormalForm_of_gauss
    (exists_gauss_rank_normal_form_oracle oracle A)

/-- Universe-level base case for the Smith target. -/
theorem smith_base_univ (x : RectUniverse R) :
    ((∀ (x_sub : PosRectUniverse R), (x_sub : RectUniverse R) ≠ x) ∨
      rectSubtypeμ x ≤ rectSubtypeμBase) →
      Smith_P x := by
  intro hx
  rcases rectSubtypeBaseDimEqZero x hx with hrow | hcol
  · letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hrow
    exact base_smith_empty_rows x.A
  · letI : IsEmpty x.κ := Fintype.card_eq_zero_iff.mp hcol
    exact base_smith_empty_cols x.A

noncomputable def smith_strategy_data
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SmithStepOracle R m n)
    (hooks : SmithDescentHooks R oracle) :
    RectStrategyData R Smith_P :=
  mkRectStrategyData
    (smith_strategy_core R oracle)
    (smith_strategy_proof R oracle hooks)

noncomputable def smith_framework_inst
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SmithStepOracle R m n)
    (hooks : SmithDescentHooks R oracle) :
    RectSubtypeInductionInstance R :=
  mkRectSubtypeInductionInstanceFromStrategy
    Smith_P
    smith_base_univ
    (smith_strategy_data oracle hooks)

/-- Framework-routed Smith theorem with explicit proof hooks. -/
theorem exists_smith_normal_form_framework
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SmithStepOracle R m n)
    (hooks : SmithDescentHooks R oracle)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A := by
  have hP :
      (smith_framework_inst oracle hooks).P (RectUniverse.ofMatrix A) :=
    RectSubtypeInductionInstance.prove_for_matrix
      (inst := smith_framework_inst oracle hooks) A
  exact hP

/-- Framework-routed Smith theorem conditional only on the one-step oracle. -/
theorem exists_smith_normal_form_framework_oracle
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SmithStepOracle R m n)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A := by
  exact exists_smith_normal_form_framework oracle (smith_descent_hooks R oracle) A

/--
Smith framework theorem driven by a Gauss rank-normal-form step oracle.
This is still routed through the Smith rectangular driver; the theorem exposes
that the remaining one-step input is Gauss-style rank reduction.
-/
theorem exists_smith_normal_form_framework_gauss_oracle
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A := by
  exact exists_smith_normal_form_framework_oracle
    (fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        smithStepOracleOfGauss R p q (oracle (m := p) (n := q)))
    A

section Field

variable {R : Type u} [Field R]

/--
Smith normal form over a field. This theorem is routed through the
Smith rectangular descent framework, using the concrete Gauss elementary
one-step oracle through `smithStepOracleOfGauss`.
-/
theorem exists_smith_normal_form_field
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A := by
  exact exists_smith_normal_form_framework_gauss_oracle
    (R := R)
    (fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        gaussRankStepOracle R p q)
    A

/--
Field-scope Smith normal form theorem.

The public `exists_smith_normal_form` name is reserved for the PID-scope theorem
in `Smith/PIDBridge.lean`; the field case remains available under this explicit
name.
-/
theorem exists_smith_normal_form_field_alias
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A :=
  exists_smith_normal_form_field A

end Field

end MatDecompFormal.Instances
