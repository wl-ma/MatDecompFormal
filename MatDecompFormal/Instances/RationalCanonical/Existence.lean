import MatDecompFormal.Instances.RationalCanonical.Direct

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Rational Canonical Form: Framework Entry

This file assembles the matrix-indexed rational-canonical theorem through the
project square descent framework. The theorem is conditional on
`RationalCanonicalStepOracle`; constructing that oracle is the remaining
`K[X]` module-structure work.
-/

/-- Universe-level base case for the rational-canonical target. -/
theorem rationalCanonical_base_univ
    {K : Type v} [Field K] (x : SquareUniverse K) :
    ((∀ (x_sub : PosSquareUniverse K), (x_sub : SquareUniverse K) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      RationalCanonical_P x := by
  intro hx
  have hzero : Fintype.card x.ι = 0 :=
    squareSubtypeBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  exact base_rationalCanonical_empty x.A

noncomputable def rationalCanonical_strategy_data
    (K : Type v) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        RationalCanonicalStepOracle K ι) :
    SquareStrategyData K RationalCanonical_P :=
  mkSquareStrategyData
    (rationalCanonical_strategy_core K oracle)
    (rationalCanonical_strategy_proof oracle)

noncomputable def rationalCanonical_framework_inst
    (K : Type v) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        RationalCanonicalStepOracle K ι) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstanceFromStrategy
    RationalCanonical_P
    rationalCanonical_base_univ
    (rationalCanonical_strategy_data K oracle)

/--
Framework-routed rational canonical form theorem, conditional on the
one-step cyclic-summand oracle.
-/
theorem exists_rational_canonical_matrix_framework
    {K : Type v} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        RationalCanonicalStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasRationalCanonical A := by
  have hP :
      (rationalCanonical_framework_inst K oracle).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := rationalCanonical_framework_inst K oracle) A
  exact hP

end MatDecompFormal.Instances
