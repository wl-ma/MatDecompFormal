import MatDecompFormal.Instances.Jordan.Direct

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Jordan Form: Framework Entry

This file assembles the Jordan descent strategy through the project square
descent framework.  The theorem is conditional on `JordanStepOracle`;
constructing that oracle from rational canonical form or primary decomposition
is the remaining algebraic work.
-/

/-- Universe-level base case for the Jordan target. -/
theorem jordan_base_univ
    {K : Type u} [Field K] (x : SquareUniverse K) :
    ((∀ (x_sub : PosSquareUniverse K), (x_sub : SquareUniverse K) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      Jordan_P x := by
  intro hx _hsplit
  have hzero : Fintype.card x.ι = 0 :=
    squareSubtypeBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  exact base_jordan_empty x.A

noncomputable def jordan_strategy_data
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        JordanStepOracle K ι) :
    SquareStrategyData K Jordan_P :=
  mkSquareStrategyData
    (jordan_strategy_core K oracle)
    (jordan_strategy_proof K oracle)

noncomputable def jordan_framework_inst
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        JordanStepOracle K ι) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstanceFromStrategy
    Jordan_P
    jordan_base_univ
    (jordan_strategy_data K oracle)

/--
Framework-routed Jordan theorem, conditional on the one-step Jordan oracle.
-/
theorem exists_jordan_matrix_framework
    {K : Type u} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        JordanStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  have hP :
      (jordan_framework_inst K oracle).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := jordan_framework_inst K oracle) A
  exact hP hsplit

/--
Framework-routed Jordan theorem, conditional on the concrete one-step oracle.

The unsuffixed `exists_jordan_matrix_of_splits` name is intentionally reserved
for the later theorem where this oracle is discharged from rational canonical
form, primary decomposition, or nilpotent Jordan chains.
-/
theorem exists_jordan_matrix_framework_oracle
    {K : Type u} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        JordanStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  exact exists_jordan_matrix_framework oracle A hsplit

end MatDecompFormal.Instances
