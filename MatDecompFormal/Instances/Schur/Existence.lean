import MatDecompFormal.Instances.Schur.Direct
import MatDecompFormal.Instances.Schur.Spectral

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Algebraic and Unitary Schur Triangularization: Framework Entry

This file assembles the Schur descent strategies through the square universe
driver:

```lean
SquareStrategyData
mkSquareSubtypeInductionInstanceFromStrategy
SquareSubtypeInductionInstance.prove_for_matrix
```

The theorem `exists_schur` is the algebraic invertible-similarity
triangularization over an algebraically closed field.  The complex unitary
Schur API is separate; its unconditional entry point is
`exists_unitary_schur`, assembled from the concrete orthonormal
eigenvector/basis-completion step in `Spectral.lean`.
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
Conditional framework-routed algebraic Schur triangularization theorem.

This theorem is already assembled through the square descent driver. The
remaining mathematical work is to construct the one-step oracle and the
transport/lift hooks supplied by the Schur direct/spectral modules.
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
Framework-routed algebraic Schur theorem conditional on the one-step
invertible-similarity oracle and the concrete transport/lift hooks constructed
in `Direct.lean`.
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
Algebraic Schur triangularization over an algebraically closed field, routed
through the project square descent framework.

The witness similarity is an arbitrary invertible matrix.  This is not the
complex unitary Schur theorem; see `HasUnitarySchur` and
`exists_unitary_schur` for the separate unitary API.
-/
theorem exists_schur
    {K : Type u} [Field K] [IsAlgClosed K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasSchur A := by
  exact exists_schur_framework_oracle
    (schur_step_oracle_of_isAlgClosed K) A

/-- Universe-level base case for the unitary Schur target. -/
theorem unitarySchur_base_univ (x : SquareUniverse ℂ) :
    ((∀ (x_sub : PosSquareUniverse ℂ), (x_sub : SquareUniverse ℂ) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      UnitarySchur_P x := by
  intro hx
  exact base_unitarySchur_zero_dim_sq
    (squareSubtypeBaseDimEqZero x hx)

noncomputable def unitary_schur_strategy_data
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        UnitarySchurStepOracle ι)
    (hooks : UnitarySchurDescentHooks oracle) :
    SquareStrategyData ℂ UnitarySchur_P :=
  mkSquareStrategyData
    (unitary_schur_strategy_core oracle)
    (unitary_schur_strategy_proof oracle hooks)

noncomputable def unitary_schur_framework_inst
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        UnitarySchurStepOracle ι)
    (hooks : UnitarySchurDescentHooks oracle) :
    SquareSubtypeInductionInstance ℂ :=
  mkSquareSubtypeInductionInstanceFromStrategy
    UnitarySchur_P
    unitarySchur_base_univ
    (unitary_schur_strategy_data oracle hooks)

/--
Conditional framework-routed unitary Schur theorem.

The explicit `UnitarySchurStepOracle` parameter is the remaining mathematical
unitary step: choose an eigenvector, extend it to an orthonormal basis, and make
the lower-left head-tail block vanish by unitary similarity.
-/
theorem exists_unitary_schur_framework
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        UnitarySchurStepOracle κ)
    (hooks : UnitarySchurDescentHooks oracle)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasUnitarySchur A := by
  have hP :
      (unitary_schur_framework_inst oracle hooks).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := unitary_schur_framework_inst oracle hooks) A
  exact hP

/--
Unitary Schur decomposition conditional on the explicit one-step unitary oracle.

This is intentionally weaker than an unconditional theorem only in its
assumptions, not in its conclusion: it proves the full `HasUnitarySchur` target
from a genuine unitary step oracle.
-/
theorem exists_unitary_schur_of_oracle
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        UnitarySchurStepOracle κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasUnitarySchur A := by
  exact exists_unitary_schur_framework
    oracle (unitary_schur_descent_hooks oracle) A

/--
Complex unitary Schur decomposition for finite square matrices.

There are no spectral oracle assumptions: the one-step unitary similarity is
constructed in `Schur.Spectral` by choosing an eigenvector, normalizing it, and
extending it to an orthonormal basis.
-/
theorem exists_unitary_schur
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasUnitarySchur A := by
  exact exists_unitary_schur_of_oracle unitarySchurStepOracle A

end MatDecompFormal.Instances
