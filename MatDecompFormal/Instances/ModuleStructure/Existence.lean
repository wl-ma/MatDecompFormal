/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.ModuleStructure.Direct
import MatDecompFormal.Instances.Gauss.Elementary
import MatDecompFormal.Instances.Smith.PIDBridge

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# PID Module Structure: Framework Entry

This file assembles the finite-presentation module-structure target through the
rectangular descent driver.  The main framework theorem is conditional on the
same Smith one-step oracle used by Smith normal form.  The PID-scope theorem
uses the unconditional PID Smith normal-form theorem, so its public statement
has only the usual algebraic hypotheses.
-/

variable {R : Type v} [CommSemiring R]

/-- Universe-level base case for finite-presentation module structure. -/
theorem moduleStructure_base_univ (x : RectUniverse R) :
    ((∀ (x_sub : PosRectUniverse R), (x_sub : RectUniverse R) ≠ x) ∨
      rectSubtypeμ x ≤ rectSubtypeμBase) →
      ModuleStructure_P x := by
  intro hx
  rcases rectSubtypeBaseDimEqZero x hx with hrow | hcol
  · letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hrow
    exact base_moduleStructure_empty_rows x.A
  · letI : IsEmpty x.κ := Fintype.card_eq_zero_iff.mp hcol
    exact base_moduleStructure_empty_cols x.A

noncomputable def moduleStructure_strategy_data
    (oracle :
      ∀ {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
        [Nonempty rel] [Fintype gen] [DecidableEq gen] [LinearOrder gen]
        [Nonempty gen],
        ModuleStructureStepOracle R rel gen)
    (hooks : ModuleStructureDescentHooks R oracle) :
    RectStrategyData R ModuleStructure_P :=
  mkRectStrategyData
    (moduleStructure_strategy_core R oracle)
    (moduleStructure_strategy_proof R oracle hooks)

noncomputable def moduleStructure_framework_inst
    (oracle :
      ∀ {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
        [Nonempty rel] [Fintype gen] [DecidableEq gen] [LinearOrder gen]
        [Nonempty gen],
        ModuleStructureStepOracle R rel gen)
    (hooks : ModuleStructureDescentHooks R oracle) :
    RectSubtypeInductionInstance R :=
  mkRectSubtypeInductionInstanceFromStrategy
    ModuleStructure_P
    moduleStructure_base_univ
    (moduleStructure_strategy_data oracle hooks)

/-- Framework-routed presentation module-structure theorem with explicit hooks. -/
theorem exists_structure_of_presentation_framework
    (oracle :
      ∀ {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
        [Nonempty rel] [Fintype gen] [DecidableEq gen] [LinearOrder gen]
        [Nonempty gen],
        ModuleStructureStepOracle R rel gen)
    (hooks : ModuleStructureDescentHooks R oracle)
    {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPIDModuleStructure A := by
  have hP :
      (moduleStructure_framework_inst oracle hooks).P (RectUniverse.ofMatrix A) :=
    RectSubtypeInductionInstance.prove_for_matrix
      (inst := moduleStructure_framework_inst oracle hooks) A
  exact hP

/-- Framework-routed presentation theorem conditional only on a Smith step oracle. -/
theorem exists_structure_of_presentation_oracle
    (oracle :
      ∀ {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
        [Nonempty rel] [Fintype gen] [DecidableEq gen] [LinearOrder gen]
        [Nonempty gen],
        ModuleStructureStepOracle R rel gen)
    {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPIDModuleStructure A :=
  exists_structure_of_presentation_framework oracle
    (moduleStructure_descent_hooks R oracle) A

section PublicPID

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/--
PID finite-presentation module-structure theorem.

Once the presentation matrix has strengthened Smith normal form, the
module-structure payload is immediate. The Smith theorem used here is the
framework-routed public PID theorem, so this result is an indirect framework
route without exposing the Smith bridge or oracle in its statement.
-/
theorem exists_presented_pid_module_structure
    {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPresentedPIDModuleStructure A := by
  simpa [HasPresentedPIDModuleStructure] using
    (hasPIDModuleStructure_of_smith
      (exists_smith_normal_form (R := R) A))

/-- Matrix-level version of `exists_presented_pid_module_structure`. -/
theorem exists_structure_of_presentation_pid
    {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPIDModuleStructure A :=
  hasPIDModuleStructure_of_smith
    (exists_smith_normal_form (R := R) A)

/--
Public PID matrix-level structure theorem for a finite presentation.

This keeps the plan-level name available while
`exists_structure_of_presentation_pid` remains as the explicit PID-suffixed
compatibility name.
-/
theorem exists_structure_of_presentation
    {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPIDModuleStructure A :=
  exists_structure_of_presentation_pid A

end PublicPID

/--
Abstract finitely generated PID module structure theorem, conditional on the
missing finite-presentation/cokernel bridge.

The bridge carries the actual isomorphism
`M ≃ₗ[R] R^freeRank × ∏ᵢ R/(dᵢ)`.  This statement is intentionally not the
unconditional classification theorem yet; it isolates the remaining quotient
module infrastructure needed to derive such a bridge from an arbitrary
`[Module.Finite R M]`.
-/
theorem exists_pid_module_structure_of_bridge
    {R M : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (bridge : PIDModuleDecompositionBridge R M) :
    ∃ freeRank torsionData,
      PIDModuleDecomposition R M freeRank torsionData :=
  bridge.exists_decomposition

section Field

variable {R : Type v} [Field R]

/--
Concrete presentation module-structure theorem over a field.  It is
obtained from the rectangular module-structure driver using the Smith step
oracle induced by the concrete Gauss rank-normal-form oracle.
-/
theorem exists_structure_of_presentation_field
    {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPIDModuleStructure A :=
  exists_structure_of_presentation_oracle
    (R := R)
    (fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        smithStepOracleOfGauss R p q (gaussRankStepOracle R p q))
    A

/--
Concrete field specialization of the finite-presentation theorem.  This is not
the PID-scope theorem; it discharges the Smith step oracle through Gauss rank
normal form over a field.
-/
theorem exists_presented_module_structure_field
    {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPresentedPIDModuleStructure A :=
  exists_structure_of_presentation_field A

end Field

end MatDecompFormal.Instances
