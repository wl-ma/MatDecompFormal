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
keeps the remaining PID Smith-step obligation named, instead of hiding it as a
field-only theorem or as an anonymous higher-order parameter.
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

section PID

variable {R : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/--
PID Smith-step bridge for the module-structure descent.

This is the remaining algebraic content needed for an unconditional PID module
structure theorem through the descent template: every nonempty finite
presentation matrix must have the one-step Smith pivot isolation used by the
rectangular driver.
-/
structure PIDModuleStructureStepBridge
    (R : Type v) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] where
  stepOracle :
    ∀ {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
      [Nonempty rel] [Fintype gen] [DecidableEq gen] [LinearOrder gen]
      [Nonempty gen],
      ModuleStructureStepOracle R rel gen

/--
Framework-routed PID finite-presentation module-structure theorem, conditional
on the named PID Smith-step bridge.

This is an internal descent-template entry point.  The public PID theorem below
is stated through the Smith matrix bridge instead of exposing this one-step
oracle directly.
-/
theorem exists_presented_pid_module_structure_step_bridge
    (bridge : PIDModuleStructureStepBridge.{u, v} R)
    {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPresentedPIDModuleStructure A := by
  simpa [HasPresentedPIDModuleStructure] using
    (exists_structure_of_presentation_oracle
      (R := R) bridge.stepOracle A)

/-- Matrix-level version of `exists_presented_pid_module_structure_step_bridge`. -/
theorem exists_structure_of_presentation_pid_step_bridge
    (bridge : PIDModuleStructureStepBridge.{u, v} R)
    {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPIDModuleStructure A := by
  exact exists_structure_of_presentation_oracle
    (R := R) bridge.stepOracle A

end PID

section PublicPID

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/--
PID finite-presentation module-structure theorem.

This is the public PID-level theorem for presentation matrices.  It depends on
the public PID Smith normal-form theorem; once the presentation matrix has
Smith normal form, the module-structure payload is immediate.
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

end PublicPID

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
