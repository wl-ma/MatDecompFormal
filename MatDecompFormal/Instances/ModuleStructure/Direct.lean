import MatDecompFormal.Instances.ModuleStructure.Strategy

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# PID Module Structure Direct Hooks

Proof-side hooks for the finite-presentation module-structure descent.  The
transport and lift operations mirror Smith normal form because the current
target is the Smith decomposition of a presentation matrix.
-/

structure ModuleStructureDescentHooks
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
        [Nonempty rel] [Fintype gen] [DecidableEq gen] [LinearOrder gen]
        [Nonempty gen],
        ModuleStructureStepOracle R rel gen) where
  proofData :
    RectStrategyProofData R ModuleStructure_P
      (moduleStructure_strategy_core R oracle)

noncomputable def moduleStructure_transport_hook
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
        [Nonempty rel] [Fintype gen] [DecidableEq gen] [LinearOrder gen]
        [Nonempty gen],
        ModuleStructureStepOracle R rel gen) :
    RectStrategyTransportType ModuleStructure_P
      (moduleStructure_strategy_core R oracle) := by
  intro rel gen frel drel orel nrel fgen dgen ogen ngen A B hrel hPB
  rcases hrel with hBA | hBA
  · subst B
    exact hPB
  · rcases hBA with ⟨t, rfl⟩
    exact moduleStructure_transport_twoSidedUnits t.1.1 t.1.2 A
      (t.1.1 * A * t.1.2) t.2.1 t.2.2 rfl hPB

noncomputable def moduleStructure_lift_hook
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
        [Nonempty rel] [Fintype gen] [DecidableEq gen] [LinearOrder gen]
        [Nonempty gen],
        ModuleStructureStepOracle R rel gen) :
    RectStrategyLiftType ModuleStructure_P
      (moduleStructure_strategy_core R oracle) := by
  intro rel gen frel drel orel nrel fgen dgen ogen ngen A hA hTail
  let er := headTailEquiv (α := rel)
  let ec := headTailEquiv (α := gen)
  let A' := Matrix.reindex er ec A
  rcases hA with ⟨d, h11, h12, h21, hdiv⟩
  have hTailSmith : HasSmithNormalForm A'.toBlocks₂₂ := by
    have hTailModule : HasPIDModuleStructure A'.toBlocks₂₂ := by
      simpa [moduleStructure_strategy_core, smithHeadTailReduction,
        SubmatrixMethod, SmithTailRowIdx, SmithTailColIdx, er, ec, A'] using hTail
    exact smith_of_hasPIDModuleStructure hTailModule
  have hA'Smith : HasSmithNormalForm A' :=
    smith_of_blockReady_reindex A' d h11 h12 h21 hdiv hTailSmith
  have hBackSmith : HasSmithNormalForm (Matrix.reindex er.symm ec.symm A') :=
    smith_reindex er.symm ec.symm hA'Smith
  have hBackModule : HasPIDModuleStructure (Matrix.reindex er.symm ec.symm A') :=
    hasPIDModuleStructure_of_smith hBackSmith
  simpa [A', er, ec] using hBackModule

noncomputable def moduleStructure_descent_hooks
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
        [Nonempty rel] [Fintype gen] [DecidableEq gen] [LinearOrder gen]
        [Nonempty gen],
        ModuleStructureStepOracle R rel gen) :
    ModuleStructureDescentHooks R oracle where
  proofData :=
    { transport := moduleStructure_transport_hook R oracle
      lift := moduleStructure_lift_hook R oracle }

noncomputable def moduleStructure_strategy_proof
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
        [Nonempty rel] [Fintype gen] [DecidableEq gen] [LinearOrder gen]
        [Nonempty gen],
        ModuleStructureStepOracle R rel gen)
    (hooks : ModuleStructureDescentHooks R oracle) :
    RectStrategyProofData R ModuleStructure_P
      (moduleStructure_strategy_core R oracle) :=
  hooks.proofData

end MatDecompFormal.Instances
