import MatDecompFormal.Instances.ModuleStructure.Details
import MatDecompFormal.Instances.Smith.Strategy

universe u v

namespace MatDecompFormal.Instances

open MatDecompFormal.Framework

/-!
# PID Module Structure Strategy

The presentation-matrix module-structure descent uses the same rectangular
Smith step: isolate one Smith pivot, recurse on the lower-right presentation
matrix, and lift the tail decomposition by adding the cyclic/free summand
encoded by the pivot.
-/

abbrev ModuleStructureTailRowIdx
    (rel : Type u) [Fintype rel] [LinearOrder rel] [Nonempty rel] :=
  SmithTailRowIdx rel

abbrev ModuleStructureTailColIdx
    (gen : Type u) [Fintype gen] [LinearOrder gen] [Nonempty gen] :=
  SmithTailColIdx gen

abbrev ModuleStructureDescentReady
    (R : Type v) [CommSemiring R]
    (rel gen : Type u) [Fintype rel] [LinearOrder rel] [Nonempty rel]
    [Fintype gen] [LinearOrder gen] [Nonempty gen] :=
  SmithDescentReady R rel gen

abbrev ModuleStructureStepOracle
    (R : Type v) [CommSemiring R]
    (rel gen : Type u) [Fintype rel] [DecidableEq rel] [LinearOrder rel] [Nonempty rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen] [Nonempty gen] :=
  SmithStepOracle R rel gen

noncomputable def moduleStructure_strategy_core
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {rel gen : Type u} [Fintype rel] [DecidableEq rel] [LinearOrder rel]
        [Nonempty rel] [Fintype gen] [DecidableEq gen] [LinearOrder gen]
        [Nonempty gen],
        ModuleStructureStepOracle R rel gen) :
    RectStrategyCore R :=
  smith_strategy_core R oracle

end MatDecompFormal.Instances
