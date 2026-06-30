/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
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

/-- Row tail index for module-structure descent, aliased to `SmithTailRowIdx`. -/
abbrev ModuleStructureTailRowIdx
    (rel : Type u) [Fintype rel] [LinearOrder rel] [Nonempty rel] :=
  SmithTailRowIdx rel

/-- Column tail index for module-structure descent, aliased to `SmithTailColIdx`. -/
abbrev ModuleStructureTailColIdx
    (gen : Type u) [Fintype gen] [LinearOrder gen] [Nonempty gen] :=
  SmithTailColIdx gen

/-- Descent-ready predicate for module-structure, aliased to `SmithDescentReady`. -/
abbrev ModuleStructureDescentReady
    (R : Type v) [CommSemiring R]
    (rel gen : Type u) [Fintype rel] [LinearOrder rel] [Nonempty rel]
    [Fintype gen] [LinearOrder gen] [Nonempty gen] :=
  SmithDescentReady R rel gen

/-- Step oracle for module-structure descent, aliased to `SmithStepOracle`. -/
abbrev ModuleStructureStepOracle
    (R : Type v) [CommSemiring R]
    (rel gen : Type u) [Fintype rel] [DecidableEq rel] [LinearOrder rel] [Nonempty rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen] [Nonempty gen] :=
  SmithStepOracle R rel gen

/-- The `RectStrategyCore` for module-structure descent, delegating to `smith_strategy_core`. -/
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
