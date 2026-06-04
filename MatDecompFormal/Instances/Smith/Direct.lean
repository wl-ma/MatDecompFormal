import MatDecompFormal.Instances.Smith.Strategy

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Smith Direct Hooks

This file packages the transport and lift hooks required by the rectangular
descent template for Smith normal form.
-/

structure SmithDescentHooks
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SmithStepOracle R m n) where
  proofData :
    RectStrategyProofData R Smith_P (smith_strategy_core R oracle)

noncomputable def smith_transport_hook
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SmithStepOracle R m n) :
    RectStrategyTransportType Smith_P (smith_strategy_core R oracle) := by
  intro m n fm dm om nm fn dn on nn A B hrel hPB
  rcases hrel with hBA | hBA
  · subst B
    exact hPB
  · rcases hBA with ⟨t, rfl⟩
    exact smith_transport_twoSidedUnits t.1.1 t.1.2 A
      (t.1.1 * A * t.1.2) t.2.1 t.2.2 rfl hPB

noncomputable def smith_lift_hook
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SmithStepOracle R m n) :
    RectStrategyLiftType Smith_P (smith_strategy_core R oracle) := by
  intro m n fm dm om nm fn dn on nn A hA hTail
  let er := headTailEquiv (α := m)
  let ec := headTailEquiv (α := n)
  let A' := Matrix.reindex er ec A
  rcases hA with ⟨d, h11, h12, h21, hdiv⟩
  have hTailSmith : HasSmithNormalForm A'.toBlocks₂₂ := by
    simpa [smithHeadTailReduction, SubmatrixMethod, SmithTailRowIdx, SmithTailColIdx,
      er, ec, A'] using hTail
  have hA'Smith : HasSmithNormalForm A' :=
    smith_of_blockReady_reindex A' d h11 h12 h21 hdiv hTailSmith
  have hBack : HasSmithNormalForm (Matrix.reindex er.symm ec.symm A') :=
    smith_reindex er.symm ec.symm hA'Smith
  simpa [A', er, ec] using hBack

noncomputable def smith_descent_hooks
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SmithStepOracle R m n) :
    SmithDescentHooks R oracle where
  proofData :=
    { transport := smith_transport_hook R oracle
      lift := smith_lift_hook R oracle }

noncomputable def smith_strategy_proof
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SmithStepOracle R m n)
    (hooks : SmithDescentHooks R oracle) :
    RectStrategyProofData R Smith_P (smith_strategy_core R oracle) :=
  hooks.proofData

end MatDecompFormal.Instances

