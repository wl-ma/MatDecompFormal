import MatDecompFormal.Instances.Gauss.Strategy

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Gauss Rank Normal Form Direct Hooks

Proof-side hooks needed by the rectangular descent template.
-/

variable {R : Type v} [Semiring R]

/-- Proof hooks needed to turn the Gauss strategy core into driver data. -/
structure GaussRankDescentHooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n) where
  proofData :
    RectStrategyProofData R GaussRank_P (gauss_strategy_core oracle)

noncomputable def gauss_transport_hook
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n) :
    RectStrategyTransportType GaussRank_P (gauss_strategy_core oracle) := by
  intro m n fm dm om nm fn dn on nn A B hrel hPB
  rcases hrel with hBA | hBA
  · subst B
    exact hPB
  · rcases hBA with ⟨t, rfl⟩
    exact gauss_transport_twoSidedUnits t.1.1 t.1.2 A
      (t.1.1 * A * t.1.2) t.2.1 t.2.2 rfl hPB

noncomputable def gauss_lift_hook
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n) :
    RectStrategyLiftType GaussRank_P (gauss_strategy_core oracle) := by
  intro m n fm dm om nm fn dn on nn A hA hTail
  let er := headTailEquiv (α := m)
  let ec := headTailEquiv (α := n)
  let A' := Matrix.reindex er ec A
  rcases hA with hZero | hBlock
  · rw [hZero]
    exact hasGaussRankNormalForm_zero
  · rcases hBlock with ⟨h11, h12, h21⟩
    have hTailNF : HasGaussRankNormalForm A'.toBlocks₂₂ := by
      simpa [gaussHeadTailReduction, SubmatrixMethod, GaussTailRowIdx, GaussTailColIdx,
        er, ec, A'] using hTail
    have hA'NF : HasGaussRankNormalForm A' :=
      gauss_of_blockReady_reindex A' h11 h12 h21 hTailNF
    have hBack : HasGaussRankNormalForm (Matrix.reindex er.symm ec.symm A') :=
      hasGaussRankNormalForm_reindex er.symm ec.symm hA'NF
    simpa [A', er, ec] using hBack

noncomputable def gauss_descent_hooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n) :
    GaussRankDescentHooks oracle where
  proofData :=
    { transport := gauss_transport_hook oracle
      lift := gauss_lift_hook oracle }

noncomputable def gauss_strategy_proof
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n)
    (hooks : GaussRankDescentHooks oracle) :
    RectStrategyProofData R GaussRank_P (gauss_strategy_core oracle) :=
  hooks.proofData

end MatDecompFormal.Instances
