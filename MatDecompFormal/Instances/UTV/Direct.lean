import MatDecompFormal.Instances.UTV.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# UTV Direct Hooks

This file packages the transport and lift hooks required by the rectangular
descent template for UTV.
-/

structure UTVDescentHooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n) where
  proofData :
    RectStrategyProofData ℂ UTV_P (utv_strategy_core oracle)

noncomputable def utv_transport_hook
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n) :
    RectStrategyTransportType UTV_P (utv_strategy_core oracle) := by
  intro m n fm dm om nm fn dn on nn A B hrel hPB
  rcases hrel with hBA | hBA
  · subst B
    exact hPB
  · rcases hBA with ⟨t, rfl⟩
    exact utv_transport_twoSidedUnitary t.1.1 t.1.2 A
      (t.1.1ᴴ * A * t.1.2) t.2.1 t.2.2 rfl hPB

noncomputable def utv_lift_hook
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n) :
    RectStrategyLiftType UTV_P (utv_strategy_core oracle) := by
  intro m n fm dm om nm fn dn on nn A hA hTail
  let er := headTailEquiv (α := m)
  let ec := headTailEquiv (α := n)
  let A' := Matrix.reindex er ec A
  rcases hA with ⟨σ, hσ, h11, h12, h21⟩
  have hTailUTV : HasUTV A'.toBlocks₂₂ := by
    simpa [utvHeadTailReduction, SubmatrixMethod, UTVTailRowIdx, UTVTailColIdx,
      SVDTailRowIdx, SVDTailColIdx, er, ec, A'] using hTail
  have hA'UTV : HasUTV A' :=
    utv_of_blockReady_reindex A' σ hσ h11 h12 h21 hTailUTV
  have hBack : HasUTV (Matrix.reindex er.symm ec.symm A') :=
    utv_reindex er.symm ec.symm hA'UTV
  simpa [A', er, ec] using hBack

noncomputable def utv_descent_hooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n) :
    UTVDescentHooks oracle where
  proofData :=
    { transport := utv_transport_hook oracle
      lift := utv_lift_hook oracle }

noncomputable def utv_strategy_proof
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n)
    (hooks : UTVDescentHooks oracle) :
    RectStrategyProofData ℂ UTV_P (utv_strategy_core oracle) :=
  hooks.proofData

end MatDecompFormal.Instances
