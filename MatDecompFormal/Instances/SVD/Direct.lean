/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.SVD.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Singular Value Decomposition Direct Hooks

This file packages the proof-side hooks needed by the rectangular descent
template for SVD. Both the two-sided unitary transport and the head-tail block
lift are proved concretely.
-/

/--
Proof hooks needed to turn the SVD strategy core into a
`RectStrategyProofData` instance.
-/
structure SVDDescentHooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SVDSimilarityOracle m n) where
  proofData :
    RectStrategyProofData ℂ SVD_P (svd_strategy_core oracle)

noncomputable def svd_transport_hook
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SVDSimilarityOracle m n) :
    RectStrategyTransportType SVD_P (svd_strategy_core oracle) := by
  intro m n fm dm om nm fn dn on nn A B hrel hPB
  rcases hrel with hBA | hBA
  · subst B
    exact hPB
  · rcases hBA with ⟨t, rfl⟩
    exact svd_transport_twoSidedUnitary t.1.1 t.1.2 A
      (t.1.1ᴴ * A * t.1.2) t.2.1 t.2.2 rfl hPB

noncomputable def svd_lift_hook
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SVDSimilarityOracle m n) :
    RectStrategyLiftType SVD_P (svd_strategy_core oracle) := by
  intro m n fm dm om nm fn dn on nn A hA hTail
  let er := headTailEquiv (α := m)
  let ec := headTailEquiv (α := n)
  let A' := Matrix.reindex er ec A
  rcases hA with ⟨σ, hσ, h11, h12, h21⟩
  have hTailSVD : HasSVD A'.toBlocks₂₂ := by
    simpa [svdHeadTailReduction, SubmatrixMethod, SVDTailRowIdx, SVDTailColIdx, er, ec, A']
      using hTail
  have hA'SVD : HasSVD A' :=
    svd_of_blockReady_reindex A' σ hσ h11 h12 h21 hTailSVD
  have hBack : HasSVD (Matrix.reindex er.symm ec.symm A') :=
    svd_reindex er.symm ec.symm hA'SVD
  simpa [A', er, ec] using hBack

noncomputable def svd_descent_hooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SVDSimilarityOracle m n) :
    SVDDescentHooks oracle where
  proofData :=
    { transport := svd_transport_hook oracle
      lift := svd_lift_hook oracle }

noncomputable def svd_strategy_proof
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SVDSimilarityOracle m n)
    (hooks : SVDDescentHooks oracle) :
    RectStrategyProofData ℂ SVD_P (svd_strategy_core oracle) :=
  hooks.proofData

end MatDecompFormal.Instances
