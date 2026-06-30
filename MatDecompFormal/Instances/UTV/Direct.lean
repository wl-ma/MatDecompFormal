/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
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

/-- Bundles the `RectStrategyProofData` for the UTV descent, holding the transport and lift
hooks together for convenient downstream use. -/
structure UTVDescentHooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n) where
  proofData :
    RectStrategyProofData ℂ UTV_P (utv_strategy_core oracle)

/-- Transport hook for the UTV descent: lifts `UTV_P` along two-sided unitary transformations
using `utv_transport_twoSidedUnitary`. -/
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

/-- Lift hook for the UTV descent: reassembles the UTV decomposition from the ready block and
the tail induction hypothesis, threading through the lexicographic reindexing. -/
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
  let erLex := headTailLexEquiv (α := m)
  let ecLex := headTailLexEquiv (α := n)
  let Aₗ := Matrix.reindex erLex ecLex A
  rcases hA with ⟨σ, hσ, h11, h12, h21⟩
  have hTailUTV : HasUTV A'.toBlocks₂₂ := by
    simpa [utvHeadTailReduction, SubmatrixMethod, UTVTailRowIdx, UTVTailColIdx,
      SVDTailRowIdx, SVDTailColIdx, er, ec, A'] using hTail
  have h11Lex : Aₗ.toBlocks₁₁ = (fun _ _ : Unit => (σ : ℂ)) := by
    simpa [Aₗ, A', erLex, ecLex, er, ec, headTailLexEquiv, Matrix.reindex_apply,
      sumToLexEquiv] using h11
  have h12Lex : Aₗ.toBlocks₁₂ = 0 := by
    simpa [Aₗ, A', erLex, ecLex, er, ec, headTailLexEquiv, Matrix.reindex_apply,
      sumToLexEquiv] using h12
  have h21Lex : Aₗ.toBlocks₂₁ = 0 := by
    simpa [Aₗ, A', erLex, ecLex, er, ec, headTailLexEquiv, Matrix.reindex_apply,
      sumToLexEquiv] using h21
  have hTailLex : HasUTV Aₗ.toBlocks₂₂ := by
    simpa [Aₗ, A', erLex, ecLex, er, ec, headTailLexEquiv, Matrix.reindex_apply,
      sumToLexEquiv] using hTailUTV
  have hAₗUTV : HasUTV Aₗ :=
    utv_of_blockReady_reindex Aₗ σ h11Lex h12Lex h21Lex hTailLex
  have hBack : HasUTV (Matrix.reindex erLex.symm ecLex.symm Aₗ) :=
    utv_reindex_strictMono erLex.symm ecLex.symm
      (strictMono_symm_of_strictMono_equiv erLex headTailLexEquiv_strictMono)
      (strictMono_symm_of_strictMono_equiv ecLex headTailLexEquiv_strictMono)
      hAₗUTV
  simpa [Aₗ, erLex, ecLex] using hBack

/-- Packages the transport and lift hooks into a `UTVDescentHooks` record. -/
noncomputable def utv_descent_hooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n) :
    UTVDescentHooks oracle where
  proofData :=
    { transport := utv_transport_hook oracle
      lift := utv_lift_hook oracle }

/-- Extracts the `RectStrategyProofData` from a `UTVDescentHooks` record. -/
noncomputable def utv_strategy_proof
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n)
    (hooks : UTVDescentHooks oracle) :
    RectStrategyProofData ℂ UTV_P (utv_strategy_core oracle) :=
  hooks.proofData

end MatDecompFormal.Instances
