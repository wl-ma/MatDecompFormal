import MatDecompFormal.Instances.Bidiagonalization.Strategy
import MatDecompFormal.Framework.Reindex

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Bidiagonalization Direct Hooks

This file packages the target-specific proof hooks needed by the rectangular
descent template for oracle-routed unitary bidiagonalization.
-/

variable {𝕜 : Type v} [RCLike 𝕜]

/-- Proof hooks needed to turn the bidiagonalization strategy core into framework data. -/
structure BidiagonalizationDescentHooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationStepOracle 𝕜 m n) where
  proofData :
    RectStrategyProofData 𝕜 (Bidiagonalization_P 𝕜)
      (bidiagonalization_strategy_core 𝕜 oracle)

noncomputable def bidiagonalization_transport_hook
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationStepOracle 𝕜 m n) :
    RectStrategyTransportType (Bidiagonalization_P 𝕜)
      (bidiagonalization_strategy_core 𝕜 oracle) := by
  intro m n fm dm om nm fn dn on nn A B hrel hPB
  rcases hrel with hBA | hBA
  · subst B
    exact hPB
  · rcases hBA with ⟨t, rfl⟩
    exact bidiagonalization_transport_equivalence t.1.1 t.1.2 A
      (t.1.1ᴴ * A * t.1.2) t.2.1 t.2.2 rfl hPB

noncomputable def bidiagonalization_lift_hook
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationStepOracle 𝕜 m n) :
    RectStrategyLiftType (Bidiagonalization_P 𝕜)
      (bidiagonalization_strategy_core 𝕜 oracle) := by
  intro m n fm dm om nm fn dn on nn A hA hTail
  let er := headTailLexEquiv (α := m)
  let ec := headTailLexEquiv (α := n)
  let Ablk : Matrix (Unit ⊕ₗ BidiagonalRowTail m) (Unit ⊕ₗ BidiagonalColTail n) 𝕜 :=
    Matrix.reindex er ec A
  have hTailBi : HasUnitaryBidiagonalization Ablk.toBlocks₂₂ := by
    simpa [bidiagonalizationHeadTailReduction, SubmatrixMethod,
      BidiagonalRowTail, BidiagonalColTail, er, ec, Ablk] using hTail
  have hLift :
      HasUnitaryBidiagonalization
        (Matrix.reindex
          (sumToLexEquiv Unit (BidiagonalRowTail m))
          (sumToLexEquiv Unit (BidiagonalColTail n))
          (fromBlocks Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ Ablk.toBlocks₂₁ Ablk.toBlocks₂₂ :
            Matrix (Unit ⊕ BidiagonalRowTail m) (Unit ⊕ BidiagonalColTail n) 𝕜)) := by
    exact bidiagonalization_of_ready_blocks
      Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ Ablk.toBlocks₂₁ Ablk.toBlocks₂₂
      hA.1 hA.2 hTailBi
  have hBlkBi : HasUnitaryBidiagonalization Ablk := by
    simpa [Ablk, reindex_sumToLex_fromBlocks, fromBlocks_toBlocks] using hLift
  have hOrig :
      HasUnitaryBidiagonalization (Matrix.reindex er.symm ec.symm Ablk) :=
    bidiagonalization_reindex_strictMono er.symm ec.symm
      (by
        intro a b hab
        have hxy' : er (er.symm a) < er (er.symm b) := by
          simpa using hab
        exact (headTailLexEquiv_strictMono (α := m)).lt_iff_lt.mp hxy')
      (by
        intro a b hab
        have hxy' : ec (ec.symm a) < ec (ec.symm b) := by
          simpa using hab
        exact (headTailLexEquiv_strictMono (α := n)).lt_iff_lt.mp hxy')
      hBlkBi
  simpa [Ablk, er, ec, reindex_reindex] using hOrig

noncomputable def bidiagonalization_descent_hooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationStepOracle 𝕜 m n) :
    BidiagonalizationDescentHooks oracle where
  proofData :=
    { transport := bidiagonalization_transport_hook oracle
      lift := bidiagonalization_lift_hook oracle }

noncomputable def bidiagonalization_strategy_proof
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationStepOracle 𝕜 m n)
    (hooks : BidiagonalizationDescentHooks oracle) :
    RectStrategyProofData 𝕜 (Bidiagonalization_P 𝕜)
      (bidiagonalization_strategy_core 𝕜 oracle) :=
  hooks.proofData

/-! ## Boundary-aware fixed-right-head hooks -/

structure BidiagonalizationBoundaryDescentHooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationBoundaryStepOracle 𝕜 m n) where
  proofData :
    RectStrategyProofData 𝕜 (BidiagonalizationFixedRightHead_P 𝕜)
      (bidiagonalization_boundary_strategy_core 𝕜 oracle)

noncomputable def bidiagonalization_boundary_transport_hook
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationBoundaryStepOracle 𝕜 m n) :
    RectStrategyTransportType (BidiagonalizationFixedRightHead_P 𝕜)
      (bidiagonalization_boundary_strategy_core 𝕜 oracle) := by
  intro m n fm dm om nm fn dn on nn A B hrel hPB
  rcases hrel with hBA | hBA
  · subst B
    exact hPB
  · rcases hBA with ⟨t, rfl⟩
    rcases hPB with ⟨_hn, hfixed⟩ | hEmpty
    · exact Or.inl ⟨nn,
        bidiagonalization_transport_equivalence_fixedRightHead
          t.1.1 t.1.2 A (t.1.1ᴴ * A * t.1.2)
          t.2.1 t.2.2.1 t.2.2.2 rfl hfixed⟩
    · exact Or.inr hEmpty

noncomputable def bidiagonalization_boundary_lift_hook
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationBoundaryStepOracle 𝕜 m n) :
    RectStrategyLiftType (BidiagonalizationFixedRightHead_P 𝕜)
      (bidiagonalization_boundary_strategy_core 𝕜 oracle) := by
  intro m n fm dm om nm fn dn on nn A hA hTail
  let er := headTailLexEquiv (α := m)
  let ec := headTailLexEquiv (α := n)
  let Ablk : Matrix (Unit ⊕ₗ BidiagonalRowTail m) (Unit ⊕ₗ BidiagonalColTail n) 𝕜 :=
    Matrix.reindex er ec A
  have hLift :
      HasUnitaryBidiagonalizationFixedRightHead
        (Matrix.reindex
          (sumToLexEquiv Unit (BidiagonalRowTail m))
          (sumToLexEquiv Unit (BidiagonalColTail n))
          (fromBlocks Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ Ablk.toBlocks₂₁ Ablk.toBlocks₂₂ :
            Matrix (Unit ⊕ BidiagonalRowTail m) (Unit ⊕ BidiagonalColTail n) 𝕜)) := by
    by_cases hnTail : Nonempty (BidiagonalColTail n)
    · letI : Nonempty (BidiagonalColTail n) := hnTail
      have hTailFixed : HasUnitaryBidiagonalizationFixedRightHead Ablk.toBlocks₂₂ := by
        have hTail' :
            BidiagonalizationFixedRightHead_P 𝕜
              (RectUniverse.ofMatrix Ablk.toBlocks₂₂) := by
          simpa [bidiagonalizationBoundaryHeadTailReduction, SubmatrixMethod,
            BidiagonalRowTail, BidiagonalColTail, er, ec, Ablk] using hTail
        rcases hTail' with ⟨_hn, hfixed⟩ | hEmpty
        · exact hfixed
        · exact False.elim (not_nonempty_iff.mpr hEmpty hnTail)
      exact bidiagonalization_of_boundary_ready_blocks
        Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ Ablk.toBlocks₂₁ Ablk.toBlocks₂₂
        hA.1 hA.2 hTailFixed
    · have hEmpty : IsEmpty (BidiagonalColTail n) := not_nonempty_iff.mp hnTail
      letI : IsEmpty (BidiagonalColTail n) := hEmpty
      exact bidiagonalization_fixedRightHead_of_boundary_ready_blocks_empty_tail_cols
        Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ Ablk.toBlocks₂₁ Ablk.toBlocks₂₂ hA.1
  have hBlkFixed : HasUnitaryBidiagonalizationFixedRightHead Ablk := by
    simpa [Ablk, reindex_sumToLex_fromBlocks, fromBlocks_toBlocks] using hLift
  have hOrig :
      HasUnitaryBidiagonalizationFixedRightHead (Matrix.reindex er.symm ec.symm Ablk) :=
    bidiagonalizationFixedRightHead_reindex_strictMono er.symm ec.symm
      (by
        intro a b hab
        have hxy' : er (er.symm a) < er (er.symm b) := by
          simpa using hab
        exact (headTailLexEquiv_strictMono (α := m)).lt_iff_lt.mp hxy')
      (by
        intro a b hab
        have hxy' : ec (ec.symm a) < ec (ec.symm b) := by
          simpa using hab
        exact (headTailLexEquiv_strictMono (α := n)).lt_iff_lt.mp hxy')
      hBlkFixed
  exact Or.inl ⟨nn, by simpa [Ablk, er, ec, reindex_reindex] using hOrig⟩

noncomputable def bidiagonalization_boundary_descent_hooks
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationBoundaryStepOracle 𝕜 m n) :
    BidiagonalizationBoundaryDescentHooks oracle where
  proofData :=
    { transport := bidiagonalization_boundary_transport_hook oracle
      lift := bidiagonalization_boundary_lift_hook oracle }

noncomputable def bidiagonalization_boundary_strategy_proof
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationBoundaryStepOracle 𝕜 m n)
    (hooks : BidiagonalizationBoundaryDescentHooks oracle) :
    RectStrategyProofData 𝕜 (BidiagonalizationFixedRightHead_P 𝕜)
      (bidiagonalization_boundary_strategy_core 𝕜 oracle) :=
  hooks.proofData

end MatDecompFormal.Instances
