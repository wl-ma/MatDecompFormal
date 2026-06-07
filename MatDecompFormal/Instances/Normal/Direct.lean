import MatDecompFormal.Instances.Normal.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Normal Matrix Direct Hooks

This file packages the proof-side mathematical hooks that remain after the
strategy-side unitary-similarity descent has been defined.

The hooks are explicit parameters, not unsupported placeholders. The final
unconditional spectral theorem is obtained by constructing these hooks from the
eigenvector, unitary-completion, block-diagonalization, and lift lemmas in the
normal instance files.
-/

/--
Proof hooks needed to turn the normal strategy core into a
`SquareStrategyProofData` instance.
-/
structure NormalDescentHooks
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι) where
  transport :
    SquareStrategyTransportType NormalSpectral_P (normal_strategy_core oracle)
  lift :
    SquareStrategyLiftType NormalSpectral_P (normal_strategy_core oracle)

noncomputable def normal_transport_hook
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι) :
    SquareStrategyTransportType NormalSpectral_P (normal_strategy_core oracle) := by
  intro ι fι dι oι nι A B hrel hPB hNormalA
  rcases hrel with hBA | hBA
  · subst B
    exact hPB hNormalA
  · rcases hBA with ⟨t, rfl⟩
    exact normalSpectral_transport_unitarySimilarity t.1 A (t.1ᴴ * A * t.1) t.2 rfl
      (hPB (isNormalMatrix_unitarySimilarity t.2 hNormalA))

noncomputable def normal_lift_hook
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι) :
    SquareStrategyLiftType NormalSpectral_P (normal_strategy_core oracle) := by
  intro ι fι dι oι nι A hA hTailP hNormalA
  let e := headTailEquiv (α := ι)
  let A' := Matrix.reindex e e A
  have hReady : NormalBlockReady ι A := by
    cases hA with
    | inl hNotNormal => exact False.elim (hNotNormal hNormalA)
    | inr hReady => exact hReady
  rcases hReady with ⟨h12, h21⟩
  have hTailNormal : IsNormalMatrix A'.toBlocks₂₂ := by
    exact isNormalMatrix_tail_of_zero_offdiag A' (isNormalMatrix_reindex e hNormalA) h12 h21
  have hTailSpec : HasNormalSpectral A'.toBlocks₂₂ := by
    simpa [A', normalHeadTailReduction, SubmatrixMethod, NormalTailIdx, e] using hTailP hTailNormal
  have hA'Spec : HasNormalSpectral A' :=
    normalSpectral_of_blockReady_reindex A' h12 h21 hTailSpec
  have hBack : HasNormalSpectral (Matrix.reindex e.symm e.symm A') :=
    normalSpectral_reindex e.symm hA'Spec
  simpa [A', e] using hBack

noncomputable def normal_descent_hooks
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι) :
    NormalDescentHooks oracle where
  transport := normal_transport_hook oracle
  lift := normal_lift_hook oracle

noncomputable def normal_strategy_proof
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι)
    (hooks : NormalDescentHooks oracle) :
    SquareStrategyProofData ℂ NormalSpectral_P (normal_strategy_core oracle) where
  transport := hooks.transport
  lift := hooks.lift

end MatDecompFormal.Instances
