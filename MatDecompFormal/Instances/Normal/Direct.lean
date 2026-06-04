import MatDecompFormal.Instances.Normal.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Normal Matrix Direct Hooks

This file packages the proof-side mathematical hooks that remain after the
strategy-side unitary-similarity descent has been defined.

The hooks are explicit parameters, not unsupported placeholders. The final unconditional spectral
theorem will be obtained by constructing these hooks from the eigenvector,
unitary-completion, block-diagonalization, and lift lemmas listed in `PLAN.md`.
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

noncomputable def normal_strategy_proof
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι)
    (hooks : NormalDescentHooks oracle) :
    SquareStrategyProofData ℂ NormalSpectral_P (normal_strategy_core oracle) where
  transport := hooks.transport
  lift := hooks.lift

end MatDecompFormal.Instances
