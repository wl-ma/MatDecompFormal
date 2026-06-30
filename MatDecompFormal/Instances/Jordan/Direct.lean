/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Jordan.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework

/-!
# Jordan Direct Hooks

The proof-side hooks are similarity transport and the oracle-provided lift from
a ready object.
-/

/-- Transport hook for the Jordan descent: lifts `Jordan_P` along similarity steps while
preserving the characteristic-polynomial split hypothesis. -/
noncomputable def jordan_transport_hook
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        JordanStepOracle K ι) :
    SquareStrategyTransportType Jordan_P (jordan_strategy_core K oracle) := by
  intro ι fι dι oι nι A B hrel hPB hsplitA
  rcases hrel with hBA | hBA
  · subst B
    exact hPB hsplitA
  · rcases hBA with ⟨t, rfl⟩
    have hchar :
        (t.1⁻¹ * A * t.1).charpoly = A.charpoly :=
      jordan_similarity_charpoly t.2
    have hsplitB :
        (SquareUniverse.ofMatrix (t.1⁻¹ * A * t.1)).A.charpoly.Splits
          (RingHom.id K) := by
      simpa [hchar] using hsplitA
    exact jordan_transport_similarity t.2 rfl (hPB hsplitB)

/-- Lift hook for the Jordan descent: promotes the tail induction hypothesis once
the oracle-provided descent step is ready. -/
noncomputable def jordan_lift_hook
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        JordanStepOracle K ι) :
    SquareStrategyLiftType Jordan_P (jordan_strategy_core K oracle) := by
  intro ι fι dι oι nι A hReady hTail hsplitA
  exact hReady hsplitA hTail

/-- Bundles the transport and lift hooks into the `SquareStrategyProofData` record consumed
by the framework's square descent driver. -/
noncomputable def jordan_strategy_proof
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        JordanStepOracle K ι) :
    SquareStrategyProofData K Jordan_P (jordan_strategy_core K oracle) where
  transport := jordan_transport_hook K oracle
  lift := jordan_lift_hook K oracle

end MatDecompFormal.Instances
