/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Tridiagonalization.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework

/-!
# Tridiagonalization Direct Hooks

This file packages the proof-side hooks for the strict square descent template.
The lift hook is exactly the proof stored in
`TridiagonalizationDescentReady`; concrete Householder/Givens files should
construct the corresponding step oracle.
-/

/-- Transport hook for the tridiagonalization descent: lifts `Tridiagonalization_P` along
unitary similarity steps using `tridiagonalization_transport_unitarySimilarity`. -/
noncomputable def tridiagonalization_transport_hook
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        TridiagonalizationSimilarityOracle ι) :
    SquareStrategyTransportType Tridiagonalization_P
      (tridiagonalization_strategy_core oracle) := by
  intro ι fι dι oι nι A B hrel hPB hHermA
  rcases hrel with hBA | hBA
  · subst B
    exact hPB hHermA
  · rcases hBA with ⟨t, rfl⟩
    exact tridiagonalization_transport_unitarySimilarity
      t.1 A (t.1ᴴ * A * t.1) t.2 rfl
      (hPB (isHermitian_unitarySimilarity hHermA))

/-- Lift hook for the tridiagonalization descent: promotes the tail induction hypothesis to the
full matrix once `TridiagonalizationDescentReady` is satisfied. -/
noncomputable def tridiagonalization_lift_hook
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        TridiagonalizationSimilarityOracle ι) :
    SquareStrategyLiftType Tridiagonalization_P
      (tridiagonalization_strategy_core oracle) := by
  intro ι fι dι oι nι A hReady hTailP
  exact hReady hTailP

/-- Bundles the transport and lift hooks into the `SquareStrategyProofData` record consumed
by the framework's square descent driver. -/
noncomputable def tridiagonalization_strategy_proof
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        TridiagonalizationSimilarityOracle ι) :
    SquareStrategyProofData ℂ Tridiagonalization_P
      (tridiagonalization_strategy_core oracle) where
  transport := tridiagonalization_transport_hook oracle
  lift := tridiagonalization_lift_hook oracle

end MatDecompFormal.Instances
