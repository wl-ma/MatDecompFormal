/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Hessenberg.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework

/-!
# Hessenberg Direct Hooks

This file packages the proof-side hooks for the Hessenberg descent template.
The similarity transport is proved concretely. The lift hook is exactly the
proof stored in `HessenbergDescentReady`.
-/

/-- Transport hook for the Hessenberg descent: lifts `Hessenberg_P` along
similarity steps using `hessenberg_transport_similarity`. -/
noncomputable def hessenberg_transport_hook
    {R : Type u} [Semiring R]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        HessenbergSimilarityOracle R ι) :
    SquareStrategyTransportType Hessenberg_P (hessenberg_strategy_core oracle) := by
  intro ι fι dι oι nι A B hrel hPB
  rcases hrel with hBA | hBA
  · subst B
    exact hPB
  · rcases hBA with ⟨t, rfl⟩
    exact hessenberg_transport_similarity t.1.1 t.1.2 A
      (t.1.2 * A * t.1.1) t.2 rfl hPB

/-- Lift hook for the Hessenberg descent: promotes the tail induction hypothesis once
`HessenbergDescentReady` is satisfied. -/
noncomputable def hessenberg_lift_hook
    {R : Type u} [Semiring R]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        HessenbergSimilarityOracle R ι) :
    SquareStrategyLiftType Hessenberg_P (hessenberg_strategy_core oracle) := by
  intro ι fι dι oι nι A hReady hTail
  exact hReady hTail

/-- Bundles the transport and lift hooks into the `SquareStrategyProofData` record consumed
by the framework's square descent driver. -/
noncomputable def hessenberg_strategy_proof
    {R : Type u} [Semiring R]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        HessenbergSimilarityOracle R ι) :
    SquareStrategyProofData R Hessenberg_P (hessenberg_strategy_core oracle) where
  transport := hessenberg_transport_hook oracle
  lift := hessenberg_lift_hook oracle

end MatDecompFormal.Instances
