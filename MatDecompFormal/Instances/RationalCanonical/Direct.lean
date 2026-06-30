/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.RationalCanonical.Strategy

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework

/-!
# Rational Canonical Form Direct Hooks

The proof-side hooks are exactly the similarity transport lemma and the
oracle-provided lift from a ready object.
-/

/-- Transport hook for the rational canonical form descent: lifts `RationalCanonical_P` along
similarity steps using `rationalCanonical_transport_similarity`. -/
noncomputable def rationalCanonical_transport_hook
    {K : Type v} [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        RationalCanonicalStepOracle K ι) :
    SquareStrategyTransportType
      RationalCanonical_P (rationalCanonical_strategy_core K oracle) := by
  intro ι fι dι oι nι A B hrel hPB
  rcases hrel with hBA | hBA
  · subst B
    exact hPB
  · rcases hBA with ⟨t, rfl⟩
    exact rationalCanonical_transport_similarity
      t.1.1 t.1.2 A (t.1.2 * A * t.1.1) t.2 rfl hPB

/-- Lift hook for the rational canonical form descent: promotes the tail induction hypothesis
once the oracle-provided descent step is ready. -/
noncomputable def rationalCanonical_lift_hook
    {K : Type v} [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        RationalCanonicalStepOracle K ι) :
    SquareStrategyLiftType
      RationalCanonical_P (rationalCanonical_strategy_core K oracle) := by
  intro ι fι dι oι nι A hReady hTail
  exact hReady hTail

/-- Bundles the transport and lift hooks into the `SquareStrategyProofData` record consumed
by the framework's square descent driver. -/
noncomputable def rationalCanonical_strategy_proof
    {K : Type v} [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        RationalCanonicalStepOracle K ι) :
    SquareStrategyProofData K
      RationalCanonical_P (rationalCanonical_strategy_core K oracle) where
  transport := rationalCanonical_transport_hook oracle
  lift := rationalCanonical_lift_hook oracle

end MatDecompFormal.Instances
