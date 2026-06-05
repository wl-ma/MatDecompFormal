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

noncomputable def rationalCanonical_lift_hook
    {K : Type v} [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        RationalCanonicalStepOracle K ι) :
    SquareStrategyLiftType
      RationalCanonical_P (rationalCanonical_strategy_core K oracle) := by
  intro ι fι dι oι nι A hReady hTail
  exact hReady hTail

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
