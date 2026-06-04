import MatDecompFormal.Instances.Normal.Direct

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Normal Matrix Spectral Decomposition: Framework Entry

This file assembles the normal-matrix descent strategy through the same bridge
used by the other decompositions:

```lean
SquareStrategyData
mkSquareSubtypeInductionInstanceFromStrategy
SquareSubtypeInductionInstance.prove_for_matrix
```

At this stage the theorem is conditional on `NormalSimilarityOracle` and
`NormalDescentHooks`. These are the concrete remaining obligations from the
plan, not hidden unsupported placeholders.
-/

/-- Universe-level base case for the normal spectral target. -/
theorem normalSpectral_base_univ (x : SquareUniverse ℂ) :
    ((∀ (x_sub : PosSquareUniverse ℂ), (x_sub : SquareUniverse ℂ) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      NormalSpectral_P x := by
  intro hx _hNormal
  have hzero : Fintype.card x.ι = 0 := by
    have hxcard : Fintype.card x.ι ≤ 0 := by
      rcases hx with hnot | hle
      · by_contra hnotzero
        have hposCard : 0 < Fintype.card x.ι :=
          Nat.pos_of_ne_zero (fun hz => hnotzero (hz.le))
        let x_sub : PosSquareUniverse ℂ := ⟨x, hposCard⟩
        exact hnot x_sub rfl
      · simpa [squareSubtypeμ, squareSubtypeμBase] using hle
    exact Nat.le_zero.mp hxcard
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  letI : Subsingleton x.ι := by infer_instance
  exact base_normalSpectral_subsingleton x.A

noncomputable def normal_strategy_data
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι)
    (hooks : NormalDescentHooks oracle) :
    SquareStrategyData ℂ NormalSpectral_P :=
  mkSquareStrategyData
    (normal_strategy_core oracle)
    (normal_strategy_proof oracle hooks)

noncomputable def normal_framework_inst
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι)
    (hooks : NormalDescentHooks oracle) :
    SquareSubtypeInductionInstance ℂ :=
  mkSquareSubtypeInductionInstanceFromStrategy
    NormalSpectral_P
    normalSpectral_base_univ
    (normal_strategy_data oracle hooks)

/--
Conditional framework-routed normal spectral decomposition theorem.

The proof route is already the intended descent route. The remaining work is to
construct the `oracle` and `hooks` parameters from the concrete spectral
mathematics.
-/
theorem exists_normal_spectral_decomposition_framework
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        NormalSimilarityOracle κ)
    (hooks : NormalDescentHooks oracle)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  have hP :
      (normal_framework_inst oracle hooks).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := normal_framework_inst oracle hooks) A
  exact hP hA

end MatDecompFormal.Instances
