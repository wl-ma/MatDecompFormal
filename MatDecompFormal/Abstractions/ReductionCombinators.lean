import MatDecompFormal.Abstractions.ReductionMethod

namespace MatDecompFormal.Abstractions

/-!
# 规约方法组合子 (Reduction Method Combinators)
-/

/--
`ReductionMethod.try_else` (Fin m n 版)
-/
noncomputable def ReductionMethod.try_else {m n slice_m slice_n : ℕ} {R : Type*} [CommRing R]
    (M₁ M₂ : ReductionMethod m n slice_m slice_n R)
    : ReductionMethod m n slice_m slice_n R where

  IsSliceable := fun A ↦ M₁.IsSliceable A ∨ M₂.IsSliceable A

  slice := by
    intro A hA
    by_cases h₁ : M₁.IsSliceable A
    · exact M₁.slice A h₁
    · let h₂ : M₂.IsSliceable A := hA.resolve_left h₁
      -- 使用前提来统一类型
      exact M₂.slice A h₂

  reconstruct := by
    intro A hA slice_sol
    by_cases h₁ : M₁.IsSliceable A
    · exact M₁.reconstruct A h₁ slice_sol
    · let h₂ : M₂.IsSliceable A := hA.resolve_left h₁
      exact M₂.reconstruct A h₂ slice_sol

  reconstruct_slice_eq := by
    intro A hA
    dsimp only
    split_ifs with h₁
    · exact M₁.reconstruct_slice_eq A h₁
    · exact M₂.reconstruct_slice_eq A (hA.resolve_left h₁)

end MatDecompFormal.Abstractions
