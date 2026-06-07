import MatDecompFormal.Abstractions.ReductionMethod

namespace MatDecompFormal.Abstractions

/-!
# Reduction Method Combinators
-/

/--
`ReductionMethod.try_else`
-/
noncomputable def ReductionMethod.try_else {ι κ ιs κs : Type*} {R : Type*}
    (M₁ M₂ : ReductionMethod ι κ ιs κs R) :
    ReductionMethod ι κ ιs κs R where

  IsSliceable := fun A ↦ M₁.IsSliceable A ∨ M₂.IsSliceable A

  slice := by
    intro A hA
    by_cases h₁ : M₁.IsSliceable A
    · exact M₁.slice A h₁
    · let h₂ : M₂.IsSliceable A := hA.resolve_left h₁
      -- Use the assumption to unify the types
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
