import Mathlib.LinearAlgebra.Matrix.Block
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Framework.Reindex

namespace MatDecompFormal.Components.Reductions

open Matrix MatDecompFormal.Framework

/-!
# Submatrix-Based Reduction Method

`SubmatrixMethod` packages the standard lower-right block reduction determined
by chosen row and column splits. The recursive slice is the bottom-right block,
and reconstruction restores the original boundary blocks around the recursive
solution.
-/

/--
`SubmatrixMethod` is a `ReductionMethod` instance implementing the reduction
strategy that directly handles the lower-right block selected by the supplied
row and column splits.

*   `IsSliceable_def`: a user-provided predicate defining when slicing is allowed.
-/
noncomputable def SubmatrixMethod
    {ι κ ι₁ ι₂ κ₁ κ₂ R : Type*}
    (er : ι ≃ ι₁ ⊕ ι₂) (ec : κ ≃ κ₁ ⊕ κ₂)
    (IsSliceable_def : Matrix ι κ R → Prop) :
    Abstractions.ReductionMethod ι κ ι₂ κ₂ R where
  IsSliceable := IsSliceable_def

  slice := fun A _hA ↦ A.submatrix (fun i => er.symm (Sum.inr i)) (fun j => ec.symm (Sum.inr j))

  reconstruct := fun A _hA slice_sol ↦
    -- Move the original matrix to the block world to extract the corner data
    let A' := Matrix.reindex er ec A
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    -- Use fromBlocks to reassemble the corner data and the subproblem solution
    let blocks := fromBlocks A₁₁ A₁₂ A₂₁ slice_sol
    -- Reindex back to the original types
    blocks.reindex er.symm ec.symm

  reconstruct_slice_eq := by
    intro A hA
    dsimp only
    let A' := Matrix.reindex er ec A
    have h_slice_eq_A₂₂ :
        A.submatrix
            (fun i => er.symm (Sum.inr i))
            (fun j => ec.symm (Sum.inr j)) =
          A'.toBlocks₂₂ := by
      simpa [A'] using submatrix_inr_inr_eq_toBlocks₂₂ er ec A
    rw [h_slice_eq_A₂₂]
    have h_reconstructed_eq_A' :
        fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁ A'.toBlocks₂₂ = A' :=
      fromBlocks_toBlocks A'
    rw [h_reconstructed_eq_A']
    ext i j
    simp [A']


end MatDecompFormal.Components.Reductions
