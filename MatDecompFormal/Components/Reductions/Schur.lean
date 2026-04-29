import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Framework.Fin
import MatDecompFormal.Framework.FinEnum

namespace MatDecompFormal.Components.Reductions

open Matrix MatDecompFormal.Framework

/-!
# Schur-Complement-Based Reduction Method

`SchurMethod` implements the square-matrix reduction that cuts off the leading
row and column by taking the Schur complement of the top-left scalar block.
Reconstruction restores the original matrix by adding back the correction term.
-/

/--
`SchurMethod` is a `ReductionMethod` instance implementing a Schur-complement-based
reduction strategy for **square matrices**. It is defined on square matrices indexed
by `Fin (n+1)`.
-/
noncomputable def SchurMethod (n : ℕ) (R : Type*) [Field R] :
    Abstractions.ReductionMethod (n + 1) (n + 1) n n R where
  IsSliceable := fun A ↦ IsUnit (A 0 0)

  slice := fun A hA ↦
    -- Reindex using the new computational equivalence
    let A' := reindex (finSuccEquivSum n) (finSuccEquivSum n) A
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    let A₂₂ := A'.toBlocks₂₂
    -- The inverse of A 0 0 is the scalar (A 0 0)⁻¹
    let inv_A₀₀ : R := (IsUnit.unit hA).inv
    -- Compute the Schur complement manually
    A₂₂ - A₂₁ * (!![inv_A₀₀]) * A₁₂

  reconstruct := fun A hA slice_sol ↦
    -- Use the computational equivalence here as well
    let e := finSuccEquivSum n
    let A' := reindex e e A
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    let inv_A₀₀ : R := (IsUnit.unit hA).inv
    -- Reconstruct the A₂₂ block from the subproblem solution
    let A₂₂_reconstructed := slice_sol + A₂₁ * (!![inv_A₀₀]) * A₁₂
    -- Reassemble using fromBlocks
    let blocks := fromBlocks A₁₁ A₁₂ A₂₁ A₂₂_reconstructed
    -- Reindex back to the original types
    blocks.reindex e.symm e.symm

  reconstruct_slice_eq := by
    intro A hA
    -- Unfold the definitions of reconstruct and slice
    dsimp only
    -- Introduce the computational equivalences
    let e := finSuccEquivSum n
    let A' := reindex e e A
    -- Extract the blocks
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    let A₂₂ := A'.toBlocks₂₂
    -- Construct the reconstructed matrix
    let reconstructed_blocks :=
      fromBlocks A₁₁ A₁₂ A₂₁ (A₂₂ - A₂₁ * (!![(IsUnit.unit hA).inv]) * A₁₂ +
          A₂₁ * (!![(IsUnit.unit hA).inv]) * A₁₂)
    -- Prove that the reconstructed block matrix equals the original block matrix
    have h_reconstructed_eq_A' : reconstructed_blocks = A' := by
      simp [reconstructed_blocks, sub_add_cancel]
      rw [fromBlocks_toBlocks]
    -- Apply the equality to the reindexed result
    change (reindex (finSuccEquivSum n).symm (finSuccEquivSum n).symm) reconstructed_blocks = A
    rw [h_reconstructed_eq_A']
    -- Prove that reindexing and then reindexing by reindex.symm gives the original matrix
    simp [A', e]


end MatDecompFormal.Components.Reductions
