/-
Copyright (c) 2026 Wanli Ma, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanli Ma, Zichen Wang
-/
import Mathlib.LinearAlgebra.Matrix.Block
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Framework.Reindex

namespace MatDecompFormal.Components.Reductions

open Matrix MatDecompFormal.Framework

/-!
# Zero-Column Reduction Method

`ZeroColumnMethod` handles the degenerate case where the first column already
vanishes. The recursive problem is the lower-right submatrix, and reconstruction
reinstates the zero leading column together with the original top row.
-/

/--
`ZeroColumnMethod` is a `ReductionMethod` instance implementing the reduction
strategy that removes the tail rows and tail columns once the distinguished head
column is zero.
-/
noncomputable def ZeroColumnMethod
    {ι κ ι₁ ι₂ κ₁ κ₂ R : Type*} [Zero R] [Unique κ₁]
    (er : ι ≃ ι₁ ⊕ ι₂) (ec : κ ≃ κ₁ ⊕ κ₂) :
    Abstractions.ReductionMethod ι κ ι₂ κ₂ R where
  IsSliceable := fun A ↦ ∀ i, A i (ec.symm (Sum.inl default)) = 0

  slice := fun A _hA ↦ A.submatrix (fun i => er.symm (Sum.inr i)) (fun j => ec.symm (Sum.inr j))

  reconstruct := fun A hA slice_sol ↦
    -- Extract the upper-right block A₁₂ from the original matrix
    let A₁₂ := (Matrix.reindex er ec A).toBlocks₁₂
    -- Construct zero blocks
    let zero_block₁₁ : Matrix ι₁ κ₁ R := 0
    let zero_block₂₁ : Matrix ι₂ κ₁ R := 0
    -- Use fromBlocks to reassemble the zero blocks and the subproblem solution
    let blocks := fromBlocks zero_block₁₁ A₁₂ zero_block₂₁ slice_sol
    -- Reindex back to the original types
    blocks.reindex er.symm ec.symm

  reconstruct_slice_eq := by
    intro A hA
    -- Unfold the definitions of reconstruct and slice
    dsimp only
    let A' := Matrix.reindex er ec A
    change (reindex er.symm ec.symm)
      (fromBlocks 0 A'.toBlocks₁₂ 0
        (A.submatrix (fun i => er.symm (Sum.inr i)) (fun j => ec.symm (Sum.inr j)))) = A
    have h_slice_eq_A₂₂ :
        A.submatrix (fun i => er.symm (Sum.inr i)) (fun j => ec.symm (Sum.inr j)) = A'.toBlocks₂₂ := by
      simpa [A'] using
        submatrix_inr_inr_eq_toBlocks₂₂ er ec A
    rw [h_slice_eq_A₂₂]
    -- Prove that the left blocks A₁₁ and A₂₁ of A' are both zero
    have h_zero_blocks : A'.toBlocks₁₁ = 0 ∧ A'.toBlocks₂₁ = 0 := by
      constructor
      · ext i j
        have h_entry := hA (er.symm (Sum.inl i))
        simpa [A', Matrix.toBlocks₁₁, Matrix.reindex_apply, Subsingleton.elim j default] using h_entry
      · ext i j
        have h_entry := hA (er.symm (Sum.inr i))
        simpa [A', Matrix.toBlocks₂₁, Matrix.reindex_apply, Subsingleton.elim j default] using h_entry
    -- Substitute the zero blocks
    rw [← h_zero_blocks.1, ← h_zero_blocks.2]
    -- Prove that the reconstructed block matrix equals the original block matrix
    have h_reconstructed_eq_A' :
        fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁ A'.toBlocks₂₂ = A' :=
      fromBlocks_toBlocks A'
    rw [h_reconstructed_eq_A']
    -- Prove that reindexing and then reindexing by reindex.symm gives the original matrix
    simp [A']


end MatDecompFormal.Components.Reductions
