import Mathlib.LinearAlgebra.Matrix.Block
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Framework.Fin
import MatDecompFormal.Framework.FinEnum

namespace MatDecompFormal.Components.Reductions

open Matrix MatDecompFormal.Framework

/-!
# Zero-Column Reduction Method

`ZeroColumnMethod` handles the degenerate case where the first column already
vanishes. The recursive problem is the lower-right submatrix, and reconstruction
reinstates the zero leading column together with the original top row.
-/

/--
`ZeroColumnMethod` is a `ReductionMethod` instance implementing the reduction strategy
that removes both the first row and the first column when the first column is zero.
-/
noncomputable def ZeroColumnMethod (n m : ℕ) (R : Type*) [CommRing R] :
    Abstractions.ReductionMethod (n + 1) (m + 1) n m R where
  IsSliceable := fun A ↦ ∀ i, A i 0 = 0

  slice := fun A _hA ↦ A.submatrix Fin.succ Fin.succ

  reconstruct := fun A hA slice_sol ↦
    -- Introduce the computational equivalences
    let e_ι := finSuccEquivSum n
    let e_κ := finSuccEquivSum m
    -- Extract the upper-right block A₁₂ from the original matrix
    let A₁₂ := (reindex e_ι e_κ A).toBlocks₁₂
    -- Construct zero blocks
    let zero_block₁₁ : Matrix (Fin 1) (Fin 1) R := 0
    let zero_block₂₁ : Matrix (Fin n) (Fin 1) R := 0
    -- Use fromBlocks to reassemble the zero blocks and the subproblem solution
    let blocks := fromBlocks zero_block₁₁ A₁₂ zero_block₂₁ slice_sol
    -- Reindex back to the original types
    blocks.reindex e_ι.symm e_κ.symm

  reconstruct_slice_eq := by
    intro A hA
    -- Unfold the definitions of reconstruct and slice
    dsimp only
    -- Introduce the computational equivalences
    let e_ι := finSuccEquivSum n
    let e_κ := finSuccEquivSum m
    let A' := reindex e_ι e_κ A
    -- Key step: use submatrix_succ_eq_toBlocks₂₂ to relate slice to toBlocks₂₂
    change (reindex (finSuccEquivSum n).symm (finSuccEquivSum m).symm)
      (fromBlocks 0 A'.toBlocks₁₂ 0 (A.submatrix Fin.succ Fin.succ)) = A
    have h_slice_eq_A₂₂ : A.submatrix Fin.succ Fin.succ = A'.toBlocks₂₂ := by
      rw [submatrix_succ_eq_toBlocks₂₂ A, ← submatrix_succ_eq_toBlocks₂₂ A]
    rw [h_slice_eq_A₂₂]
    -- Prove that the left blocks A₁₁ and A₂₁ of A' are both zero
    have h_zero_blocks : A'.toBlocks₁₁ = 0 ∧ A'.toBlocks₂₁ = 0 := by
      constructor
      · ext i j; simp [A', finSuccEquivSum, toBlocks₁₁, e_ι, e_κ, hA]
      · ext i j; simp [A', finSuccEquivSum, toBlocks₂₁, e_ι, e_κ, hA]
    -- Substitute the zero blocks
    rw [← h_zero_blocks.1, ← h_zero_blocks.2]
    -- Prove that the reconstructed block matrix equals the original block matrix
    have h_reconstructed_eq_A' :
        fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁ A'.toBlocks₂₂ = A' :=
      fromBlocks_toBlocks A'
    rw [h_reconstructed_eq_A']
    -- Prove that reindexing and then reindexing by reindex.symm gives the original matrix
    simp [A', e_ι, e_κ]


end MatDecompFormal.Components.Reductions
