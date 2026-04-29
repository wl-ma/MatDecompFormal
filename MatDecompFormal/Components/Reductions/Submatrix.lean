import Mathlib.LinearAlgebra.Matrix.Block
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Framework.Fin
import MatDecompFormal.Framework.FinEnum

namespace MatDecompFormal.Components.Reductions

open Matrix MatDecompFormal.Framework

/-!
# Submatrix-Based Reduction Method

`SubmatrixMethod` packages the standard lower-right submatrix reduction on
`Fin (n + 1) × Fin (m + 1)` matrices. The recursive slice is obtained by
dropping the first row and column, and reconstruction restores the original
boundary blocks around the recursive solution.
-/

/--
`SubmatrixMethod` is a `ReductionMethod` instance implementing the reduction strategy
that directly handles the lower-right submatrix. It is defined on matrices indexed by
`Fin (n+1)` and `Fin (m+1)`.

*   `IsSliceable_def`: a user-provided predicate defining when slicing is allowed.
-/
noncomputable def SubmatrixMethod (n m : ℕ) (R : Type*) [CommRing R]
    (IsSliceable_def : Matrix (Fin (n + 1)) (Fin (m + 1)) R → Prop) :
    Abstractions.ReductionMethod (n + 1) (m + 1) n m R where
  IsSliceable := IsSliceable_def

  slice := fun A _hA ↦ A.submatrix Fin.succ Fin.succ

  reconstruct := fun A _hA slice_sol ↦
    -- Introduce the computational equivalences
    let e_ι := finSuccEquivSum n
    let e_κ := finSuccEquivSum m
    -- Move the original matrix to the block world to extract the corner data
    let A' := reindex e_ι e_κ A
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    -- Use fromBlocks to reassemble the corner data and the subproblem solution
    let blocks := fromBlocks A₁₁ A₁₂ A₂₁ slice_sol
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
    have h_slice_eq_A₂₂ : A.submatrix Fin.succ Fin.succ = A'.toBlocks₂₂ := by
      rw [submatrix_succ_eq_toBlocks₂₂ A, ← submatrix_succ_eq_toBlocks₂₂ A]
    rw [h_slice_eq_A₂₂]
    -- Prove that the reconstructed block matrix equals the original block matrix
    have h_reconstructed_eq_A' :
        fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁ A'.toBlocks₂₂ = A' :=
      fromBlocks_toBlocks A'
    rw [h_reconstructed_eq_A']
    -- Prove that reindexing and then reindexing by reindex.symm gives the original matrix
    simp [A', e_ι, e_κ]


end MatDecompFormal.Components.Reductions
