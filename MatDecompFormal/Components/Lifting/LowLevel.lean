/-
Copyright (c) 2026 Wanli Ma, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanli Ma, Zichen Wang
-/
import Mathlib.Data.Sum.Order
import Mathlib.LinearAlgebra.Matrix.Block
import MatDecompFormal.Components.BlockAlgebra

namespace MatDecompFormal.Components

open Matrix

/-!
# Lifting Low-Level Tools

This file contains equation-level transport and assembly lemmas shared by
higher-level lifting constructions.
-/

section LowLevel

variable {R : Type*} [Semiring R]

/-- Transport a reindexed equality back to the original index type. -/
lemma schur_case_transport_back
    {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (A : Matrix ι ι R)
    (e : ι ≃ σ)
    (P_blk L_blk U_blk : Matrix σ σ R)
    (h_blk : P_blk * (Matrix.reindex e e A) = L_blk * U_blk) :
    (Matrix.reindex e.symm e.symm P_blk) * A =
      (Matrix.reindex e.symm e.symm L_blk) * (Matrix.reindex e.symm e.symm U_blk) := by
  let P : Matrix ι ι R := Matrix.reindex e.symm e.symm P_blk
  let U : Matrix ι ι R := Matrix.reindex e.symm e.symm U_blk
  let L : Matrix ι ι R := Matrix.reindex e.symm e.symm L_blk

  have h_back := congrArg (Matrix.reindex e.symm e.symm) h_blk
  dsimp [P, L, U]
  rw [← submatrix_mul]
  · simp only [reindex_apply, Equiv.symm_symm] at h_back
    rw [← h_back]
    classical
    let Aℓ : Matrix σ σ R := Matrix.reindex e e A
    have hA : A = Aℓ.submatrix (⇑e) (⇑e) := by
      ext i j
      simp [Aℓ, Matrix.reindex_apply, Matrix.submatrix]
    simp [hA]
  · apply e.bijective

/--
Two-factor lifting core for the common pattern where the lower-left block
vanishes and the lower-right block comes from a recursive two-factor
decomposition.
-/
lemma lift_two_factor_from_zero_block21
    {ι ι₁ ι₂ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    (A : Matrix ι ι R)
    (e : ι ≃ ι₁ ⊕ₗ ι₂)
    (subF₁ subF₂ : Matrix ι₂ ι₂ R)
    (hA21 : (Matrix.reindex e e A).toBlocks₂₁ = 0)
    (hA22 : (Matrix.reindex e e A).toBlocks₂₂ = subF₁ * subF₂) :
    A =
      (Matrix.reindex e.symm e.symm
        (fromBlocks (1 : Matrix ι₁ ι₁ R) 0 0 subF₁)) *
      (Matrix.reindex e.symm e.symm
        (fromBlocks
          ((Matrix.reindex e e A).toBlocks₁₁)
          ((Matrix.reindex e e A).toBlocks₁₂)
          0 subF₂)) := by
  let A_blk : Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R := Matrix.reindex e e A
  let A₁₁ : Matrix ι₁ ι₁ R := A_blk.toBlocks₁₁
  let A₁₂ : Matrix ι₁ ι₂ R := A_blk.toBlocks₁₂
  let A₂₁ : Matrix ι₂ ι₁ R := A_blk.toBlocks₂₁
  let A₂₂ : Matrix ι₂ ι₂ R := A_blk.toBlocks₂₂

  have hA21' : A₂₁ = 0 := by
    simpa [A_blk, A₂₁] using hA21
  have hA22' : A₂₂ = subF₁ * subF₂ := by
    simpa [A_blk, A₂₂] using hA22
  have hA_fromBlocks :
      (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ :
        Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R) = A_blk := by
    simpa [A₁₁, A₁₂, A₂₁, A₂₂, A_blk] using (fromBlocks_toBlocks A_blk)
  have h_blk :
      A_blk =
        (fromBlocks A₁₁ A₁₂ 0 (subF₁ * subF₂) :
          Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R) := by
    calc
      A_blk
          = (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ :
              Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R) := by
                exact hA_fromBlocks.symm
      _ = (fromBlocks A₁₁ A₁₂ 0 (subF₁ * subF₂) :
            Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R) := by
            rw [hA21', hA22']
  have h_blk' :
      (1 : Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R) * A_blk =
        (fromBlocks (1 : Matrix ι₁ ι₁ R) 0 0 subF₁ :
          Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R) *
        (fromBlocks A₁₁ A₁₂ 0 subF₂ :
          Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R) := by
    calc
      (1 : Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R) * A_blk = A_blk := by simp
      _ = (fromBlocks A₁₁ A₁₂ 0 (subF₁ * subF₂) :
            Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R) := h_blk
      _ =
          (fromBlocks (1 : Matrix ι₁ ι₁ R) 0 0 subF₁ :
            Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R) *
          (fromBlocks A₁₁ A₁₂ 0 subF₂ :
            Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R) := by
              symm
              simpa using
                (block_P_mul_A
                  (A₁₁ := A₁₁)
                  (A₁₂ := A₁₂)
                  (A₂₁ := (0 : Matrix ι₂ ι₁ R))
                  (A₂₂ := subF₂)
                  (P' := subF₁))
  have h_transport :=
    schur_case_transport_back (A := A) (e := e)
      (P_blk := (1 : Matrix (ι₁ ⊕ₗ ι₂) (ι₁ ⊕ₗ ι₂) R))
      (L_blk := fromBlocks (1 : Matrix ι₁ ι₁ R) 0 0 subF₁)
      (U_blk := fromBlocks A₁₁ A₁₂ 0 subF₂)
      h_blk'
  simpa [A_blk, A₁₁, A₁₂] using h_transport

end LowLevel

end MatDecompFormal.Components
