import Mathlib.Data.Sum.Order
import Mathlib.LinearAlgebra.Matrix.Block
import MatDecompFormal.Components.BlockAlgebra

namespace MatDecompFormal.Components

open Matrix
open MatDecompFormal.Framework

/-!
# Lifting Low-Level Tools

This file contains equation-level transport and assembly lemmas shared by
higher-level lifting constructions.
-/

section LowLevel

variable {R : Type*} [Field R]

/-- Transport a block-world equality back to `Fin (k + 1)`. -/
lemma schur_case_transport_back {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (e : Fin (k + 1) ≃ (Fin 1) ⊕ₗ (Fin k))
    (P_blk L_blk U_blk :
      Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R)
    (h_blk : P_blk * (Matrix.reindex e e A) = L_blk * U_blk) :
    (Matrix.reindex e.symm e.symm P_blk) * A =
      (Matrix.reindex e.symm e.symm L_blk) * (Matrix.reindex e.symm e.symm U_blk) := by
  let P : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm P_blk
  let U : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm U_blk
  let L : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm L_blk

  have h_back := congrArg (Matrix.reindex e.symm e.symm) h_blk
  dsimp [P, L, U]
  rw [← submatrix_mul]
  · simp only [reindex_apply, Equiv.symm_symm] at h_back
    rw [← h_back]
    classical
    let Aℓ : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R := Matrix.reindex e e A
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
lemma lift_two_factor_from_zero_block21 {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (subF₁ subF₂ : Matrix (Fin k) (Fin k) R)
    (hA21 :
      (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₂₁ = 0)
    (hA22 :
      (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₂₂ =
        subF₁ * subF₂) :
    A =
      (Matrix.reindex (finSuccEquivSumLex k).symm (finSuccEquivSumLex k).symm
        (fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subF₁)) *
      (Matrix.reindex (finSuccEquivSumLex k).symm (finSuccEquivSumLex k).symm
        (fromBlocks
          ((Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₁)
          ((Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₂)
          0 subF₂)) := by
  let e : Fin (k + 1) ≃ (Fin 1) ⊕ₗ Fin k := finSuccEquivSumLex k
  let A_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R := Matrix.reindex e e A
  let A₁₁ : Matrix (Fin 1) (Fin 1) R := A_blk.toBlocks₁₁
  let A₁₂ : Matrix (Fin 1) (Fin k) R := A_blk.toBlocks₁₂
  let A₂₁ : Matrix (Fin k) (Fin 1) R := A_blk.toBlocks₂₁
  let A₂₂ : Matrix (Fin k) (Fin k) R := A_blk.toBlocks₂₂

  have hA21' : A₂₁ = 0 := by
    simpa [e, A_blk, A₂₁] using hA21
  have hA22' : A₂₂ = subF₁ * subF₂ := by
    simpa [e, A_blk, A₂₂] using hA22
  have hA_fromBlocks :
      (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ :
        Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) = A_blk := by
    simpa [A₁₁, A₁₂, A₂₁, A₂₂, A_blk] using (fromBlocks_toBlocks A_blk)
  have h_blk :
      A_blk =
        (fromBlocks A₁₁ A₁₂ 0 (subF₁ * subF₂) :
          Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
    calc
      A_blk
          = (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ :
              Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
                exact hA_fromBlocks.symm
      _ = (fromBlocks A₁₁ A₁₂ 0 (subF₁ * subF₂) :
            Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
            rw [hA21', hA22']
  have h_blk' :
      (1 : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) * A_blk =
        (fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subF₁ :
          Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) *
        (fromBlocks A₁₁ A₁₂ 0 subF₂ :
          Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
    calc
      (1 : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) * A_blk = A_blk := by simp
      _ = (fromBlocks A₁₁ A₁₂ 0 (subF₁ * subF₂) :
            Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := h_blk
      _ =
          (fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subF₁ :
            Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) *
          (fromBlocks A₁₁ A₁₂ 0 subF₂ :
            Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
              symm
              simpa using
                (block_P_mul_A
                  (A₁₁ := A₁₁)
                  (A₁₂ := A₁₂)
                  (A₂₁ := (0 : Matrix (Fin k) (Fin 1) R))
                  (A₂₂ := subF₂)
                  (P' := subF₁))
  have h_transport :=
    schur_case_transport_back (R := R) (k := k) (A := A) (e := e)
      (P_blk := (1 : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R))
      (L_blk := fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subF₁)
      (U_blk := fromBlocks A₁₁ A₁₂ 0 subF₂)
      h_blk'
  simpa [e, A_blk, A₁₁, A₁₂] using h_transport

end LowLevel

end MatDecompFormal.Components
