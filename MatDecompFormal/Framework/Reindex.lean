/-
Copyright (c) 2026 Wanli Ma, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanli Ma, Zichen Wang
-/
import Mathlib.Data.Matrix.Block
import MatDecompFormal.Framework.HeadTail

namespace MatDecompFormal.Framework

open Matrix

/-!
# Reindex

Thin helper lemmas around `Matrix.reindex` for block decompositions. No wrapper
structures are introduced here; callers work directly with `Equiv` and `OrderIso`.
-/

section Equiv

variable {ι ι₁ ι₂ κ κ₁ κ₂ R : Type*}

/-- The upper-left block of `reindex er ec A` equals the submatrix of `A` indexed by
`inl`-preimages under `er` and `ec`. -/
@[simp] lemma submatrix_inl_inl_eq_toBlocks₁₁
    (er : ι ≃ ι₁ ⊕ ι₂) (ec : κ ≃ κ₁ ⊕ κ₂) (A : Matrix ι κ R) :
    A.submatrix (fun i => er.symm (Sum.inl i)) (fun j => ec.symm (Sum.inl j)) =
      (Matrix.reindex er ec A).toBlocks₁₁ := by
  rfl

/-- The upper-right block of `reindex er ec A` equals the submatrix of `A` indexed by
`inl`-row and `inr`-column preimages. -/
@[simp] lemma submatrix_inl_inr_eq_toBlocks₁₂
    (er : ι ≃ ι₁ ⊕ ι₂) (ec : κ ≃ κ₁ ⊕ κ₂) (A : Matrix ι κ R) :
    A.submatrix (fun i => er.symm (Sum.inl i)) (fun j => ec.symm (Sum.inr j)) =
      (Matrix.reindex er ec A).toBlocks₁₂ := by
  rfl

/-- The lower-left block of `reindex er ec A` equals the submatrix indexed by
`inr`-row and `inl`-column preimages. -/
@[simp] lemma submatrix_inr_inl_eq_toBlocks₂₁
    (er : ι ≃ ι₁ ⊕ ι₂) (ec : κ ≃ κ₁ ⊕ κ₂) (A : Matrix ι κ R) :
    A.submatrix (fun i => er.symm (Sum.inr i)) (fun j => ec.symm (Sum.inl j)) =
      (Matrix.reindex er ec A).toBlocks₂₁ := by
  rfl

/-- The lower-right block of `reindex er ec A` equals the submatrix indexed by
`inr`-preimages under both `er` and `ec`. -/
@[simp] lemma submatrix_inr_inr_eq_toBlocks₂₂
    (er : ι ≃ ι₁ ⊕ ι₂) (ec : κ ≃ κ₁ ⊕ κ₂) (A : Matrix ι κ R) :
    A.submatrix (fun i => er.symm (Sum.inr i)) (fun j => ec.symm (Sum.inr j)) =
      (Matrix.reindex er ec A).toBlocks₂₂ := by
  rfl


/-- Composing two `reindex` operations is the same as reindexing by the composed equivalences. -/
@[simp] lemma reindex_reindex
    {ι' ι'' κ' κ'' : Type*}
    (er₁ : ι ≃ ι') (ec₁ : κ ≃ κ')
    (er₂ : ι' ≃ ι'') (ec₂ : κ' ≃ κ'')
    (A : Matrix ι κ R) :
    Matrix.reindex er₂ ec₂ (Matrix.reindex er₁ ec₁ A) =
      Matrix.reindex (er₁.trans er₂) (ec₁.trans ec₂) A := by
  ext i j
  rfl

/-- Reindexing a `fromBlocks` matrix by `sumToLexEquiv` yields the same block structure
typed in the lexicographic sum. -/
@[simp] lemma reindex_sumToLex_fromBlocks
    {ι₁ ι₂ κ₁ κ₂ R : Type*}
    (A₁₁ : Matrix ι₁ κ₁ R)
    (A₁₂ : Matrix ι₁ κ₂ R)
    (A₂₁ : Matrix ι₂ κ₁ R)
    (A₂₂ : Matrix ι₂ κ₂ R) :
    Matrix.reindex (sumToLexEquiv ι₁ ι₂) (sumToLexEquiv κ₁ κ₂)
      (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) =
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ : Matrix (ι₁ ⊕ₗ ι₂) (κ₁ ⊕ₗ κ₂) R) := by
  rfl

end Equiv

end MatDecompFormal.Framework
