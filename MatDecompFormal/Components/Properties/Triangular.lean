import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Sum.Order
import Mathlib.Data.FinEnum


namespace MatDecompFormal.Components.Properties

open Matrix

/-!
# Triangular Matrix Properties

This file defines the properties of upper triangular, lower triangular, and
unit lower triangular matrices.

Design notes:

* The definitions depend only on `LinearOrder` on the index type and **do not depend on `FinEnum`**.
* `IsUpperTriangular` uses `Matrix.BlockTriangular` with the identity map as the blocking function
  `fun i ↦ i`, so the condition is equivalent to: if `j < i`, then `A i j = 0`.
* For general `FinEnum` index types, these definitions can be used through the canonical
  `LinearOrder` instance provided in `Framework/FinEnum.lean`.
-/

section Triangular

variable {ι R : Type*} [Zero R]  --[LinearOrder ι]

/--
`IsUpperTriangular A`: matrix `A` is upper triangular under the given index order.

Formally, it is defined as `BlockTriangular` with respect to the identity map `id : ι → ι`:
if `j < i`, then `A i j = 0`.
-/
def IsUpperTriangular [LT ι] (A : Matrix ι ι R) : Prop :=
  BlockTriangular A (fun i : ι => i)

/--
`IsLowerTriangular A`: matrix `A` is lower triangular if and only if `Aᵀ` is upper triangular.
-/
def IsLowerTriangular [LT ι] (A : Matrix ι ι R) : Prop :=
  IsUpperTriangular Aᵀ

/--
`IsUnitLowerTriangular A`: `A` is a unit lower triangular matrix,
that is, lower triangular with all diagonal entries equal to `1`.
-/
def IsUnitLowerTriangular [LT ι] [One R] (A : Matrix ι ι R) : Prop :=
  IsLowerTriangular A ∧ A.diag = 1

-- ==================================================================
-- Basic Properties
-- ==================================================================

variable [One R] [Preorder ι] [DecidableEq ι]

/-- The identity matrix `1` is upper triangular. -/
lemma isUpperTriangular_one : IsUpperTriangular (1 : Matrix ι ι R) := by
  -- The identity matrix is BlockTriangular for any blocking function.
  dsimp [IsUpperTriangular]
  simpa using
    (blockTriangular_one (R := R) (b := fun i : ι => i))

/-- The identity matrix `1` is lower triangular. -/
lemma isLowerTriangular_one : IsLowerTriangular (1 : Matrix ι ι R) := by
  dsimp [IsLowerTriangular]
  -- `(1 : Matrix _ _ _)ᵀ = 1`
  simpa [Matrix.transpose_one] using
    (isUpperTriangular_one (ι := ι) (R := R))

/-- The identity matrix `1` is unit lower triangular. -/
lemma isUnitLowerTriangular_one : IsUnitLowerTriangular (1 : Matrix ι ι R) := by
  constructor
  · exact isLowerTriangular_one (ι := ι) (R := R)
  · -- All diagonal entries are 1
    simp [Matrix.diag_one]

/--
Any square matrix indexed by a subsingleton type, a type with only one element, is upper triangular.
This result is vacuously true because the condition `j < i` can never be satisfied.
-/
lemma isUpperTriangular_of_subsingleton {ι R} [Zero R] [Preorder ι] [Subsingleton ι]
    (A : Matrix ι ι R) : IsUpperTriangular A := by
  dsimp [IsUpperTriangular, BlockTriangular]
  intro i j hij
  -- Because ι is a subsingleton type, any two elements are equal.
  have : i = j := Subsingleton.elim i j
  -- Substitute i = j into hij
  rw [this] at hij
  -- hij is now j < j, contradicting irreflexivity of less-than.
  exfalso; exact lt_irrefl j hij

/--
Any square matrix indexed by a subsingleton type is also lower triangular.
-/
lemma isLowerTriangular_of_subsingleton {ι R} [Zero R] [Preorder ι] [Subsingleton ι]
    (A : Matrix ι ι R) : IsLowerTriangular A := by
  -- Proof: A is lower triangular iff Aᵀ is upper triangular.
  -- Aᵀ is also indexed by a Subsingleton type, so it is upper triangular.
  dsimp [IsLowerTriangular]
  exact isUpperTriangular_of_subsingleton Aᵀ

end Triangular


/-!
## `fromBlocks` and unit lower triangular structure

This subsection provides a lemma specialized for block matrices:
if the lower-right block is unit lower triangular, then
\[
  \begin{pmatrix}
    I & 0 \\
    L₂₁ & L'
  \end{pmatrix}
\]
the whole matrix is still unit lower triangular.
-/


section BlockFromBlocks

variable {n₁ n₂ : ℕ} {R : Type*} [CommRing R]

-- Key point: use the lexicographic index `⊕ₗ`, which has an order structure in Mathlib
local notation "ι" => (Fin n₁ ⊕ₗ Fin n₂)

/--
If the diagonal blocks `A₁₁` and `A₂₂` are both upper triangular, then
after moving `fromBlocks A₁₁ A₁₂ 0 A₂₂` via `reindex Sum.toLex Sum.toLex`
to `Fin n₁ ⊕ₗ Fin n₂`, it is upper triangular.
-/
lemma isUpperTriangular_fromBlocks_toLex
    (A₁₁ : Matrix (Fin n₁) (Fin n₁) R) (A₁₂ : Matrix (Fin n₁) (Fin n₂) R)
    (A₂₂ : Matrix (Fin n₂) (Fin n₂) R)
    (hA₁₁ : IsUpperTriangular A₁₁) (hA₂₂ : IsUpperTriangular A₂₂) :
    IsUpperTriangular
      ((fromBlocks A₁₁ A₁₂ 0 A₂₂ :
          Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R).reindex toLex toLex :
        Matrix ι ι R) := by
  dsimp [IsUpperTriangular, BlockTriangular] at hA₁₁ hA₂₂ ⊢
  intro i j hij
  -- i j : Fin n₁ ⊕ₗ Fin n₂，but we can still split into blocks by cases on inl/inr
  rcases i with i₁ | i₂
  · rcases j with j₁ | j₂
    · -- Upper-left block: reduce to hA₁₁
      have hij' : j₁ < i₁ := Sum.Lex.inl_lt_inl_iff.mp hij
      -- After reindexing, `simp` rewrites entries back to fromBlocks_apply₁₁.
      simpa [Matrix.reindex_apply, fromBlocks_apply₁₁] using hA₁₁ (i := i₁) (j := j₁) hij'
    · -- Upper-right block: `inr _ < inl _` is impossible in lexicographic order
      -- Here j = inr and i = inl, so hij cannot be constructed
      cases hij
  · rcases j with j₁ | j₂
    · -- Lower-left block: the lower-left block of fromBlocks is 0
      simp [ofLex, Lex, fromBlocks_apply₂₁]
    · -- Lower-right block: reduce to hA₂₂
      have hij' : j₂ < i₂ := Sum.Lex.inr_lt_inr_iff.mp hij
      simpa [Matrix.reindex_apply, fromBlocks_apply₂₂] using hA₂₂ (i := i₂) (j := j₂) hij'

/-- A special case of `isUpperTriangular_fromBlocks_toLex`: the upper-left block is 0. -/
lemma isUpperTriangular_fromBlocks_zero_top_toLex
    (A₁₂ : Matrix (Fin n₁) (Fin n₂) R) (A₂₂ : Matrix (Fin n₂) (Fin n₂) R)
    (hA₂₂ : IsUpperTriangular A₂₂) :
    IsUpperTriangular
      ((fromBlocks 0 A₁₂ 0 A₂₂ :
          Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R).reindex toLex toLex :
        Matrix ι ι R) := by
  have h_zero_ut : IsUpperTriangular (0 : Matrix (Fin n₁) (Fin n₁) R) := by
    dsimp [IsUpperTriangular, BlockTriangular]; intro _ _ _; simp
  exact isUpperTriangular_fromBlocks_toLex
    (n₁ := n₁) (n₂ := n₂) (A₁₁ := 0) (A₁₂ := A₁₂) (A₂₂ := A₂₂) h_zero_ut hA₂₂

/--
If `L'` is unit lower triangular, then after moving to `⊕ₗ`,
`fromBlocks 1 0 L₂₁ L'` is also unit lower triangular.
-/
lemma isUnitLowerTriangular_fromBlocks_one_zero_toLex
    (L₂₁ : Matrix (Fin n₂) (Fin n₁) R)
    (L' : Matrix (Fin n₂) (Fin n₂) R)
    (hL' : IsUnitLowerTriangular L') :
    IsUnitLowerTriangular
      ((fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 L₂₁ L' :
          Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R).reindex toLex toLex :
        Matrix ι ι R) := by
  constructor
  · -- lower triangular ↔ transpose is upper triangular
    dsimp [IsLowerTriangular]
    -- transpose commutes with reindex; Mathlib has transpose_reindex
    simpa [Matrix.transpose_reindex, fromBlocks_transpose] using
      (isUpperTriangular_fromBlocks_toLex (n₁ := n₁) (n₂ := n₂)
        (A₁₁ := (1 : Matrix (Fin n₁) (Fin n₁) R)ᵀ)
        (A₁₂ := (L₂₁ : Matrix (Fin n₂) (Fin n₁) R)ᵀ)
        (A₂₂ := (L' : Matrix (Fin n₂) (Fin n₂) R)ᵀ)
        (by simp [transpose_one]; apply isUpperTriangular_one)
        (by
          -- hL'.1 : IsLowerTriangular L' = IsUpperTriangular L'ᵀ
          simpa [IsLowerTriangular] using hL'.1))
  · -- diag = 1
    funext i
    rcases i with i₁ | i₂
    · simp [Matrix.diag, Matrix.reindex_apply, fromBlocks_apply₁₁, Lex, toLex]
    · -- The lower-right diagonal follows from hL'.2
      have := congrArg (fun d => d i₂) hL'.2
      simpa [Matrix.diag, Matrix.reindex_apply, fromBlocks_apply₂₂] using this

end BlockFromBlocks

end MatDecompFormal.Components.Properties
