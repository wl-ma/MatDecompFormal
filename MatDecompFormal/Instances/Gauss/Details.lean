/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import MatDecompFormal.Framework.DecompositionDriver

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Gauss Rank Normal Form Details

Target predicates and proof-side algebra for Gauss/rank normal form.  The normal
form is data-oriented: it records a finite list of independent row/column
positions carrying `1`, with every other entry zero.
-/

variable {R : Type v} {m n : Type u}

/-- Lightweight matrix invertibility witness with an explicit two-sided inverse. -/
def GaussInvertibleMatrix [Semiring R] [Fintype m] [DecidableEq m]
    (P : Matrix m m R) : Prop :=
  ∃ inv : Matrix m m R, inv * P = 1 ∧ P * inv = 1

lemma gaussInvertibleMatrix_one [Semiring R] [Fintype m] [DecidableEq m] :
    GaussInvertibleMatrix (1 : Matrix m m R) :=
  ⟨1, by simp, by simp⟩

lemma GaussInvertibleMatrix.mul [Semiring R] [Fintype m] [DecidableEq m]
    {P Q : Matrix m m R}
    (hP : GaussInvertibleMatrix P) (hQ : GaussInvertibleMatrix Q) :
    GaussInvertibleMatrix (P * Q) := by
  rcases hP with ⟨Pinv, hP_left, hP_right⟩
  rcases hQ with ⟨Qinv, hQ_left, hQ_right⟩
  refine ⟨Qinv * Pinv, ?_, ?_⟩
  · calc
      (Qinv * Pinv) * (P * Q) = Qinv * (Pinv * P) * Q := by
        simp [Matrix.mul_assoc]
      _ = 1 := by simp [hP_left, hQ_left]
  · calc
      (P * Q) * (Qinv * Pinv) = P * (Q * Qinv) * Pinv := by
        simp [Matrix.mul_assoc]
      _ = 1 := by simp [hP_right, hQ_right]

/-- Data-oriented rank-normal-form payload. -/
structure GaussRankBlockData
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (G : Matrix m n R) where
  r : Type u
  fintype_r : Fintype r
  row : r → m
  col : r → n
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  entry_one : ∀ k, G (row k) (col k) = 1
  entry_zero : ∀ i j, (∀ k, row k ≠ i ∨ col k ≠ j) → G i j = 0

attribute [instance] GaussRankBlockData.fintype_r

/-- Predicate saying a matrix is in data-oriented Gauss/rank normal form. -/
def IsGaussRankNormalForm
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (G : Matrix m n R) : Prop :=
  Nonempty (GaussRankBlockData G)

/-- Two-sided equivalence to a rank-normal-form matrix. -/
def HasGaussRankNormalForm
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n R) : Prop :=
  ∃ P : Matrix m m R, ∃ Q : Matrix n n R, ∃ G : Matrix m n R,
    GaussInvertibleMatrix P ∧
    GaussInvertibleMatrix Q ∧
    IsGaussRankNormalForm G ∧
    G = P * A * Q

/-- Universe-level predicate used by the rectangular driver. -/
def GaussRank_P [Semiring R] (x : RectUniverse R) : Prop :=
  HasGaussRankNormalForm x.A

def GaussRank_P_sub [Semiring R] (x_sub : PosRectUniverse R) : Prop :=
  GaussRank_P (x_sub : RectUniverse R)

@[simp] theorem gaussRank_P_compat [Semiring R] (x_sub : PosRectUniverse R) :
    GaussRank_P_sub x_sub ↔ GaussRank_P (x_sub : RectUniverse R) :=
  Iff.rfl

/-- Empty rank-normal-form data for a zero matrix. -/
noncomputable def gaussRankBlockData_zero
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (G : Matrix m n R) (hG : G = 0) :
    GaussRankBlockData G where
  r := ULift Empty
  fintype_r := inferInstance
  row := fun k => Empty.elim k.down
  col := fun k => Empty.elim k.down
  row_injective := by intro k; cases k.down
  col_injective := by intro k; cases k.down
  entry_one := by intro k; cases k.down
  entry_zero := by
    intro i j _h
    simp [hG]

lemma isGaussRankNormalForm_zero
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    IsGaussRankNormalForm (0 : Matrix m n R) :=
  ⟨gaussRankBlockData_zero 0 rfl⟩

/-- Zero matrices have a trivial rank normal form. -/
theorem hasGaussRankNormalForm_zero
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    HasGaussRankNormalForm (0 : Matrix m n R) := by
  refine ⟨1, 1, 0, gaussInvertibleMatrix_one, gaussInvertibleMatrix_one,
    isGaussRankNormalForm_zero, ?_⟩
  simp

lemma gauss_matrix_eq_zero_of_isEmpty_rows
    [Semiring R] [Fintype m] [Fintype n] [IsEmpty m] (A : Matrix m n R) :
    A = 0 := by
  ext i
  cases IsEmpty.false i

lemma gauss_matrix_eq_zero_of_isEmpty_cols
    [Semiring R] [Fintype m] [Fintype n] [IsEmpty n] (A : Matrix m n R) :
    A = 0 := by
  ext i j
  cases IsEmpty.false j

/-- Base witness for matrices with empty row type. -/
theorem base_gauss_empty_rows
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [IsEmpty m] (A : Matrix m n R) :
    HasGaussRankNormalForm A := by
  rw [gauss_matrix_eq_zero_of_isEmpty_rows A]
  exact hasGaussRankNormalForm_zero

/-- Base witness for matrices with empty column type. -/
theorem base_gauss_empty_cols
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [IsEmpty n] (A : Matrix m n R) :
    HasGaussRankNormalForm A := by
  rw [gauss_matrix_eq_zero_of_isEmpty_cols A]
  exact hasGaussRankNormalForm_zero

/-- Reindexing preserves explicit matrix invertibility. -/
lemma gaussInvertibleMatrix_reindex
    [Semiring R] {α β : Type u} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β) {A : Matrix α α R} (hA : GaussInvertibleMatrix A) :
    GaussInvertibleMatrix (Matrix.reindex e e A) := by
  rcases hA with ⟨Ainv, hleft, hright⟩
  refine ⟨Matrix.reindex e e Ainv, ?_, ?_⟩
  · have h := congrArg (Matrix.reindex e e) hleft
    simpa [Matrix.submatrix_mul_equiv] using h
  · have h := congrArg (Matrix.reindex e e) hright
    simpa [Matrix.submatrix_mul_equiv] using h

/-- Reindexing preserves rank normal-form data. -/
theorem isGaussRankNormalForm_reindex
    [Semiring R] {m' n' : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype m'] [DecidableEq m'] [Fintype n'] [DecidableEq n']
    (em : m ≃ m') (en : n ≃ n') {G : Matrix m n R}
    (hG : IsGaussRankNormalForm G) :
    IsGaussRankNormalForm (Matrix.reindex em en G) := by
  rcases hG with ⟨data⟩
  refine ⟨{
    r := data.r
    fintype_r := data.fintype_r
    row := fun k => em (data.row k)
    col := fun k => en (data.col k)
    row_injective := ?_
    col_injective := ?_
    entry_one := ?_
    entry_zero := ?_
  }⟩
  · intro a b h
    exact data.row_injective (em.injective h)
  · intro a b h
    exact data.col_injective (en.injective h)
  · intro k
    simp [data.entry_one k]
  · intro i j h
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    apply data.entry_zero
    intro k
    specialize h k
    rcases h with hrow | hcol
    · exact Or.inl (fun hk => hrow (by simp [hk]))
    · exact Or.inr (fun hk => hcol (by simp [hk]))

/-- Reindexing preserves rank normal-form equivalence. -/
theorem hasGaussRankNormalForm_reindex
    [Semiring R] {m' n' : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype m'] [DecidableEq m'] [Fintype n'] [DecidableEq n']
    (em : m ≃ m') (en : n ≃ n') {A : Matrix m n R}
    (hA : HasGaussRankNormalForm A) :
    HasGaussRankNormalForm (Matrix.reindex em en A) := by
  rcases hA with ⟨P, Q, G, hP, hQ, hG, hEq⟩
  refine ⟨Matrix.reindex em em P, Matrix.reindex en en Q,
    Matrix.reindex em en G, gaussInvertibleMatrix_reindex em hP,
    gaussInvertibleMatrix_reindex en hQ,
    isGaussRankNormalForm_reindex em en hG, ?_⟩
  have hEq' := congrArg (Matrix.reindex em en) hEq
  simpa [Matrix.submatrix_mul_equiv, Matrix.mul_assoc] using hEq'

/--
Transport a Gauss rank normal-form witness across a two-sided invertible
transformation.
-/
theorem gauss_transport_twoSidedUnits
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P₀ : Matrix m m R) (Q₀ : Matrix n n R)
    (A B : Matrix m n R)
    (hP₀ : GaussInvertibleMatrix P₀) (hQ₀ : GaussInvertibleMatrix Q₀)
    (hB : B = P₀ * A * Q₀)
    (hNF : HasGaussRankNormalForm B) :
    HasGaussRankNormalForm A := by
  rcases hNF with ⟨PB, QB, G, hPB, hQB, hG, hEqB⟩
  refine ⟨PB * P₀, Q₀ * QB, G, hPB.mul hP₀, hQ₀.mul hQB, hG, ?_⟩
  calc
    G = PB * B * QB := hEqB
    _ = PB * (P₀ * A * Q₀) * QB := by rw [hB]
    _ = (PB * P₀) * A * (Q₀ * QB) := by simp [Matrix.mul_assoc]

section BlockLift

variable [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Prepend one pivot to rank-normal-form data. -/
noncomputable def gaussRankBlockData_blockDiag_unit
    {G : Matrix m n R} (data : GaussRankBlockData G) :
    GaussRankBlockData
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 G :
        Matrix (Unit ⊕ m) (Unit ⊕ n) R) where
  r := Unit ⊕ data.r
  fintype_r := inferInstance
  row := Sum.elim (fun _ => Sum.inl ()) (fun k => Sum.inr (data.row k))
  col := Sum.elim (fun _ => Sum.inl ()) (fun k => Sum.inr (data.col k))
  row_injective := by
    intro a b h
    cases a with
    | inl au =>
        cases b with
        | inl bu => simp
        | inr bk => cases h
    | inr ak =>
        cases b with
        | inl bu => cases h
        | inr bk =>
            simp only [Sum.elim_inr, Sum.inr.injEq] at h
            exact congrArg Sum.inr (data.row_injective h)
  col_injective := by
    intro a b h
    cases a with
    | inl au =>
        cases b with
        | inl bu => simp
        | inr bk => cases h
    | inr ak =>
        cases b with
        | inl bu => cases h
        | inr bk =>
            simp only [Sum.elim_inr, Sum.inr.injEq] at h
            exact congrArg Sum.inr (data.col_injective h)
  entry_one := by
    intro k
    cases k with
    | inl u => simp
    | inr k => simpa using data.entry_one k
  entry_zero := by
    intro i j h
    cases i with
    | inl iu =>
        cases j with
        | inl ju =>
            exfalso
            exact (h (Sum.inl ())).elim (by simp) (by simp)
        | inr jn => simp
    | inr im =>
        cases j with
        | inl ju => simp
        | inr jn =>
            apply data.entry_zero
            intro k
            specialize h (Sum.inr k)
            rcases h with hrow | hcol
            · exact Or.inl (fun hk => hrow (by simp [hk]))
            · exact Or.inr (fun hk => hcol (by simp [hk]))

lemma isGaussRankNormalForm_blockDiag_unit
    {G : Matrix m n R} (hG : IsGaussRankNormalForm G) :
    IsGaussRankNormalForm
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 G :
        Matrix (Unit ⊕ m) (Unit ⊕ n) R) := by
  rcases hG with ⟨data⟩
  exact ⟨gaussRankBlockData_blockDiag_unit data⟩

lemma gaussInvertibleMatrix_blockDiag_one
    {α : Type u} [Fintype α] [DecidableEq α] {P : Matrix α α R}
    (hP : GaussInvertibleMatrix P) :
    GaussInvertibleMatrix
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 P :
        Matrix (Unit ⊕ α) (Unit ⊕ α) R) := by
  rcases hP with ⟨Pinv, hleft, hright⟩
  refine ⟨fromBlocks (1 : Matrix Unit Unit R) 0 0 Pinv, ?_, ?_⟩
  · calc
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 Pinv :
          Matrix (Unit ⊕ α) (Unit ⊕ α) R) *
          fromBlocks (1 : Matrix Unit Unit R) 0 0 P =
          fromBlocks (1 : Matrix Unit Unit R) 0 0 (Pinv * P) := by
        simp [fromBlocks_multiply]
      _ = 1 := by
        rw [hleft]
        exact Matrix.fromBlocks_one
  · calc
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 P :
          Matrix (Unit ⊕ α) (Unit ⊕ α) R) *
          fromBlocks (1 : Matrix Unit Unit R) 0 0 Pinv =
          fromBlocks (1 : Matrix Unit Unit R) 0 0 (P * Pinv) := by
        simp [fromBlocks_multiply]
      _ = 1 := by
        rw [hright]
        exact Matrix.fromBlocks_one

/-- Lift a tail rank normal form through a block diagonal head pivot. -/
theorem gauss_blockDiag_unit
    {A : Matrix m n R} (hA : HasGaussRankNormalForm A) :
    HasGaussRankNormalForm
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 A :
        Matrix (Unit ⊕ m) (Unit ⊕ n) R) := by
  rcases hA with ⟨P, Q, G, hP, hQ, hG, hEq⟩
  let Pblk : Matrix (Unit ⊕ m) (Unit ⊕ m) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 P
  let Qblk : Matrix (Unit ⊕ n) (Unit ⊕ n) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 Q
  let Gblk : Matrix (Unit ⊕ m) (Unit ⊕ n) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 G
  refine ⟨Pblk, Qblk, Gblk, ?_, ?_, ?_, ?_⟩
  · exact gaussInvertibleMatrix_blockDiag_one hP
  · exact gaussInvertibleMatrix_blockDiag_one hQ
  · exact isGaussRankNormalForm_blockDiag_unit hG
  · calc
      Gblk = fromBlocks (1 : Matrix Unit Unit R) 0 0 (P * A * Q) := by
        simp [Gblk, hEq]
      _ = Pblk *
            (fromBlocks (1 : Matrix Unit Unit R) 0 0 A :
              Matrix (Unit ⊕ m) (Unit ⊕ n) R) * Qblk := by
        simp [Pblk, Qblk, fromBlocks_multiply, Matrix.mul_assoc]

/-- Lift from an isolated-pivot block-ready matrix. -/
theorem gauss_of_blockReady_reindex
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R)
    (h₁₁ : A.toBlocks₁₁ = 1)
    (h₁₂ : A.toBlocks₁₂ = 0) (h₂₁ : A.toBlocks₂₁ = 0)
    (hTail : HasGaussRankNormalForm A.toBlocks₂₂) :
    HasGaussRankNormalForm A := by
  have hA :
      A =
        fromBlocks (1 : Matrix Unit Unit R) 0 0 A.toBlocks₂₂ := by
    exact (Matrix.ext_iff_blocks).2 ⟨h₁₁, h₁₂, h₂₁, rfl⟩
  rw [hA]
  exact gauss_blockDiag_unit hTail

end BlockLift

end MatDecompFormal.Instances
