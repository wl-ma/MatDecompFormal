/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Normal.Details

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Singular Value Decomposition Details

This file contains the target predicate and small algebraic facts for the SVD
development. The first implementation uses a data-oriented rectangular diagonal
core; this avoids committing prematurely to an order-specific rectangular
diagonal encoding between unrelated row and column index types.
-/

variable {m n : Type*}

/--
Data-oriented rectangular diagonal payload for an SVD.

The maps `row` and `col` identify where each listed singular value is placed.
The `entry_eq` field states that `Σ` is zero away from the listed pairs and has
the listed nonnegative real values on them. The injectivity assumptions prevent
two listed values from competing for the same row or column.
-/
structure RectangularDiagonalData
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (S : Matrix m n ℂ) where
  r : Type
  fintype_r : Fintype r
  row : r → m
  col : r → n
  sigma : r → ℝ
  sigma_nonneg : ∀ k, 0 ≤ sigma k
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  entry_eq :
    ∀ i j,
      S i j =
        ∑ k : r, if row k = i ∧ col k = j then (sigma k : ℂ) else 0

attribute [instance] RectangularDiagonalData.fintype_r

/-- Rectangular diagonal/nonnegative predicate used by the SVD target. -/
def IsRectangularDiagonalNonnegative
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (S : Matrix m n ℂ) : Prop :=
  Nonempty (RectangularDiagonalData S)

/-- Singular value decomposition target for a rectangular complex matrix. -/
def HasSVD
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : Prop :=
  ∃ U : Matrix m m ℂ, ∃ V : Matrix n n ℂ, ∃ S : Matrix m n ℂ,
    IsUnitaryMatrix U ∧
    IsUnitaryMatrix V ∧
    IsRectangularDiagonalNonnegative S ∧
    A = U * S * Vᴴ

/-- Universe-level SVD predicate used by the rectangular subtype induction framework. -/
def SVD_P (x : RectUniverse ℂ) : Prop :=
  HasSVD x.A

def SVD_P_sub (x_sub : PosRectUniverse ℂ) : Prop :=
  SVD_P (x_sub : RectUniverse ℂ)

@[simp] theorem svd_P_compat (x_sub : PosRectUniverse ℂ) :
    SVD_P_sub x_sub ↔ SVD_P (x_sub : RectUniverse ℂ) :=
  Iff.rfl

/-- Empty rectangular diagonal data for the zero matrix. -/
noncomputable def rectangularDiagonalData_zero
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (S : Matrix m n ℂ) (hS : S = 0) :
    RectangularDiagonalData S where
  r := Empty
  fintype_r := inferInstance
  row := Empty.elim
  col := Empty.elim
  sigma := Empty.elim
  sigma_nonneg := by intro k; cases k
  row_injective := by intro k; cases k
  col_injective := by intro k; cases k
  entry_eq := by
    intro i j
    simp [hS]

lemma isRectangularDiagonalNonnegative_zero
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    IsRectangularDiagonalNonnegative (0 : Matrix m n ℂ) :=
  ⟨rectangularDiagonalData_zero 0 rfl⟩

/-- Zero matrices have a trivial SVD. -/
theorem hasSVD_zero
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    HasSVD (0 : Matrix m n ℂ) := by
  refine ⟨1, 1, 0, isUnitaryMatrix_one, isUnitaryMatrix_one, ?_, ?_⟩
  · exact isRectangularDiagonalNonnegative_zero
  · simp

lemma matrix_eq_zero_of_isEmpty_rows
    [Fintype m] [Fintype n] [IsEmpty m] (A : Matrix m n ℂ) :
    A = 0 := by
  ext i
  cases IsEmpty.false i

lemma matrix_eq_zero_of_isEmpty_cols
    [Fintype m] [Fintype n] [IsEmpty n] (A : Matrix m n ℂ) :
    A = 0 := by
  ext i j
  cases IsEmpty.false j

/-- Base SVD witness for matrices with an empty row type. -/
theorem base_svd_empty_rows
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [IsEmpty m]
    (A : Matrix m n ℂ) :
    HasSVD A := by
  rw [matrix_eq_zero_of_isEmpty_rows A]
  exact hasSVD_zero

/-- Base SVD witness for matrices with an empty column type. -/
theorem base_svd_empty_cols
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [IsEmpty n]
    (A : Matrix m n ℂ) :
    HasSVD A := by
  rw [matrix_eq_zero_of_isEmpty_cols A]
  exact hasSVD_zero

/--
Transport an SVD witness across a two-sided unitary transformation.

If `B = Uᴴ * A * V` and `B` has an SVD, then `A` has an SVD by multiplying the
left and right singular-vector factors by `U` and `V`.
-/
theorem svd_transport_twoSidedUnitary
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (A B : Matrix m n ℂ)
    (hU : IsUnitaryMatrix U) (hV : IsUnitaryMatrix V)
    (hB : B = Uᴴ * A * V)
    (hSVD : HasSVD B) :
    HasSVD A := by
  rcases hSVD with ⟨UB, VB, S, hUB, hVB, hS, hEqB⟩
  refine ⟨U * UB, V * VB, S, isUnitaryMatrix_mul hU hUB,
    isUnitaryMatrix_mul hV hVB, hS, ?_⟩
  calc
    A = (U * Uᴴ) * A * (V * Vᴴ) := by
      simp [hU.2, hV.2]
    _ = U * (Uᴴ * A * V) * Vᴴ := by
      simp [Matrix.mul_assoc]
    _ = U * B * Vᴴ := by
      rw [← hB]
    _ = U * (UB * S * VBᴴ) * Vᴴ := by
      rw [hEqB]
    _ = (U * UB) * S * (V * VB)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp [Matrix.mul_assoc]

section BlockLift

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Prepend one nonnegative head entry to rectangular diagonal data. -/
noncomputable def rectangularDiagonalData_blockDiag_unit
    (σ : ℝ) (hσ : 0 ≤ σ) {S : Matrix m n ℂ}
    (data : RectangularDiagonalData S) :
    RectangularDiagonalData
      (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 S :
        Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ) where
  r := Unit ⊕ data.r
  fintype_r := inferInstance
  row := Sum.elim (fun _ => Sum.inl ()) (fun k => Sum.inr (data.row k))
  col := Sum.elim (fun _ => Sum.inl ()) (fun k => Sum.inr (data.col k))
  sigma := Sum.elim (fun _ => σ) data.sigma
  sigma_nonneg := by
    intro k
    cases k with
    | inl u => exact hσ
    | inr k => exact data.sigma_nonneg k
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
  entry_eq := by
    intro i j
    cases i with
    | inl iu =>
        cases j with
        | inl ju =>
            simp
        | inr jn =>
            simp
    | inr im =>
        cases j with
        | inl ju =>
            simp
        | inr jn =>
            simpa using data.entry_eq im jn

lemma isRectangularDiagonalNonnegative_blockDiag_unit
    (σ : ℝ) (hσ : 0 ≤ σ) {S : Matrix m n ℂ}
    (hS : IsRectangularDiagonalNonnegative S) :
    IsRectangularDiagonalNonnegative
      (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 S :
        Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ) := by
  rcases hS with ⟨data⟩
  exact ⟨rectangularDiagonalData_blockDiag_unit σ hσ data⟩

/-- Lift a tail SVD through a rectangular head-tail block diagonal matrix. -/
theorem svd_blockDiag_unit
    (σ : ℝ) (hσ : 0 ≤ σ) {A : Matrix m n ℂ} (hA : HasSVD A) :
    HasSVD
      (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 A :
        Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ) := by
  rcases hA with ⟨U, V, S, hU, hV, hS, hEq⟩
  let Ublk : Matrix (Unit ⊕ m) (Unit ⊕ m) ℂ :=
    fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U
  let Vblk : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
    fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 V
  let Sblk : Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ :=
    fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 S
  refine ⟨Ublk, Vblk, Sblk, ?_, ?_, ?_, ?_⟩
  · exact isUnitaryMatrix_blockDiag_one hU
  · exact isUnitaryMatrix_blockDiag_one hV
  · exact isRectangularDiagonalNonnegative_blockDiag_unit σ hσ hS
  · calc
      (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 A :
          Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ)
          = fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 (U * S * Vᴴ) := by
        rw [hEq]
      _ = Ublk * Sblk * Vblkᴴ := by
        simp [Ublk, Vblk, Sblk, Matrix.fromBlocks_conjTranspose, fromBlocks_multiply,
          Matrix.mul_assoc]

theorem svd_of_blockReady_reindex
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (h₁₁ : A.toBlocks₁₁ = (fun _ _ : Unit => (σ : ℂ)))
    (h₁₂ : A.toBlocks₁₂ = 0) (h₂₁ : A.toBlocks₂₁ = 0)
    (hTail : HasSVD A.toBlocks₂₂) :
    HasSVD A := by
  have hA :
      A =
        fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 A.toBlocks₂₂ := by
    exact (Matrix.ext_iff_blocks).2 ⟨h₁₁, h₁₂, h₂₁, rfl⟩
  rw [hA]
  exact svd_blockDiag_unit σ hσ hTail

theorem svd_reindex
    {m' n' : Type*} [Fintype m'] [DecidableEq m'] [Fintype n'] [DecidableEq n']
    (em : m ≃ m') (en : n ≃ n') {A : Matrix m n ℂ} (hA : HasSVD A) :
    HasSVD (Matrix.reindex em en A) := by
  rcases hA with ⟨U, V, S, hU, hV, hS, hEq⟩
  refine ⟨Matrix.reindex em em U, Matrix.reindex en en V, Matrix.reindex em en S,
    isUnitaryMatrix_reindex em hU, isUnitaryMatrix_reindex en hV, ?_, ?_⟩
  · rcases hS with ⟨data⟩
    refine ⟨{
      r := data.r
      fintype_r := data.fintype_r
      row := fun k => em (data.row k)
      col := fun k => en (data.col k)
      sigma := data.sigma
      sigma_nonneg := data.sigma_nonneg
      row_injective := ?_
      col_injective := ?_
      entry_eq := ?_
    }⟩
    · intro a b h
      exact data.row_injective (em.injective h)
    · intro a b h
      exact data.col_injective (en.injective h)
    · intro i j
      have hentry := data.entry_eq (em.symm i) (en.symm j)
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [hentry]
      apply Finset.sum_congr rfl
      intro k _hk
      have hrow : (em (data.row k) = i) ↔ (data.row k = em.symm i) := by
        constructor
        · intro h
          exact em.injective (by simpa using h)
        · intro h
          simp [h]
      have hcol : (en (data.col k) = j) ↔ (data.col k = en.symm j) := by
        constructor
        · intro h
          exact en.injective (by simpa using h)
        · intro h
          simp [h]
      by_cases h :
          data.row k = em.symm i ∧ data.col k = en.symm j
      · have h' : em (data.row k) = i ∧ en (data.col k) = j :=
          ⟨hrow.2 h.1, hcol.2 h.2⟩
        simp [h]
      · have h' : ¬ (em (data.row k) = i ∧ en (data.col k) = j) := by
          intro hp
          exact h ⟨hrow.1 hp.1, hcol.1 hp.2⟩
        simp [h, h']
  · have hEq' := congrArg (Matrix.reindex em en) hEq
    simpa [Matrix.conjTranspose_reindex, Matrix.submatrix_mul_equiv, Matrix.mul_assoc] using hEq'

end BlockLift

end MatDecompFormal.Instances
