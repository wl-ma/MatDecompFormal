/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.SVD.Details

universe u

namespace MatDecompFormal.Instances

open Matrix

/-!
# Singular Value Decomposition Specs

This file records user-facing consequences of an SVD witness.  The main
spectral bridge is the right-Gram model: if `A = U * S * Vᴴ`, then `Aᴴ * A` is
unitarily conjugate to `Sᴴ * S`.  Since `S` is the rectangular nonnegative
diagonal payload, later spectrum/charpoly APIs can work only with the diagonal
singular-value square model.
-/

variable {m n : Type u}

/--
Right-Gram spec carried by an SVD witness.

The matrix `S` is the rectangular nonnegative diagonal factor, and the final
equality states that `Aᴴ * A` is the unitary conjugate of `Sᴴ * S` by the right
singular factor `V`.
-/
def SVDRightGramSpec
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : Prop :=
  ∃ V : Matrix n n ℂ, ∃ S : Matrix m n ℂ,
    IsUnitaryMatrix V ∧
    IsRectangularDiagonalNonnegative S ∧
    Aᴴ * A = V * (Sᴴ * S) * Vᴴ

/--
Extract the right-Gram spec from any `HasSVD` witness.

This is the first public bridge from the decomposition statement to the usual
spectral meaning of SVD: the eigenvalues of `Aᴴ * A` are represented, up to
unitary conjugacy, by the squared rectangular diagonal singular values in
`Sᴴ * S`.
-/
theorem hasSVD_rightGramSpec
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m n ℂ} (hA : HasSVD A) :
    SVDRightGramSpec A := by
  rcases hA with ⟨U, V, S, hU, hV, hS, hEq⟩
  refine ⟨V, S, hV, hS, ?_⟩
  calc
    Aᴴ * A = (U * S * Vᴴ)ᴴ * (U * S * Vᴴ) := by
      rw [hEq]
    _ = V * (Sᴴ * (Uᴴ * U) * S) * Vᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp [Matrix.mul_assoc]
    _ = V * (Sᴴ * S) * Vᴴ := by
      simp [hU.1, Matrix.mul_assoc]

/--
The right-Gram matrix of an SVD is unitarily conjugate to the square of its
rectangular diagonal factor.
-/
theorem hasSVD_rightGram_eq_unitary_conjugate
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m n ℂ} (hA : HasSVD A) :
    ∃ V : Matrix n n ℂ, ∃ S : Matrix m n ℂ,
      IsUnitaryMatrix V ∧
      IsRectangularDiagonalNonnegative S ∧
      Aᴴ * A = V * (Sᴴ * S) * Vᴴ :=
  hasSVD_rightGramSpec hA

/-- A unitary matrix is a unit of the matrix ring. -/
lemma isUnit_of_isUnitaryMatrix
    [Fintype n] [DecidableEq n] {V : Matrix n n ℂ}
    (hV : IsUnitaryMatrix V) :
    IsUnit V := by
  refine ⟨
    { val := V
      inv := Vᴴ
      val_inv := hV.2
      inv_val := hV.1 },
    rfl⟩

/--
The right-Gram matrix and the squared rectangular diagonal factor have the same
characteristic polynomial.
-/
theorem hasSVD_rightGram_charpoly_eq_diagonalGram
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m n ℂ} (hA : HasSVD A) :
    ∃ S : Matrix m n ℂ,
      IsRectangularDiagonalNonnegative S ∧
      (Aᴴ * A).charpoly = (Sᴴ * S).charpoly := by
  rcases hasSVD_rightGramSpec hA with ⟨V, S, hV, hS, hGram⟩
  refine ⟨S, hS, ?_⟩
  let Vunit : (Matrix n n ℂ)ˣ :=
    { val := V
      inv := Vᴴ
      val_inv := hV.2
      inv_val := hV.1 }
  have hconj : Vunit.val * (Sᴴ * S) * Vunit⁻¹.val = Aᴴ * A := by
    simpa [Vunit] using hGram.symm
  calc
    (Aᴴ * A).charpoly = (Vunit.val * (Sᴴ * S) * Vunit⁻¹.val).charpoly := by
      rw [hconj]
    _ = (Sᴴ * S).charpoly := by
      have h := Matrix.charpoly_units_conj Vunit (Sᴴ * S)
      simpa using h

/--
Listed entries of a rectangular diagonal payload are exactly their singular
values.
-/
lemma RectangularDiagonalData.entry_row_col
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {S : Matrix m n ℂ} (data : RectangularDiagonalData S) (k : data.r) :
    S (data.row k) (data.col k) = (data.sigma k : ℂ) := by
  rw [data.entry_eq]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro k' hk'
    by_cases hrow : data.row k' = data.row k
    · have hcol : data.col k' ≠ data.col k := by
        intro hc
        exact hk' (data.col_injective hc)
      simp [hrow, hcol]
    · simp [hrow]

/--
Away from a listed row, a fixed listed column of a rectangular diagonal payload
is zero.
-/
lemma RectangularDiagonalData.entry_col_eq_zero_of_row_ne
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {S : Matrix m n ℂ} (data : RectangularDiagonalData S)
    {i : m} (k : data.r) (hi : i ≠ data.row k) :
    S i (data.col k) = 0 := by
  rw [data.entry_eq]
  refine Finset.sum_eq_zero ?_
  intro k' _
  by_cases hrow : data.row k' = i
  · have hcol : data.col k' ≠ data.col k := by
      intro hc
      have hk : k' = k := data.col_injective hc
      subst hk
      exact hi hrow.symm
    simp [hrow, hcol]
  · simp [hrow]

/--
The right-Gram diagonal entry at a listed singular-value column is the square of
that singular value.
-/
lemma RectangularDiagonalData.rightGram_entry_col
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {S : Matrix m n ℂ} (data : RectangularDiagonalData S) (k : data.r) :
    (Sᴴ * S) (data.col k) (data.col k) =
      (data.sigma k : ℂ) * (data.sigma k : ℂ) := by
  rw [Matrix.mul_apply]
  rw [Fintype.sum_eq_single (data.row k)]
  · simp [Matrix.conjTranspose_apply, data.entry_row_col k]
  · intro i hi
    have hzero : S i (data.col k) = 0 :=
      data.entry_col_eq_zero_of_row_ne k hi
    simp [Matrix.conjTranspose_apply, hzero]

end MatDecompFormal.Instances
