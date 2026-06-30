/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Gauss.Details
import MatDecompFormal.Instances.Hessenberg.Boundary
import MatDecompFormal.Instances.Normal.Details

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# UTV Decomposition Details

This file defines the UTV target predicate used by the rectangular descent
framework. The ordinary UTV middle factor is a genuine rectangular upper
trapezoidal matrix with respect to the finite row and column orders.
-/

variable {m n : Type u}

/-- Generic rectangular upper-triangular/rank-normal middle factor. -/
def IsGenericRectangularUpperTriangular
    {R : Type v} [Semiring R]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (T : Matrix m n R) : Prop :=
  IsGaussRankNormalForm (R := R) (m := m) (n := n) T

/-- Generic two-sided triangular equivalence target over a semiring. -/
def HasTriangularEquivalence
    {R : Type v} [Semiring R]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n R) : Prop :=
  ∃ P : Matrix m m R, ∃ Q : Matrix n n R, ∃ T : Matrix m n R,
    GaussInvertibleMatrix (R := R) (m := m) P ∧
    GaussInvertibleMatrix (R := R) (m := n) Q ∧
    IsGenericRectangularUpperTriangular T ∧
    A = P * T * Q

/-- Universe-level generic triangular equivalence predicate. -/
def TriangularEquivalence_P {R : Type v} [Semiring R] (x : RectUniverse R) : Prop :=
  HasTriangularEquivalence x.A

def TriangularEquivalence_P_sub {R : Type v} [Semiring R] (x_sub : PosRectUniverse R) :
    Prop :=
  TriangularEquivalence_P (x_sub : RectUniverse R)

@[simp] theorem triangularEquivalence_P_compat {R : Type v} [Semiring R]
    (x_sub : PosRectUniverse R) :
    TriangularEquivalence_P_sub x_sub ↔
      TriangularEquivalence_P (x_sub : RectUniverse R) :=
  Iff.rfl

lemma gaussInvertibleMatrix_inverse
    {R : Type v} [Semiring R] [Fintype m] [DecidableEq m]
    {P Pinv : Matrix m m R}
    (hleft : Pinv * P = 1) (hright : P * Pinv = 1) :
    GaussInvertibleMatrix Pinv :=
  ⟨P, hright, hleft⟩

/-- A Gauss rank-normal-form witness gives generic triangular equivalence. -/
theorem hasTriangularEquivalence_of_gauss
    {R : Type v} [Semiring R]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m n R}
    (hA : HasGaussRankNormalForm (R := R) (m := m) (n := n) A) :
    HasTriangularEquivalence A := by
  rcases hA with ⟨P, Q, G, hP, hQ, hG, hEq⟩
  rcases hP with ⟨Pinv, hP_left, hP_right⟩
  rcases hQ with ⟨Qinv, hQ_left, hQ_right⟩
  refine ⟨Pinv, Qinv, G,
    gaussInvertibleMatrix_inverse hP_left hP_right,
    gaussInvertibleMatrix_inverse hQ_left hQ_right,
    hG, ?_⟩
  calc
    A = (Pinv * P) * A * (Q * Qinv) := by
      simp [hP_left, hQ_right]
    _ = Pinv * (P * A * Q) * Qinv := by
      simp [Matrix.mul_assoc]
    _ = Pinv * G * Qinv := by
      rw [← hEq]

/-- Generic triangular equivalence gives a Gauss rank-normal-form witness. -/
theorem gauss_of_hasTriangularEquivalence
    {R : Type v} [Semiring R]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m n R}
    (hA : HasTriangularEquivalence A) :
    HasGaussRankNormalForm (R := R) (m := m) (n := n) A := by
  rcases hA with ⟨P, Q, T, hP, hQ, hT, hEq⟩
  rcases hP with ⟨Pinv, hP_left, hP_right⟩
  rcases hQ with ⟨Qinv, hQ_left, hQ_right⟩
  refine ⟨Pinv, Qinv, T,
    gaussInvertibleMatrix_inverse hP_left hP_right,
    gaussInvertibleMatrix_inverse hQ_left hQ_right,
    hT, ?_⟩
  calc
    T = (Pinv * P) * T * (Q * Qinv) := by
      simp [hP_left, hQ_right]
    _ = Pinv * (P * T * Q) * Qinv := by
      simp [Matrix.mul_assoc]
    _ = Pinv * A * Qinv := by
      rw [← hEq]

/-- Order rank of a row index in a finite linear order. -/
noncomputable def rowRank (m : Type*) [Fintype m] [LinearOrder m] (i : m) : Nat :=
  finiteOrderRank m i

/-- Order rank of a column index in a finite linear order. -/
noncomputable def colRank (n : Type*) [Fintype n] [LinearOrder n] (j : n) : Nat :=
  finiteOrderRank n j

/--
Rectangular upper-triangular/trapezoidal payload.

Entries strictly below the rectangular main diagonal vanish: a row whose order
rank is larger than the column rank cannot carry a nonzero entry.
-/
def IsRectangularUpperTriangular
    {R m n : Type*} [Zero R]
    [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n]
    (T : Matrix m n R) : Prop :=
  ∀ i j, colRank n j < rowRank m i → T i j = 0

/-- Complex unitary UTV target for a rectangular matrix. -/
def HasUTV
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) : Prop :=
  ∃ U : Matrix m m ℂ, ∃ V : Matrix n n ℂ, ∃ T : Matrix m n ℂ,
    IsUnitaryMatrix U ∧
    IsUnitaryMatrix V ∧
    IsRectangularUpperTriangular T ∧
    A = U * T * Vᴴ

/-- Universe-level UTV predicate used by the rectangular subtype driver. -/
def UTV_P (x : RectUniverse ℂ) : Prop :=
  HasUTV x.A

def UTV_P_sub (x_sub : PosRectUniverse ℂ) : Prop :=
  UTV_P (x_sub : RectUniverse ℂ)

@[simp] theorem utv_P_compat (x_sub : PosRectUniverse ℂ) :
    UTV_P_sub x_sub ↔ UTV_P (x_sub : RectUniverse ℂ) :=
  Iff.rfl

lemma isRectangularUpperTriangular_zero
    [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n] :
    IsRectangularUpperTriangular (0 : Matrix m n ℂ) := by
  intro i j hij
  simp

/-- Zero matrices have a trivial UTV decomposition. -/
theorem hasUTV_zero
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] :
    HasUTV (0 : Matrix m n ℂ) := by
  refine ⟨1, 1, 0, isUnitaryMatrix_one, isUnitaryMatrix_one, ?_, ?_⟩
  · exact isRectangularUpperTriangular_zero
  · simp

lemma utv_matrix_eq_zero_of_isEmpty_rows
    [Fintype m] [Fintype n] [IsEmpty m] (A : Matrix m n ℂ) :
    A = 0 := by
  ext i
  cases IsEmpty.false i

lemma utv_matrix_eq_zero_of_isEmpty_cols
    [Fintype m] [Fintype n] [IsEmpty n] (A : Matrix m n ℂ) :
    A = 0 := by
  ext i j
  cases IsEmpty.false j

/-- Base UTV witness for matrices with an empty row type. -/
theorem base_utv_empty_rows
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [IsEmpty m]
    (A : Matrix m n ℂ) :
    HasUTV A := by
  rw [utv_matrix_eq_zero_of_isEmpty_rows A]
  exact hasUTV_zero

/-- Base UTV witness for matrices with an empty column type. -/
theorem base_utv_empty_cols
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [IsEmpty n]
    (A : Matrix m n ℂ) :
    HasUTV A := by
  rw [utv_matrix_eq_zero_of_isEmpty_cols A]
  exact hasUTV_zero

/-- Transport a UTV witness across a two-sided unitary transformation. -/
theorem utv_transport_twoSidedUnitary
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (A B : Matrix m n ℂ)
    (hU : IsUnitaryMatrix U) (hV : IsUnitaryMatrix V)
    (hB : B = Uᴴ * A * V)
    (hUTV : HasUTV B) :
    HasUTV A := by
  rcases hUTV with ⟨UB, VB, T, hUB, hVB, hT, hEqB⟩
  refine ⟨U * UB, V * VB, T, isUnitaryMatrix_mul hU hUB,
    isUnitaryMatrix_mul hV hVB, hT, ?_⟩
  calc
    A = (U * Uᴴ) * A * (V * Vᴴ) := by
      simp [hU.2, hV.2]
    _ = U * (Uᴴ * A * V) * Vᴴ := by
      simp [Matrix.mul_assoc]
    _ = U * B * Vᴴ := by
      rw [← hB]
    _ = U * (UB * T * VBᴴ) * Vᴴ := by
      rw [hEqB]
    _ = (U * UB) * T * (V * VB)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp [Matrix.mul_assoc]

section Reindex

variable {m n : Type u}
variable [Fintype m] [DecidableEq m] [LinearOrder m]
variable [Fintype n] [DecidableEq n] [LinearOrder n]

omit [DecidableEq m] [DecidableEq n] in
/-- Strictly monotone reindexing preserves the rectangular upper-triangular shape. -/
theorem isRectangularUpperTriangular_reindex_strictMono
    {m' n' : Type u}
    [Fintype m'] [LinearOrder m'] [Fintype n'] [LinearOrder n']
    (em : m ≃ m') (en : n ≃ n') (hem : StrictMono em) (hen : StrictMono en)
    {T : Matrix m n ℂ} (hT : IsRectangularUpperTriangular T) :
    IsRectangularUpperTriangular (Matrix.reindex em en T) := by
  intro i j hij
  have hij' : colRank n (en.symm j) < rowRank m (em.symm i) := by
    simpa [rowRank, colRank, finiteOrderRank_equiv_symm em hem i,
      finiteOrderRank_equiv_symm en hen j] using hij
  simpa [Matrix.reindex_apply] using hT (em.symm i) (en.symm j) hij'

/-- Strictly monotone reindexing preserves UTV witnesses. -/
theorem utv_reindex_strictMono
    {m' n' : Type u}
    [Fintype m'] [DecidableEq m'] [LinearOrder m']
    [Fintype n'] [DecidableEq n'] [LinearOrder n']
    (em : m ≃ m') (en : n ≃ n') (hem : StrictMono em) (hen : StrictMono en)
    {A : Matrix m n ℂ} (hA : HasUTV A) :
    HasUTV (Matrix.reindex em en A) := by
  rcases hA with ⟨U, V, T, hU, hV, hT, hEq⟩
  refine ⟨Matrix.reindex em em U, Matrix.reindex en en V, Matrix.reindex em en T,
    isUnitaryMatrix_reindex em hU, isUnitaryMatrix_reindex en hV, ?_, ?_⟩
  · exact isRectangularUpperTriangular_reindex_strictMono em en hem hen hT
  · have hEq' := congrArg (Matrix.reindex em en) hEq
    simpa [Matrix.conjTranspose_reindex, Matrix.submatrix_mul_equiv, Matrix.mul_assoc] using hEq'

lemma strictMono_symm_of_strictMono_equiv
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : α ≃ β) (he : StrictMono e) :
    StrictMono e.symm := by
  intro a b hab
  have h : e (e.symm a) < e (e.symm b) := by simpa using hab
  exact (he.lt_iff_lt).1 h

end Reindex

section BlockLift

open Sum.Lex

variable {m n : Type u}
variable [Fintype m] [DecidableEq m] [LinearOrder m]
variable [Fintype n] [DecidableEq n] [LinearOrder n]

omit [DecidableEq m] [DecidableEq n] in
/-- A lower-left-zero one-head block matrix is rectangular upper triangular. -/
theorem isRectangularUpperTriangular_fromBlocks_lowerLeft_zero
    (T₁₁ : Matrix Unit Unit ℂ) (T : Matrix m n ℂ)
    (hT : IsRectangularUpperTriangular T) :
    IsRectangularUpperTriangular
      (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
        (fromBlocks T₁₁ 0 0 T : Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ)) := by
  intro i j hij
  cases hi : ofLex i with
  | inl iu =>
      cases iu
      have i_eq : i = (Sum.inlₗ () : Unit ⊕ₗ m) := by
        rw [← toLex_ofLex i, hi]
      subst i
      rw [rowRank, finiteOrderRank_sumLex_inl_unit] at hij
      exact (Nat.not_lt_zero _ hij).elim
  | inr ii =>
      have i_eq : i = (Sum.inrₗ ii : Unit ⊕ₗ m) := by
        rw [← toLex_ofLex i, hi]
      subst i
      cases hj : ofLex j with
      | inl ju =>
          cases ju
          rw [← toLex_ofLex j, hj]
          simp [Matrix.reindex_apply, sumToLexEquiv]
      | inr jj =>
          have j_eq : j = (Sum.inrₗ jj : Unit ⊕ₗ n) := by
            rw [← toLex_ofLex j, hj]
          subst j
          have hijTail : colRank n jj < rowRank m ii := by
            dsimp [rowRank, colRank]
            rw [rowRank, colRank, finiteOrderRank_sumLex_inr,
              finiteOrderRank_sumLex_inr] at hij
            omega
          simpa [Matrix.reindex_apply, sumToLexEquiv] using hT ii jj hijTail

/-- Lift a tail UTV witness through a lexicographic block diagonal head-tail matrix. -/
theorem utv_blockDiag_unit
    (σ : ℝ) {A : Matrix m n ℂ} (hA : HasUTV A) :
    HasUTV
      (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
        (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 A :
          Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ)) := by
  rcases hA with ⟨U, V, T, hU, hV, hT, hEq⟩
  let Ublk : Matrix (Unit ⊕ₗ m) (Unit ⊕ₗ m) ℂ :=
    Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit m)
      (fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U :
        Matrix (Unit ⊕ m) (Unit ⊕ m) ℂ)
  let Vblk : Matrix (Unit ⊕ₗ n) (Unit ⊕ₗ n) ℂ :=
    Matrix.reindex (sumToLexEquiv Unit n) (sumToLexEquiv Unit n)
      (fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 V :
        Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)
  let Tblk : Matrix (Unit ⊕ₗ m) (Unit ⊕ₗ n) ℂ :=
    Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
      (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 T :
        Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ)
  refine ⟨Ublk, Vblk, Tblk, ?_, ?_, ?_, ?_⟩
  · exact isUnitaryMatrix_reindex (sumToLexEquiv Unit m)
      (isUnitaryMatrix_blockDiag_one hU)
  · exact isUnitaryMatrix_reindex (sumToLexEquiv Unit n)
      (isUnitaryMatrix_blockDiag_one hV)
  · exact isRectangularUpperTriangular_fromBlocks_lowerLeft_zero
      (fun _ _ : Unit => (σ : ℂ)) T hT
  · calc
      Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
          (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 A :
            Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ)
          = Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
              (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 (U * T * Vᴴ) :
                Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ) := by
        rw [hEq]
      _ = Ublk * Tblk * Vblkᴴ := by
        have hraw :
            (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 (U * T * Vᴴ) :
              Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ) =
                (fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U :
                  Matrix (Unit ⊕ m) (Unit ⊕ m) ℂ) *
                  (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 T :
                    Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ) *
                  (fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 V :
                    Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)ᴴ := by
          ext i j
          cases i
          · cases j
            · simp [Matrix.fromBlocks_conjTranspose, fromBlocks_multiply,
                Matrix.mul_assoc]
            · simp [Matrix.fromBlocks_conjTranspose, fromBlocks_multiply,
                Matrix.mul_assoc]
          · cases j
            · simp [Matrix.fromBlocks_conjTranspose, fromBlocks_multiply,
                Matrix.mul_assoc]
            · simp [Matrix.fromBlocks_conjTranspose, fromBlocks_multiply,
                Matrix.mul_assoc]
        have hlex := congrArg
          (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)) hraw
        simpa [Ublk, Vblk, Tblk, Matrix.conjTranspose_reindex,
          Matrix.submatrix_mul_equiv, Matrix.mul_assoc] using hlex

theorem utv_of_blockReady_reindex
    (A : Matrix (Unit ⊕ₗ m) (Unit ⊕ₗ n) ℂ)
    (σ : ℝ)
    (h₁₁ : A.toBlocks₁₁ = (fun _ _ : Unit => (σ : ℂ)))
    (h₁₂ : A.toBlocks₁₂ = 0) (h₂₁ : A.toBlocks₂₁ = 0)
    (hTail : HasUTV A.toBlocks₂₂) :
    HasUTV A := by
  have hA :
      A =
        Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
          (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 A.toBlocks₂₂ :
            Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ) := by
    exact (Matrix.ext_iff_blocks).2 ⟨h₁₁, h₁₂, h₂₁, rfl⟩
  rw [hA]
  exact utv_blockDiag_unit σ hTail

end BlockLift

end MatDecompFormal.Instances
