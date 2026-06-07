import MatDecompFormal.Instances.Gauss.Details
import MatDecompFormal.Instances.SVD.Details

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# UTV Decomposition Details

This file defines the UTV target predicate used by the rectangular descent
framework. The middle factor is represented by the same data-oriented
rectangular diagonal payload used by SVD; this is a valid UTV middle factor and
keeps the first implementation focused on the framework route.
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

/-- Rectangular upper-triangular payload for the current UTV target. -/
def IsRectangularUpperTriangular
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (T : Matrix m n ℂ) : Prop :=
  IsRectangularDiagonalNonnegative T

/-- Complex unitary UTV target for a rectangular matrix. -/
def HasUTV
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
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
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    IsRectangularUpperTriangular (0 : Matrix m n ℂ) :=
  isRectangularDiagonalNonnegative_zero

/-- Zero matrices have a trivial UTV decomposition. -/
theorem hasUTV_zero
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    HasUTV (0 : Matrix m n ℂ) := by
  refine ⟨1, 1, 0, isUnitaryMatrix_one, isUnitaryMatrix_one, ?_, ?_⟩
  · exact isRectangularUpperTriangular_zero
  · simp

/-- Base UTV witness for matrices with an empty row type. -/
theorem base_utv_empty_rows
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [IsEmpty m]
    (A : Matrix m n ℂ) :
    HasUTV A := by
  rw [matrix_eq_zero_of_isEmpty_rows A]
  exact hasUTV_zero

/-- Base UTV witness for matrices with an empty column type. -/
theorem base_utv_empty_cols
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [IsEmpty n]
    (A : Matrix m n ℂ) :
    HasUTV A := by
  rw [matrix_eq_zero_of_isEmpty_cols A]
  exact hasUTV_zero

/-- Transport a UTV witness across a two-sided unitary transformation. -/
theorem utv_transport_twoSidedUnitary
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
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

section BlockLift

variable {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Lift a tail UTV witness through a block diagonal head-tail matrix. -/
theorem utv_blockDiag_unit
    (σ : ℝ) (hσ : 0 ≤ σ) {A : Matrix m n ℂ} (hA : HasUTV A) :
    HasUTV
      (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 A :
        Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ) := by
  rcases hA with ⟨U, V, T, hU, hV, hT, hEq⟩
  let Ublk : Matrix (Unit ⊕ m) (Unit ⊕ m) ℂ :=
    fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U
  let Vblk : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
    fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 V
  let Tblk : Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ :=
    fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 T
  refine ⟨Ublk, Vblk, Tblk, ?_, ?_, ?_, ?_⟩
  · exact isUnitaryMatrix_blockDiag_one hU
  · exact isUnitaryMatrix_blockDiag_one hV
  · exact isRectangularDiagonalNonnegative_blockDiag_unit σ hσ hT
  · calc
      (fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 A :
          Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ)
          = fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 (U * T * Vᴴ) := by
        rw [hEq]
      _ = Ublk * Tblk * Vblkᴴ := by
        simp [Ublk, Vblk, Tblk, Matrix.fromBlocks_conjTranspose, fromBlocks_multiply,
          Matrix.mul_assoc]

theorem utv_of_blockReady_reindex
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) ℂ)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (h₁₁ : A.toBlocks₁₁ = (fun _ _ : Unit => (σ : ℂ)))
    (h₁₂ : A.toBlocks₁₂ = 0) (h₂₁ : A.toBlocks₂₁ = 0)
    (hTail : HasUTV A.toBlocks₂₂) :
    HasUTV A := by
  have hA :
      A =
        fromBlocks (fun _ _ : Unit => (σ : ℂ)) 0 0 A.toBlocks₂₂ := by
    exact (Matrix.ext_iff_blocks).2 ⟨h₁₁, h₁₂, h₂₁, rfl⟩
  rw [hA]
  exact utv_blockDiag_unit σ hσ hTail

theorem utv_reindex
    {m' n' : Type u} [Fintype m'] [DecidableEq m'] [Fintype n'] [DecidableEq n']
    (em : m ≃ m') (en : n ≃ n') {A : Matrix m n ℂ} (hA : HasUTV A) :
    HasUTV (Matrix.reindex em en A) := by
  rcases hA with ⟨U, V, T, hU, hV, hT, hEq⟩
  refine ⟨Matrix.reindex em em U, Matrix.reindex en en V, Matrix.reindex em en T,
    isUnitaryMatrix_reindex em hU, isUnitaryMatrix_reindex en hV, ?_, ?_⟩
  · rcases hT with ⟨data⟩
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
