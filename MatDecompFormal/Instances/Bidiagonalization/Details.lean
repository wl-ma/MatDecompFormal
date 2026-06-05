import MatDecompFormal.Instances.Hessenberg.Boundary
import MatDecompFormal.Instances.Normal.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open Sum.Lex

/-!
# Bidiagonalization Details

This file contains the target predicate, zero-pattern facts, and algebraic
transport/lift lemmas used by the rectangular descent-template implementation
of unitary bidiagonalization.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n : Type u}

/-- Upper bidiagonal zero pattern for arbitrary finite ordered row/column types. -/
def IsUpperBidiagonal
    {m n R : Type*} [Fintype m] [LinearOrder m]
    [Fintype n] [LinearOrder n] [Zero R]
    (B : Matrix m n R) : Prop :=
  ∀ i j,
    finiteOrderRank n j < finiteOrderRank m i ∨
      finiteOrderRank m i + 1 < finiteOrderRank n j →
    B i j = 0

/-- Unitary two-sided upper-bidiagonalization target. -/
def HasUnitaryBidiagonalization
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) : Prop :=
  ∃ U : Matrix m m 𝕜, ∃ V : Matrix n n 𝕜, ∃ B : Matrix m n 𝕜,
    IsUnitaryMatrix U ∧
    IsUnitaryMatrix V ∧
    IsUpperBidiagonal B ∧
    A = U * B * Vᴴ

/-- Universe-level bidiagonalization predicate used by the rectangular driver. -/
def Bidiagonalization_P (𝕜 : Type*) [RCLike 𝕜] (x : RectUniverse 𝕜) : Prop :=
  HasUnitaryBidiagonalization x.A

def Bidiagonalization_P_sub (𝕜 : Type*) [RCLike 𝕜] (x_sub : PosRectUniverse 𝕜) :
    Prop :=
  Bidiagonalization_P 𝕜 (x_sub : RectUniverse 𝕜)

@[simp] theorem bidiagonalization_P_compat (𝕜 : Type*) [RCLike 𝕜]
    (x_sub : PosRectUniverse 𝕜) :
    Bidiagonalization_P_sub 𝕜 x_sub ↔
      Bidiagonalization_P 𝕜 (x_sub : RectUniverse 𝕜) :=
  Iff.rfl

lemma isUpperBidiagonal_zero
    [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n] :
    IsUpperBidiagonal (0 : Matrix m n 𝕜) := by
  intro i j hij
  simp

/-- Zero matrices have a trivial unitary bidiagonalization. -/
theorem hasUnitaryBidiagonalization_zero
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] :
    HasUnitaryBidiagonalization (0 : Matrix m n 𝕜) := by
  refine ⟨1, 1, 0, isUnitaryMatrix_one, isUnitaryMatrix_one, ?_, ?_⟩
  · exact isUpperBidiagonal_zero
  · simp

lemma bidiagonal_matrix_eq_zero_of_isEmpty_rows
    [Fintype m] [Fintype n] [IsEmpty m] (A : Matrix m n 𝕜) :
    A = 0 := by
  ext i
  cases IsEmpty.false i

lemma bidiagonal_matrix_eq_zero_of_isEmpty_cols
    [Fintype m] [Fintype n] [IsEmpty n] (A : Matrix m n 𝕜) :
    A = 0 := by
  ext i j
  cases IsEmpty.false j

/-- Base witness for matrices with an empty row type. -/
theorem base_bidiagonalization_empty_rows
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [IsEmpty m]
    (A : Matrix m n 𝕜) :
    HasUnitaryBidiagonalization A := by
  rw [bidiagonal_matrix_eq_zero_of_isEmpty_rows A]
  exact hasUnitaryBidiagonalization_zero

/-- Base witness for matrices with an empty column type. -/
theorem base_bidiagonalization_empty_cols
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [IsEmpty n]
    (A : Matrix m n 𝕜) :
    HasUnitaryBidiagonalization A := by
  rw [bidiagonal_matrix_eq_zero_of_isEmpty_cols A]
  exact hasUnitaryBidiagonalization_zero

/-- Transport a bidiagonalization witness across a two-sided unitary transform. -/
theorem bidiagonalization_transport_equivalence
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (U : Matrix m m 𝕜) (V : Matrix n n 𝕜)
    (A B : Matrix m n 𝕜)
    (hU : IsUnitaryMatrix U) (hV : IsUnitaryMatrix V)
    (hB : B = Uᴴ * A * V)
    (hBi : HasUnitaryBidiagonalization B) :
    HasUnitaryBidiagonalization A := by
  rcases hBi with ⟨UB, VB, C, hUB, hVB, hC, hEqB⟩
  refine ⟨U * UB, V * VB, C, isUnitaryMatrix_mul hU hUB,
    isUnitaryMatrix_mul hV hVB, hC, ?_⟩
  calc
    A = (U * Uᴴ) * A * (V * Vᴴ) := by
      simp [hU.2, hV.2]
    _ = U * (Uᴴ * A * V) * Vᴴ := by
      simp [Matrix.mul_assoc]
    _ = U * B * Vᴴ := by
      rw [← hB]
    _ = U * (UB * C * VBᴴ) * Vᴴ := by
      rw [hEqB]
    _ = (U * UB) * C * (V * VB)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp [Matrix.mul_assoc]

section Reindex

variable {m' n' : Type u}
variable [Fintype m] [DecidableEq m] [LinearOrder m]
variable [Fintype n] [DecidableEq n] [LinearOrder n]
variable [Fintype m'] [DecidableEq m'] [LinearOrder m']
variable [Fintype n'] [DecidableEq n'] [LinearOrder n']

theorem isUpperBidiagonal_reindex_strictMono
    (em : m ≃ m') (en : n ≃ n') (hem : StrictMono em) (hen : StrictMono en)
    {B : Matrix m n 𝕜} (hB : IsUpperBidiagonal B) :
    IsUpperBidiagonal (Matrix.reindex em en B) := by
  intro i j hij
  have hij' :
      finiteOrderRank n (en.symm j) < finiteOrderRank m (em.symm i) ∨
        finiteOrderRank m (em.symm i) + 1 < finiteOrderRank n (en.symm j) := by
    simpa [finiteOrderRank_equiv_symm em hem i,
      finiteOrderRank_equiv_symm en hen j] using hij
  simpa [Matrix.reindex_apply] using hB (em.symm i) (en.symm j) hij'

theorem bidiagonalization_reindex_strictMono
    (em : m ≃ m') (en : n ≃ n') (hem : StrictMono em) (hen : StrictMono en)
    {A : Matrix m n 𝕜} (hA : HasUnitaryBidiagonalization A) :
    HasUnitaryBidiagonalization (Matrix.reindex em en A) := by
  rcases hA with ⟨U, V, B, hU, hV, hB, hEq⟩
  refine ⟨Matrix.reindex em em U, Matrix.reindex en en V, Matrix.reindex em en B,
    isUnitaryMatrix_reindex em hU, isUnitaryMatrix_reindex en hV, ?_, ?_⟩
  · exact isUpperBidiagonal_reindex_strictMono em en hem hen hB
  · have hEq' := congrArg (Matrix.reindex em en) hEq
    simpa [Matrix.conjTranspose_reindex, Matrix.submatrix_mul_equiv, Matrix.mul_assoc] using hEq'

end Reindex

section BlockLift

variable {m n : Type u}
variable [Fintype m] [DecidableEq m] [LinearOrder m]
variable [Fintype n] [DecidableEq n] [LinearOrder n]

/-- A one-head block matrix is upper bidiagonal from a ready boundary and tail shape. -/
theorem isUpperBidiagonal_fromBlocks_ready
    (B₁₁ : Matrix Unit Unit 𝕜) (B₁₂ : Matrix Unit n 𝕜)
    (B₂₁ : Matrix m Unit 𝕜) (B₂₂ : Matrix m n 𝕜)
    (hcol : ∀ i : m, B₂₁ i () = 0)
    (hrow : ∀ j : n, B₁₂ () j = 0)
    (hTail : IsUpperBidiagonal B₂₂) :
    IsUpperBidiagonal
      (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
        (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)) := by
  intro i j hij
  cases hi : ofLex i with
  | inl iu =>
      cases iu
      have i_eq : i = (Sum.inlₗ () : Unit ⊕ₗ m) := by
        rw [← toLex_ofLex i, hi]
      subst i
      cases hj : ofLex j with
      | inl ju =>
          cases ju
          have j_eq : j = (Sum.inlₗ () : Unit ⊕ₗ n) := by
            rw [← toLex_ofLex j, hj]
          subst j
          have hbad : 0 < 0 ∨ 1 < 0 := by
            simpa [finiteOrderRank_sumLex_inl_unit] using hij
          rcases hbad with hbad | hbad
          · exact (Nat.lt_irrefl 0 hbad).elim
          · exact (Nat.not_lt_zero 1 hbad).elim
      | inr jj =>
          have j_eq : j = (Sum.inrₗ jj : Unit ⊕ₗ n) := by
            rw [← toLex_ofLex j, hj]
          subst j
          simpa [Matrix.reindex_apply, sumToLexEquiv] using hrow jj
  | inr ii =>
      have i_eq : i = (Sum.inrₗ ii : Unit ⊕ₗ m) := by
        rw [← toLex_ofLex i, hi]
      subst i
      cases hj : ofLex j with
      | inl ju =>
          cases ju
          rw [← toLex_ofLex j, hj]
          simpa [Matrix.reindex_apply, sumToLexEquiv] using hcol ii
      | inr jj =>
          have j_eq : j = (Sum.inrₗ jj : Unit ⊕ₗ n) := by
            rw [← toLex_ofLex j, hj]
          subst j
          have hijTail :
              finiteOrderRank n jj < finiteOrderRank m ii ∨
                finiteOrderRank m ii + 1 < finiteOrderRank n jj := by
            rw [finiteOrderRank_sumLex_inr, finiteOrderRank_sumLex_inr] at hij
            omega
          simpa [Matrix.reindex_apply, sumToLexEquiv] using hTail ii jj hijTail

/-- Lift a tail bidiagonalization through a ready rectangular head-tail block. -/
theorem bidiagonalization_of_ready_blocks
    (B₁₁ : Matrix Unit Unit 𝕜) (B₁₂ : Matrix Unit n 𝕜)
    (B₂₁ : Matrix m Unit 𝕜) (B₂₂ : Matrix m n 𝕜)
    (hcol : ∀ i : m, B₂₁ i () = 0)
    (hrow : ∀ j : n, B₁₂ () j = 0)
    (hTail : HasUnitaryBidiagonalization B₂₂) :
    HasUnitaryBidiagonalization
      (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
        (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)) := by
  rcases hTail with ⟨U, V, C, hU, hV, hC, hEq⟩
  let Ublk : Matrix (Unit ⊕ₗ m) (Unit ⊕ₗ m) 𝕜 :=
    fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 U
  let Vblk : Matrix (Unit ⊕ₗ n) (Unit ⊕ₗ n) 𝕜 :=
    fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 V
  let Cparent : Matrix (Unit ⊕ₗ m) (Unit ⊕ₗ n) 𝕜 :=
    Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
      (fromBlocks B₁₁ 0 0 C : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)
  refine ⟨Ublk, Vblk, Cparent, ?_, ?_, ?_, ?_⟩
  · exact isUnitaryMatrix_blockDiag_one hU
  · exact isUnitaryMatrix_blockDiag_one hV
  · exact isUpperBidiagonal_fromBlocks_ready B₁₁ 0 0 C (by simp) (by simp) hC
  · calc
      Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
          (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)
          = Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
              (fromBlocks B₁₁ 0 0 B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) := by
            congr 1
            ext i j <;> cases i <;> cases j <;> simp [hrow, hcol]
      _ = Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
              (fromBlocks B₁₁ 0 0 (U * C * Vᴴ) :
                Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) := by
            rw [hEq]
      _ = Ublk * Cparent * Vblkᴴ := by
            have hraw :
                (fromBlocks B₁₁ 0 0 (U * C * Vᴴ) :
                  Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) =
                    (fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 U :
                      Matrix (Unit ⊕ m) (Unit ⊕ m) 𝕜) *
                      (fromBlocks B₁₁ 0 0 C :
                        Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) *
                      (fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 V :
                        Matrix (Unit ⊕ n) (Unit ⊕ n) 𝕜)ᴴ := by
              ext i j <;> cases i <;> cases j <;>
                simp [Matrix.fromBlocks_conjTranspose, fromBlocks_multiply,
                  Matrix.mul_assoc]
            have hlex := congrArg
              (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)) hraw
            simpa [Ublk, Vblk, Cparent, Matrix.submatrix_mul_equiv,
              Matrix.conjTranspose_reindex, Matrix.mul_assoc] using hlex

end BlockLift

end MatDecompFormal.Instances
