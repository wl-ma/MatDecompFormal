import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Components.Properties.PositiveDiagonal
import MatDecompFormal.Components.Properties.Triangular
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties

open scoped ComplexOrder

/-!
# Cholesky schema and diagonal square-root helpers

This file contains the public Cholesky schema and the algebraic helper used to
convert an LDL witness into a Cholesky witness over the real `RCLike` setting
used by this project.
-/

section Presentation

variable {ι R : Type*}

/--
Standard Cholesky schema on finite square matrices.

Equation form: `A = C * Cᵀ`, where `C` is lower triangular with positive
diagonal entries.
-/
def Cholesky_Schema [Fintype ι] [LinearOrder ι] [Semiring R] [PartialOrder R] :
    DecompositionSchema ι ι R where
  Factors := Matrix ι ι R
  property := fun C => IsLowerTriangular C ∧ PositiveDiagonal C
  equation := fun A C => A = C * Cᵀ

/-- Existence proposition for the standard Cholesky schema. -/
def HasCholesky [Fintype ι] [LinearOrder ι] [Semiring R] [PartialOrder R]
    (A : Matrix ι ι R) : Prop :=
  HasDecomposition Cholesky_Schema A

/-- Diagonal matrix whose diagonal entries are square roots of the real parts of `D`. -/
noncomputable def choleskySqrtDiagonal
    [DecidableEq ι] {R : Type*} [RCLike R]
    (D : Matrix ι ι R) : Matrix ι ι R :=
  Matrix.diagonal fun i => ((Real.sqrt (RCLike.re (D i i)) : ℝ) : R)

/-- A positive `RCLike` scalar is the square of the embedded square root of its real part. -/
lemma rclike_sqrt_mul_self_of_pos
    {R : Type*} [RCLike R] {x : R} (hx : 0 < x) :
    ((Real.sqrt (RCLike.re x) : ℝ) : R) *
        ((Real.sqrt (RCLike.re x) : ℝ) : R) = x := by
  rcases RCLike.pos_iff.mp hx with ⟨hre, him⟩
  apply RCLike.ext
  · rw [← RCLike.ofReal_mul]
    simp [Real.mul_self_sqrt (le_of_lt hre)]
  · rw [← RCLike.ofReal_mul]
    simp [him]

/-- The embedded square root of the real part of a positive `RCLike` scalar is positive. -/
lemma rclike_ofReal_sqrt_pos_of_pos
    {R : Type*} [RCLike R] {x : R} (hx : 0 < x) :
    0 < ((Real.sqrt (RCLike.re x) : ℝ) : R) := by
  rcases RCLike.pos_iff.mp hx with ⟨hre, _him⟩
  exact RCLike.ofReal_pos.2 (Real.sqrt_pos.2 hre)

/--
The square-root diagonal factor squares back to the original positive diagonal
matrix.
-/
lemma choleskySqrtDiagonal_mul_transpose
    [Fintype ι] [DecidableEq ι] {R : Type*} [RCLike R]
    {D : Matrix ι ι R} (hDdiag : D.IsDiag) (hDpos : PositiveDiagonal D) :
    choleskySqrtDiagonal D * (choleskySqrtDiagonal D)ᵀ = D := by
  rw [choleskySqrtDiagonal, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.IsDiag.diagonal_diag hDdiag]
  congr
  funext i
  simpa [Matrix.diag] using rclike_sqrt_mul_self_of_pos (hDpos i)

/-- The square-root diagonal factor is lower triangular. -/
lemma isLowerTriangular_choleskySqrtDiagonal
    [DecidableEq ι] [LinearOrder ι] {R : Type*} [RCLike R]
    (D : Matrix ι ι R) :
    IsLowerTriangular (choleskySqrtDiagonal D) := by
  simpa [choleskySqrtDiagonal] using
    (isLowerTriangular_diagonal
      (d := fun i => ((Real.sqrt (RCLike.re (D i i)) : ℝ) : R)))

/-- Multiplying a unit-lower factor by the square-root diagonal gives positive diagonal entries. -/
lemma positiveDiagonal_mul_choleskySqrtDiagonal
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] {R : Type*} [RCLike R]
    {L D : Matrix ι ι R} (hL : IsUnitLowerTriangular L) (hDpos : PositiveDiagonal D) :
    PositiveDiagonal (L * choleskySqrtDiagonal D) := by
  intro i
  have hLdiag : L i i = 1 := by
    have hdiag := congr_fun hL.2 i
    simpa [Matrix.diag] using hdiag
  calc
    0 < L i i * (((Real.sqrt (RCLike.re (D i i)) : ℝ) : R)) := by
      simpa [hLdiag] using rclike_ofReal_sqrt_pos_of_pos (hDpos i)
    _ = (L * choleskySqrtDiagonal D) i i := by
      simp [choleskySqrtDiagonal]

end Presentation

end MatDecompFormal.Instances
