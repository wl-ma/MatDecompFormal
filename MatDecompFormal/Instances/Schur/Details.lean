import MatDecompFormal.Instances.Normal.Details
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Framework.UniverseDecompositionSquareSubtype
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Components.Properties
open MatDecompFormal.Framework

/-!
# Algebraic Schur Triangularization Details

This file contains the matrix-level targets and base cases for Schur-style
triangularization.  The generic `HasSchur` target is algebraic: it uses an
arbitrary invertible similarity over an algebraically closed field.  The
complex unitary Schur target is exposed separately as `HasUnitarySchur`.
-/

variable {K ι : Type*}

/-- Matrix-level invertibility predicate used by the Schur target. -/
abbrev InvertibleMatrix [Ring K] [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι K) : Prop :=
  IsUnit P

/--
Algebraic Schur upper-triangularization target for a concrete finite square
matrix.

The similarity matrix is only required to be invertible.  This is intentionally
weaker than the usual complex unitary Schur decomposition; use
`HasUnitarySchur` for the unitary target.
-/
def HasSchur [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ P : Matrix ι ι K, ∃ T : Matrix ι ι K,
    InvertibleMatrix P ∧ IsUpperTriangular T ∧ A = P * T * P⁻¹

/--
Complex unitary Schur target.

This is deliberately separate from `HasSchur`: the witness `Q` is unitary and
the inverse is written as the conjugate transpose `Qᴴ`.
-/
def HasUnitarySchur [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) : Prop :=
  ∃ Q : Matrix ι ι ℂ, ∃ T : Matrix ι ι ℂ,
    IsUnitaryMatrix Q ∧ IsUpperTriangular T ∧ A = Q * T * Qᴴ

/-- A unitary matrix is invertible, with inverse given by its conjugate transpose. -/
lemma invertibleMatrix_of_isUnitaryMatrix
    [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℂ}
    (hQ : IsUnitaryMatrix Q) :
    InvertibleMatrix Q := by
  exact ⟨⟨Q, Qᴴ, hQ.2, hQ.1⟩, rfl⟩

/-- The unitary Schur target implies the algebraic invertible-similarity target. -/
theorem hasSchur_of_hasUnitarySchur
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ} (hA : HasUnitarySchur A) :
    HasSchur A := by
  rcases hA with ⟨Q, T, hQ, hT, hEq⟩
  refine ⟨Q, T, invertibleMatrix_of_isUnitaryMatrix hQ, hT, ?_⟩
  have hQinv : Q⁻¹ = Qᴴ := by
    apply Matrix.inv_eq_right_inv
    exact hQ.2
  simpa [hQinv] using hEq

/-- Universe-level predicate used by the square-subtype induction framework. -/
def Schur_P [Field K] (x : SquareUniverse K) : Prop :=
  HasSchur x.A

def Schur_P_sub [Field K] (x_sub : PosSquareUniverse K) : Prop :=
  Schur_P (x_sub : SquareUniverse K)

@[simp] theorem schur_P_compat [Field K] (x_sub : PosSquareUniverse K) :
    Schur_P_sub x_sub ↔ Schur_P (x_sub : SquareUniverse K) :=
  Iff.rfl

/-- Universe-level predicate for the complex unitary Schur target. -/
def UnitarySchur_P (x : SquareUniverse ℂ) : Prop :=
  HasUnitarySchur x.A

def UnitarySchur_P_sub (x_sub : PosSquareUniverse ℂ) : Prop :=
  UnitarySchur_P (x_sub : SquareUniverse ℂ)

@[simp] theorem unitarySchur_P_compat (x_sub : PosSquareUniverse ℂ) :
    UnitarySchur_P_sub x_sub ↔ UnitarySchur_P (x_sub : SquareUniverse ℂ) :=
  Iff.rfl

lemma invertibleMatrix_one [Field K] [Fintype ι] [DecidableEq ι] :
    InvertibleMatrix (1 : Matrix ι ι K) := by
  exact isUnit_one

/-- Any square matrix on a subsingleton index type has a trivial Schur witness. -/
lemma base_schur_subsingleton
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Subsingleton ι]
    (A : Matrix ι ι K) :
    HasSchur A := by
  refine ⟨1, A, invertibleMatrix_one, isUpperTriangular_of_subsingleton A, ?_⟩
  simp

/-- Base case for zero-dimensional square universes. -/
lemma base_schur_zero_dim_sq [Field K]
    {x : SquareUniverse K} (h_zero : Fintype.card x.ι = 0) :
    HasSchur x.A := by
  classical
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp h_zero
  letI : Subsingleton x.ι := by infer_instance
  exact base_schur_subsingleton x.A

/-- Any square matrix on a subsingleton index type has a trivial unitary Schur witness. -/
lemma base_unitarySchur_subsingleton
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Subsingleton ι]
    (A : Matrix ι ι ℂ) :
    HasUnitarySchur A := by
  refine ⟨1, A, isUnitaryMatrix_one, isUpperTriangular_of_subsingleton A, ?_⟩
  simp

/-- Base case for zero-dimensional square universes in the unitary Schur target. -/
lemma base_unitarySchur_zero_dim_sq
    {x : SquareUniverse ℂ} (h_zero : Fintype.card x.ι = 0) :
    HasUnitarySchur x.A := by
  classical
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp h_zero
  letI : Subsingleton x.ι := by infer_instance
  exact base_unitarySchur_subsingleton x.A

end MatDecompFormal.Instances
