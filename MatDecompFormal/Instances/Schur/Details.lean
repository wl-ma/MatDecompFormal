import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Framework.UniverseDecompositionSquareSubtype
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Components.Properties
open MatDecompFormal.Framework

/-!
# Schur Triangularization Details

This file contains the matrix-level Schur target predicate and base cases. The
recursive framework route is assembled in `Existence.lean`.
-/

variable {K ι : Type*}

/-- Matrix-level invertibility predicate used by the Schur target. -/
abbrev InvertibleMatrix [Ring K] [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι K) : Prop :=
  IsUnit P

/-- Schur upper-triangularization target for a concrete finite square matrix. -/
def HasSchur [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ P : Matrix ι ι K, ∃ T : Matrix ι ι K,
    InvertibleMatrix P ∧ IsUpperTriangular T ∧ A = P * T * P⁻¹

/-- Universe-level predicate used by the square-subtype induction framework. -/
def Schur_P [Field K] (x : SquareUniverse K) : Prop :=
  HasSchur x.A

def Schur_P_sub [Field K] (x_sub : PosSquareUniverse K) : Prop :=
  Schur_P (x_sub : SquareUniverse K)

@[simp] theorem schur_P_compat [Field K] (x_sub : PosSquareUniverse K) :
    Schur_P_sub x_sub ↔ Schur_P (x_sub : SquareUniverse K) :=
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

end MatDecompFormal.Instances
