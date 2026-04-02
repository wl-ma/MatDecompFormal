import MatDecompFormal.Framework.FinEnum
import MatDecompFormal.Instances.Bidiag.Core
import Mathlib.Data.Real.Basic

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework

/-!
# Bidiagonalization Bridge

This file provides the presentation-layer `FinEnum` view of the local
bidiagonalization draft. Because bidiagonality is inherently a relative
row/column position condition, the external predicate is phrased by reindexing
through the canonical `FinEnum` order isomorphisms and reusing the internal
`Fin` predicate.
-/

section ExternalSurface

variable {ι κ : Type*} [FinEnum ι] [FinEnum κ]

/-- Orthogonality predicate on the external presentation layer. -/
def IsOrthogonalMatrix (Q : Matrix ι ι ℝ) : Prop :=
  Qᵀ * Q = 1

/--
External upper-bidiagonal predicate.

The canonical `FinEnum` orders provide the row/column positions used to read
the rectangular band condition.
-/
def IsUpperBidiagonal (B : Matrix ι κ ℝ) : Prop :=
  let eι := orderIsoOfFinEnum ι
  let eκ := orderIsoOfFinEnum κ
  IsUpperBidiagonal_fin
    (m := FinEnum.card ι) (n := FinEnum.card κ)
    (B.reindex eι.toEquiv eκ.toEquiv)

/-- External presentation schema for bidiagonalization on rectangular matrices. -/
def Bidiag_Schema : DecompositionSchema' ι κ ℝ where
  Factors := Matrix ι ι ℝ × Matrix ι κ ℝ × Matrix κ κ ℝ
  property := fun (f : Matrix ι ι ℝ × Matrix ι κ ℝ × Matrix κ κ ℝ) =>
    let ⟨U, B, V⟩ := f
    IsOrthogonalMatrix U ∧ IsUpperBidiagonal B ∧ IsOrthogonalMatrix V
  equation := fun A (f : Matrix ι ι ℝ × Matrix ι κ ℝ × Matrix κ κ ℝ) =>
    let ⟨U, B, V⟩ := f
    A = U * B * Vᵀ

/-- External semantic wrapper for bidiagonalization existence. -/
def HasBidiag (A : Matrix ι κ ℝ) : Prop :=
  HasDecomposition' (Bidiag_Schema (ι := ι) (κ := κ)) A

end ExternalSurface

section ExternalConstructors

variable {ι κ : Type*} [FinEnum ι] [FinEnum κ]

/-- The identity matrix is orthogonal on the external presentation layer. -/
lemma isOrthogonalMatrix_one :
    IsOrthogonalMatrix (ι := ι) (1 : Matrix ι ι ℝ) := by
  simp [IsOrthogonalMatrix]

/--
Constructor theorem for the external bidiagonal schema.
-/
theorem mk_hasBidiag_of_data
    (A : Matrix ι κ ℝ)
    (U : Matrix ι ι ℝ)
    (B : Matrix ι κ ℝ)
    (V : Matrix κ κ ℝ)
    (hU : IsOrthogonalMatrix U)
    (hB : IsUpperBidiagonal B)
    (hV : IsOrthogonalMatrix V)
    (hEq : A = U * B * Vᵀ) :
    HasBidiag (ι := ι) (κ := κ) A := by
  exact ⟨⟨U, B, V⟩, ⟨hU, hB, hV⟩, hEq⟩

/--
Any externally indexed matrix that is already upper bidiagonal admits the
trivial two-sided bidiagonalization.
-/
theorem mk_hasBidiag_of_upperBidiagonal
    (A : Matrix ι κ ℝ)
    (hA : IsUpperBidiagonal (ι := ι) (κ := κ) A) :
    HasBidiag (ι := ι) (κ := κ) A := by
  refine mk_hasBidiag_of_data
    (A := A) (U := 1) (B := A) (V := 1)
    (hU := isOrthogonalMatrix_one (ι := ι))
    (hB := hA)
    (hV := isOrthogonalMatrix_one (ι := κ))
    ?_
  simp

end ExternalConstructors

end MatDecompFormal.Instances
