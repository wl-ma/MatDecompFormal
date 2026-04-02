import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Framework.FinEnum
import Mathlib.Data.Real.Basic

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions

/-!
# Bidiagonalization Core

This file contains a local internal draft for bidiagonalization on rectangular
real matrices. Unlike the existing PLU/QR instances, it does not attempt to
package a full recursive driver; instead, it isolates the internal schema and
the constructor-style existence theorems that a future two-sided rectangular
driver would need to target.
-/

section InternalSurface

variable {m n : ℕ}

/-- Orthogonality predicate used by the internal bidiagonal schema on `ℝ`. -/
def IsOrthogonalMatrix_fin (Q : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  Qᵀ * Q = 1

/--
Internal upper-bidiagonal predicate on rectangular `Fin` matrices.

Entries are allowed to be nonzero only on the main diagonal and the first
superdiagonal.
-/
def IsUpperBidiagonal_fin (B : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, (j.1 < i.1 ∨ i.1 + 1 < j.1) → B i j = 0

/--
Internal canonical bidiagonalization schema on rectangular `Fin`-indexed real
matrices.

We use the two-sided factorization shape `A = U * B * Vᵀ`, because it matches
the natural semantics of bidiagonal reduction and makes the two-sided pressure
on the current framework explicit.
-/
def Bidiag_Schema_fin (m n : ℕ) : DecompositionSchema m n ℝ where
  Factors :=
    Matrix (Fin m) (Fin m) ℝ ×
      Matrix (Fin m) (Fin n) ℝ ×
      Matrix (Fin n) (Fin n) ℝ
  property := fun (f : Matrix (Fin m) (Fin m) ℝ ×
      Matrix (Fin m) (Fin n) ℝ ×
      Matrix (Fin n) (Fin n) ℝ) =>
    let ⟨U, B, V⟩ := f
    IsOrthogonalMatrix_fin (m := m) U ∧
      IsUpperBidiagonal_fin (m := m) (n := n) B ∧
      IsOrthogonalMatrix_fin (m := n) V
  equation := fun A (f : Matrix (Fin m) (Fin m) ℝ ×
      Matrix (Fin m) (Fin n) ℝ ×
      Matrix (Fin n) (Fin n) ℝ) =>
    let ⟨U, B, V⟩ := f
    A = U * B * Vᵀ

/-- Internal bidiagonalization existence proposition on the canonical schema surface. -/
def HasBidiag_fin (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  HasDecomposition (Bidiag_Schema_fin m n) A

end InternalSurface

section Constructors

variable {m n : ℕ}

/-- The identity matrix is orthogonal in the project's internal sense. -/
lemma isOrthogonalMatrix_fin_one :
    IsOrthogonalMatrix_fin (m := m) (1 : Matrix (Fin m) (Fin m) ℝ) := by
  simp [IsOrthogonalMatrix_fin]

/--
Constructor theorem for the internal bidiagonal schema.

This is the local assembly point currently available without changing the
global framework: if the user already has two orthogonal side factors and an
upper-bidiagonal middle factor satisfying the target equation, then the schema
packages them into `HasBidiag_fin`.
-/
theorem mk_hasBidiag_fin_of_data
    (A : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ)
    (hU : IsOrthogonalMatrix_fin (m := m) U)
    (hB : IsUpperBidiagonal_fin (m := m) (n := n) B)
    (hV : IsOrthogonalMatrix_fin (m := n) V)
    (hEq : A = U * B * Vᵀ) :
    HasBidiag_fin (m := m) (n := n) A := by
  exact ⟨⟨U, B, V⟩, ⟨hU, hB, hV⟩, hEq⟩

/--
Any matrix that is already upper bidiagonal admits a trivial bidiagonalization,
using identity matrices for both orthogonal side factors.
-/
theorem mk_hasBidiag_fin_of_upperBidiagonal
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : IsUpperBidiagonal_fin (m := m) (n := n) A) :
    HasBidiag_fin (m := m) (n := n) A := by
  refine mk_hasBidiag_fin_of_data
    (A := A) (U := 1) (B := A) (V := 1)
    (hU := isOrthogonalMatrix_fin_one (m := m))
    (hB := hA)
    (hV := isOrthogonalMatrix_fin_one (m := n))
    ?_
  simp

end Constructors

end MatDecompFormal.Instances
