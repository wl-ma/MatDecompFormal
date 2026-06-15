import Mathlib.Data.Matrix.Basic

namespace MatDecompFormal.Components.Properties

open Matrix

/-!
# Positive diagonal entries

Shared predicate for decompositions that require strict positivity on square
matrix diagonal entries.
-/

variable {ι R : Type*}

/-- Strict positivity of the diagonal entries of a square matrix. -/
def PositiveDiagonal [Zero R] [LT R] (A : Matrix ι ι R) : Prop :=
  ∀ i, 0 < A i i

/-- Positive diagonal entries are preserved by reindexing. -/
lemma positiveDiagonal_reindex_equiv
    {α β R : Type*} [Zero R] [LT R]
    (e : α ≃ β) {D : Matrix α α R} (hD : PositiveDiagonal D) :
    PositiveDiagonal (Matrix.reindex e e D) := by
  intro i
  simpa [PositiveDiagonal, Matrix.reindex_apply] using hD (e.symm i)

end MatDecompFormal.Components.Properties
