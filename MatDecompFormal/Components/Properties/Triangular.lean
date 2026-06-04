import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Sum.Order


namespace MatDecompFormal.Components.Properties

open Matrix

/-!
# Triangular Matrix Properties

This file defines the properties of upper triangular, lower triangular, and
unit lower triangular matrices.

Design notes:

* The definitions depend only on `LinearOrder` on the index type.
* `IsUpperTriangular` uses `Matrix.BlockTriangular` with the identity map as the blocking function
  `fun i ↦ i`, so the condition is equivalent to: if `j < i`, then `A i j = 0`.
-/

section Triangular

variable {ι R : Type*} [Zero R]  --[LinearOrder ι]

/--
`IsUpperTriangular A`: matrix `A` is upper triangular under the given index order.

Formally, it is defined as `BlockTriangular` with respect to the identity map `id : ι → ι`:
if `j < i`, then `A i j = 0`.
-/
def IsUpperTriangular [LT ι] (A : Matrix ι ι R) : Prop :=
  BlockTriangular A (fun i : ι => i)

/--
`IsLowerTriangular A`: matrix `A` is lower triangular if and only if `Aᵀ` is upper triangular.
-/
def IsLowerTriangular [LT ι] (A : Matrix ι ι R) : Prop :=
  IsUpperTriangular Aᵀ

/--
`IsUnitLowerTriangular A`: `A` is a unit lower triangular matrix,
that is, lower triangular with all diagonal entries equal to `1`.
-/
def IsUnitLowerTriangular [LT ι] [One R] (A : Matrix ι ι R) : Prop :=
  IsLowerTriangular A ∧ A.diag = 1

-- ==================================================================
-- Basic Properties
-- ==================================================================

variable [One R] [Preorder ι]

/-- The identity matrix `1` is upper triangular. -/
lemma isUpperTriangular_one [DecidableEq ι] : IsUpperTriangular (1 : Matrix ι ι R) := by
  -- The identity matrix is BlockTriangular for any blocking function.
  dsimp [IsUpperTriangular]
  simpa using
    (blockTriangular_one (b := fun i : ι => i))

/-- The identity matrix `1` is lower triangular. -/
lemma isLowerTriangular_one [DecidableEq ι] : IsLowerTriangular (1 : Matrix ι ι R) := by
  dsimp [IsLowerTriangular]
  -- `(1 : Matrix _ _ _)ᵀ = 1`
  simpa [Matrix.transpose_one] using
    isUpperTriangular_one

/-- The identity matrix `1` is unit lower triangular. -/
lemma isUnitLowerTriangular_one [DecidableEq ι] : IsUnitLowerTriangular (1 : Matrix ι ι R) := by
  constructor
  · exact isLowerTriangular_one
  · -- All diagonal entries are 1
    simp [Matrix.diag_one]

/--
Any square matrix indexed by a subsingleton type, a type with only one element, is upper triangular.
This result is vacuously true because the condition `j < i` can never be satisfied.
-/
lemma isUpperTriangular_of_subsingleton {ι R} [Zero R] [Preorder ι] [Subsingleton ι]
    (A : Matrix ι ι R) : IsUpperTriangular A := by
  dsimp [IsUpperTriangular, BlockTriangular]
  intro i j hij
  -- Because ι is a subsingleton type, any two elements are equal.
  have : i = j := Subsingleton.elim i j
  -- Substitute i = j into hij
  rw [this] at hij
  -- hij is now j < j, contradicting irreflexivity of less-than.
  exfalso; exact lt_irrefl j hij

/--
Any square matrix indexed by a subsingleton type is also lower triangular.
-/
lemma isLowerTriangular_of_subsingleton {ι R} [Zero R] [Preorder ι] [Subsingleton ι]
    (A : Matrix ι ι R) : IsLowerTriangular A := by
  -- Proof: A is lower triangular iff Aᵀ is upper triangular.
  -- Aᵀ is also indexed by a Subsingleton type, so it is upper triangular.
  dsimp [IsLowerTriangular]
  exact isUpperTriangular_of_subsingleton Aᵀ

end Triangular

end MatDecompFormal.Components.Properties
