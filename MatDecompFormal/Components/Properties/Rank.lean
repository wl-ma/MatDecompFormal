import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Basis

namespace MatDecompFormal.Components.Properties

open FinEnum

/-!
# Rank Normal Form Property

This file defines the rank normal form of a matrix and its corresponding property.

1.  **`rankStdBlock`**: a constructor generating a normal-form matrix of a
    given rank `r`. This matrix has an `r × r` identity matrix in the
    upper-left corner, and all other entries are zero.

2.  **`IsRankNormalForm`**: a predicate determining whether a given matrix `A` is equal to
    the normal-form matrix of some rank `r`.

This property is the final `Goal` of decomposition algorithms such as rank factorization
or Smith normal form. It can be used in the `equation` field of `DecompositionSchema`
to describe the target state of a decomposition.
-/

section RankNormalForm

-- Declare the types and typeclass instances shared by all definitions.
variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Zero R] [One R]

/--
`rankStdBlock r` constructs an `ι × κ` rank-normal-form matrix with effective rank `r`.

This matrix is an identity matrix on the block formed by the first `r` row indices and
the first `r` column indices, and is zero elsewhere. The “before/after” ordering of
indices is given by `FinEnum.equiv`.

*   `r`: the rank of the matrix.
-/
def rankStdBlock (r : ℕ) : Matrix ι κ R :=
  fun i j ↦ if  (equiv i).val < r
              ∧ (equiv j).val < r
              ∧ (equiv i).val = (equiv j).val
            then 1
            else 0

/--
`IsRankNormalForm` is a predicate determining whether a matrix `A` is the normal
form of some rank `r`.

A matrix `A` is considered to be in rank normal form if there exists a rank `r`, not
exceeding the matrix dimensions, such that `A` is exactly equal to `rankStdBlock r`.
-/
def IsRankNormalForm (A : Matrix ι κ R) : Prop :=
  ∃ r, r ≤ card ι ∧ r ≤ card κ ∧ A = rankStdBlock r

end RankNormalForm

end MatDecompFormal.Components.Properties
