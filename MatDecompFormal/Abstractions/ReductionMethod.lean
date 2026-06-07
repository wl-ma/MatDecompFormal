import Mathlib.LinearAlgebra.Matrix.Defs

namespace MatDecompFormal.Abstractions

/-!
# Reduction Method

This file defines `ReductionMethod`, which packages the purely algebraic part of
problem reduction on matrices indexed by general row and column types.
-/

/--
`ReductionMethod`

*   `ι`, `κ`, `R`: the index types of the original matrix and the ring type.
*   `ιs`, `κs`: the index types of the sliced subproblem matrix.
*   `IsSliceable`: describes when a `Matrix ι κ R` can be sliced.
*   `slice`: extracts a subproblem of type `Matrix ιs κs R` from a sliceable matrix.
*   `reconstruct`: reconstructs a full matrix from the original matrix context
    and a solution to the submatrix.
*   `reconstruct_slice_eq`: proves the algebraic consistency of `reconstruct` and `slice`.
-/
structure ReductionMethod (ι κ ιs κs : Type*) (R : Type*) where
  /-- A predicate determining whether a matrix is in a normal form that can be sliced. -/
  IsSliceable : Matrix ι κ R → Prop

  /-- The “slice” operator, extracting a smaller subproblem from a sliceable matrix. -/
  slice : (A : Matrix ι κ R) → (hA : IsSliceable A) → Matrix ιs κs R

  /--
  The reconstruct function assembles a full matrix from the original matrix
  context and a submatrix solution.
  -/
  reconstruct : (A : Matrix ι κ R) → (hA : IsSliceable A) →
                (slice_sol : Matrix ιs κs R) → Matrix ι κ R

  /--
  Correctness of reconstruction: reconstructing with the original slice yields
  the original matrix.
  -/
  reconstruct_slice_eq : ∀ (A : Matrix ι κ R) (hA : IsSliceable A),
                           reconstruct A hA (slice A hA) = A

end MatDecompFormal.Abstractions
