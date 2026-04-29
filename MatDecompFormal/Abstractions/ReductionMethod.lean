import Mathlib.Algebra.Ring.Defs
import Mathlib.LinearAlgebra.Matrix.Defs

namespace MatDecompFormal.Abstractions

/-!
# Reduction Method

This file defines `ReductionMethod`, which packages the purely algebraic part of
problem reduction on `Fin m × Fin n` matrices.
-/

/--
`ReductionMethod` (Fin m n version)

*   `m`, `n`, `R`: the dimensions of the original matrix and the ring type.
*   `slice_m`, `slice_n`: the dimensions of the subproblem, or slice, matrix.
*   `IsSliceable`: describes when a `Matrix (Fin m) (Fin n) R` can be sliced.
*   `slice`: extracts a subproblem of type
    `Matrix (Fin slice_m) (Fin slice_n) R` from a sliceable matrix.
*   `reconstruct`: reconstructs a full matrix from the original matrix context
    and a solution to the submatrix.
*   `reconstruct_slice_eq`: proves the algebraic consistency of `reconstruct` and `slice`.
-/
structure ReductionMethod (m n slice_m slice_n : ℕ) (R : Type*) [CommRing R] where
  /-- A predicate determining whether a matrix is in a normal form that can be sliced. -/
  IsSliceable : Matrix (Fin m) (Fin n) R → Prop

  /-- The “slice” operator, extracting a smaller subproblem from a sliceable matrix. -/
  slice : (A : Matrix (Fin m) (Fin n) R) → (hA : IsSliceable A) →
    Matrix (Fin slice_m) (Fin slice_n) R

  /--
  The reconstruct function assembles a full matrix from the original matrix
  context and a submatrix solution.
  -/
  reconstruct : (A : Matrix (Fin m) (Fin n) R) → (hA : IsSliceable A) →
                (slice_sol : Matrix (Fin slice_m) (Fin slice_n) R) → Matrix (Fin m) (Fin n) R

  /--
  Correctness of reconstruction: reconstructing with the original slice yields
  the original matrix.
  -/
  reconstruct_slice_eq : ∀ (A : Matrix (Fin m) (Fin n) R) (hA : IsSliceable A),
                           reconstruct A hA (slice A hA) = A

end MatDecompFormal.Abstractions
