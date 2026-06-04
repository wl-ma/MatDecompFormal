import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Swap
import MatDecompFormal.Abstractions.MatrixProperty

namespace MatDecompFormal.Components.Properties

open Matrix
open MatDecompFormal.Abstractions

/-!
# Permutation Matrix Property

This file defines the `IsPermutation` property and proves its basic properties.
A matrix is a permutation matrix if it is equal to the matrix representation of some `Equiv.Perm`.

Design notes:
- The core property only depends on `[Fintype ι]` and `[DecidableEq ι]` for maximum generality
  and to avoid typeclass instance conflicts.
-/

section IsPermutation

variable {ι R : Type*} [Zero R] [One R] [DecidableEq ι]

/--
`IsPermutation A` is a predicate determining whether the matrix `A` is a permutation matrix.
-/
def IsPermutation (A : Matrix ι ι R) : Prop :=
  ∃ (σ : Equiv.Perm ι), A = (Equiv.toPEquiv σ).toMatrix

/--
A row/column swap matrix constructed from `Equiv.swap` is a permutation matrix.
-/
lemma isPermutation_swap (i j : ι) : IsPermutation (swap R i j) := by
  dsimp [IsPermutation]
  use (Equiv.swap i j)
  -- `swap R i j` is definitionally equal to `(Equiv.toPEquiv (Equiv.swap i j)).toMatrix`
  -- in Mathlib.LinearAlgebra.Matrix.Swap
  rfl

end IsPermutation

section Multiplication

variable {ι R : Type*} [Semiring R] [DecidableEq ι]

/--
The set of permutation matrices is closed under matrix multiplication.
The statement only needs `Fintype`, which keeps the interface generic and avoids
unnecessary instance conflicts.
-/
@[simp]
lemma isPermutation_mul {A B : Matrix ι ι R} [Fintype ι]
    (hA : IsPermutation A) (hB : IsPermutation B) : IsPermutation (A * B) := by
  rcases hA with ⟨σA, rfl⟩
  rcases hB with ⟨σB, rfl⟩
  dsimp [IsPermutation]
  -- The permutation corresponding to A * B is σB * σA (note the order).
  refine ⟨σB * σA, ?_⟩
  have hmul :
      ((Equiv.toPEquiv σA).toMatrix : Matrix ι ι R) *
          (Equiv.toPEquiv σB).toMatrix =
        (Equiv.toPEquiv (σA.trans σB)).toMatrix := by
    simpa [Equiv.toPEquiv_trans] using
      (PEquiv.toMatrix_trans (Equiv.toPEquiv σA) (Equiv.toPEquiv σB)).symm
  have hcomp : σA.trans σB = σB * σA := by
    ext i
    simp [Equiv.trans_apply, Equiv.Perm.mul_def]
  simpa [hcomp] using hmul


end Multiplication

end MatDecompFormal.Components.Properties
