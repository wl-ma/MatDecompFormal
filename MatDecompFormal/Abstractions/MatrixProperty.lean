import Mathlib.Data.Matrix.Basic

namespace MatDecompFormal.Abstractions

open Matrix

/-!
# Abstract Matrix Properties

This file defines the `MatrixGroup` typeclass, used to capture matrix properties that
form groups, such as permutation matrices and orthogonal matrices. The main purpose
of this abstraction is to organize code, unify concepts, and support future generic
lemmas and automation tactics.
-/

/--
`MatrixGroup P` is a typeclass asserting that square matrices satisfying property `P`
form a group under matrix multiplication.
-/
class MatrixGroup {ι R} [Fintype ι] [DecidableEq ι] [Semiring R] (P : Matrix ι ι R → Prop) where
  /--
  Multiplicative closure: multiplying two matrices satisfying property P still
  yields a matrix satisfying P.
  -/
  mul_closed : ∀ {A B}, P A → P B → P (A * B)
  /-- The identity element belongs to this set. -/
  one_mem : P 1
  /-- Inverse closure by witness: every matrix satisfying P has a two-sided inverse satisfying P. -/
  inv_closed : ∀ {A}, P A → ∃ B, P B ∧ A * B = 1 ∧ B * A = 1
  /-- Invertibility: matrices satisfying P are invertible, i.e. units in the matrix monoid. -/
  invertible : ∀ {A}, P A → IsUnit A

end MatDecompFormal.Abstractions
