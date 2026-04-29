import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

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
`MatrixGroup P` is a typeclass asserting that `n × n` matrices satisfying property `P`
form a group under matrix multiplication.
-/
class MatrixGroup {n R} [CommRing R] (P : Matrix (Fin n) (Fin n) R → Prop) where
  /--
  Multiplicative closure: multiplying two matrices satisfying property P still
  yields a matrix satisfying P.
  -/
  mul_closed : ∀ {A B}, P A → P B → P (A * B)
  /-- The identity element belongs to this set. -/
  one_mem : P 1
  /-- Inverse closure: the inverse of a matrix satisfying property P also satisfies P. -/
  inv_closed : ∀ {A}, P A → P A⁻¹
  /-- Invertibility: matrices satisfying property P are invertible, i.e. units in the ring. -/
  invertible : ∀ {A}, P A → IsUnit A

end MatDecompFormal.Abstractions
