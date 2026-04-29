import Mathlib

namespace MatDecompFormal.Framework

/-!
# Matrix Universe

This file defines the framework’s universe types, using Σ types to uniformly organize
matrices of different sizes so that cross-dimension reduction and induction can be
expressed in one host type.
-/

/--
`FinRectFamily m n R` wraps a matrix of fixed dimension `m × n`.
-/
structure FinRectFamily (m n : ℕ) (R : Type*) where
  A : Matrix (Fin m) (Fin n) R

/--
`FinRectUniverse R` is the collection of all `m × n` matrices, defined as a Σ type.
An object `x` in the universe is a dependent pair `⟨⟨m, n⟩, fam⟩`, where `fam.A` is the matrix.
-/
abbrev FinRectUniverse (R : Type*) := Σ (dims : ℕ × ℕ), FinRectFamily dims.1 dims.2 R

/--
`PosFinRectUniverse R` is the subtype of matrices with dimensions `m > 0 ∧ n > 0`.
-/
abbrev PosFinRectUniverse (R : Type*) := { x : FinRectUniverse R // x.1.1 > 0 ∧ x.1.2 > 0 }

@[simp] def FinRectUniverse.matrix {R} (x : FinRectUniverse R) : Matrix (Fin x.1.1) (Fin x.1.2) R :=
  x.2.A

/-- `FinSqFamily n R` wraps a square matrix of fixed dimension `n × n`. -/
structure FinSqFamily (n : ℕ) (R : Type*) where
  A : Matrix (Fin n) (Fin n) R

/-- `FinSqUniverse R`: the universe of all `n × n` square matrices, as a Σ type. -/
abbrev FinSqUniverse (R : Type*) := Σ (n : ℕ), FinSqFamily n R

/-- `PosFinSqUniverse R`: the subtype of square matrices with dimension `n > 0`. -/
abbrev PosFinSqUniverse (R : Type*) := { x : FinSqUniverse R // x.1 > 0 }

/-- Extract the matrix from a square-matrix universe object. -/
@[simp] def FinSqUniverse.matrix {R} (x : FinSqUniverse R) : Matrix (Fin x.1) (Fin x.1) R :=
  x.2.A

end MatDecompFormal.Framework
