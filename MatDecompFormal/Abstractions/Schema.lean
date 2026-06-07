import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.Matrix.Basis

namespace MatDecompFormal.Abstractions

/-!
# Decomposition Schema

This file defines the project's canonical decomposition schema surface.
-/

/--
`DecompositionSchema` is the project’s **internal canonical schema surface**.

It targets matrices indexed by arbitrary row and column types and carries the
main internal workflow: construction, reduction, induction, and internal
existence theorems.

*   `ι`, `κ`: the row and column index types of the matrix.
*   `R`: the ring type of matrix entries.
*   `Factors`: the type of the factors after decomposition.
*   `property`: describes the properties required of the decomposed factors.
*   `equation`: describes the algebraic relation between the decomposition
    factors and the original matrix.
-/
structure DecompositionSchema (ι κ : Type*) (R : Type*) where
  /--
  The type of the decomposed factors, for example
  `Matrix ι ι R × Matrix ι κ R` for QR.
  -/
  Factors : Type*
  /-- Describe the properties required of the decomposed factors. -/
  property : Factors → Prop
  /-- Describe the algebraic relation between the decomposition factors and the original matrix. -/
  equation : Matrix ι κ R → Factors → Prop

/--
`HasDecomposition sch A` is the internal canonical existence proposition.

It is the minimal landing point of the project’s unified existence layer inside
the internal proof world. Semantic wrappers for concrete instances should be
built on top of it.
-/
def HasDecomposition {ι κ R}
    (sch : DecompositionSchema ι κ R) (A : Matrix ι κ R) : Prop :=
  ∃ (factors : sch.Factors), sch.property factors ∧ sch.equation A factors

end MatDecompFormal.Abstractions
