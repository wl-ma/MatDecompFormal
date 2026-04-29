import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Data.FinEnum

namespace MatDecompFormal.Abstractions

/-!
# Decomposition Schema

This file explicitly distinguishes the two decomposition surfaces in the project:

* `DecompositionSchema` / `HasDecomposition`
  are the **internal canonical surface**. They serve construction, reduction,
  induction, and main proofs in the `Fin` world. They form the project’s
  standard internal work layer.
* `DecompositionSchema'` / `HasDecomposition'`
  are the **external presentation surface**. They serve external results indexed by `FinEnum`,
  and are usually obtained from internal `_fin` results via reindexing/bridges.

These two layers are not parallel primary interfaces: the `Fin` layer carries
the main proof work, while the `FinEnum` layer provides the unified external
presentation and final result packaging.
-/

/--
`DecompositionSchema` is the project’s **internal canonical schema surface**.

It targets `Fin m × Fin n` matrices and carries the main internal workflow:
construction, reduction, induction, and the `_fin` version of the main existence theorem.

*   `m`, `n`: the row and column counts of the matrix.
*   `R`: the ring type of matrix entries.
*   `Factors`: the type of the factors after decomposition.
*   `property`: describes the properties required of the decomposed factors.
*   `equation`: describes the algebraic relation between the decomposition
    factors and the original matrix.
-/
structure DecompositionSchema (m n : ℕ) (R : Type*) [CommRing R] where
  /--
  The type of the decomposed factors, for example
  `Matrix (Fin m) (Fin m) R × Matrix (Fin m) (Fin n) R` for QR.
  -/
  Factors : Type*
  /-- Describe the properties required of the decomposed factors. -/
  property : Factors → Prop
  /-- Describe the algebraic relation between the decomposition factors and the original matrix. -/
  equation : Matrix (Fin m) (Fin n) R → Factors → Prop

/--
`HasDecomposition sch A` is the internal canonical existence proposition.

It is the minimal landing point of the project’s unified existence layer inside
the internal `Fin` proof world. Semantic wrappers for instances such as
`HasPLU_fin` and `HasQR_fin` should be built on top of it.
-/
def HasDecomposition {m n R} [CommRing R]
    (sch : DecompositionSchema m n R) (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ (factors : sch.Factors), sch.property factors ∧ sch.equation A factors

/--
`DecompositionSchema'` is the **external presentation schema surface**.

It targets matrices indexed by general `FinEnum` types and expresses the view
of internal `_fin` results after bridging to an external schema, rather than
serving as a second internal working interface replacing `DecompositionSchema`.

*   `ι`, `κ`: the row and column index types of the matrix, required to be
    finite and enumerable (`FinEnum`).
*   `R`: the ring type of matrix entries.
*   `Factors`: the type of the factors after decomposition.
*   `property`: describes the properties required of the decomposed factors.
*   `equation`: describes the algebraic relation between the decomposition
    factors and the original matrix.
-/
structure DecompositionSchema' (ι κ : Type*) (R : Type*)
    [FinEnum ι] [FinEnum κ] [CommRing R] where
  /--
  The type of the decomposed factors, for example
  `Matrix ι ι R × Matrix ι κ R` for QR decomposition.
  -/
  Factors : Type*
  /-- Describe the properties required of the decomposed factors. -/
  property : Factors → Prop
  /-- Describe the algebraic relation between the decomposition factors and the original matrix. -/
  equation : Matrix ι κ R → Factors → Prop

/--
`HasDecomposition' sch A` is the external presentation existence proposition.

It states decomposition existence externally for `FinEnum` indices, and should
usually be understood as an internal existence result after canonical bridging
to the presentation layer.
-/
def HasDecomposition' {ι κ R} [FinEnum ι] [FinEnum κ] [CommRing R]
    (sch : DecompositionSchema' ι κ R) (A : Matrix ι κ R) : Prop :=
  ∃ (factors : sch.Factors), sch.property factors ∧ sch.equation A factors

end MatDecompFormal.Abstractions
