import MatDecompFormal.Abstractions.Schema
import Mathlib.LinearAlgebra.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.IsDiag

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions

/-!
# Cholesky-style decomposition via LDL

This file is not an internal-framework showcase like PLU.
It packages an existing mathlib `LDL` result into the project's schema/existence
language. In the current project organization, Cholesky is best read as:

* a conditional instance, because the theorem requires positive definiteness;
* a direct mathlib wrapper, because the main mathematics comes from mathlib.
-/

section Fin

variable {n : ℕ}

/--
Internal-facing Cholesky-style schema on `Fin n`, currently instantiated via LDL data.

Equation form: `A = L * D * Lᵀ`, where `D` is diagonal.
-/
def Cholesky_Schema_fin (n : ℕ) : DecompositionSchema n n ℝ where
  Factors := Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ
  property := fun (_L, D) => D.IsDiag
  equation := fun A (L, D) => A = L * D * Lᵀ

/-- Internal-facing existence proposition for the Cholesky-style wrapper. -/
def HasCholesky_fin (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  HasDecomposition (Cholesky_Schema_fin n) A

/--
Primary internal theorem for the Cholesky-style wrapper.

This is a conditional result on the internal `Fin` layer. It is intentionally
not presented as evidence that Cholesky already runs through the repository's
internal reduction/induction framework.
-/
theorem exists_cholesky_decomposition_fin
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    HasCholesky_fin A := by
  refine ⟨(LDL.lower hA, LDL.diag hA), ?_, ?_⟩
  · dsimp [Cholesky_Schema_fin, LDL.diag]
    exact Matrix.isDiag_diagonal (LDL.diagEntries hA)
  · have hldl : LDL.lower hA * LDL.diag hA * (LDL.lower hA)ᴴ = A :=
      LDL.lower_conj_diag (hS := hA)
    simpa using hldl.symm

end Fin

end MatDecompFormal.Instances
