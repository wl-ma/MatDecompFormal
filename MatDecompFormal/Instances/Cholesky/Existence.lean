/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Cholesky.Details
import MatDecompFormal.Instances.LDL.Existence

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Components.Properties

open scoped ComplexOrder

section Presentation

variable {ι : Type*}

/-- Convert a strengthened LDL decomposition into a standard Cholesky decomposition. -/
theorem hasCholesky_of_hasLDL
    {R : Type*} [RCLike R] [TrivialStar R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R} :
    HasLDLDecomposition A → HasCholesky A := by
  intro hLDL
  rcases hLDL with ⟨⟨L, D⟩, ⟨hLunit, hDdiag, hDpos⟩, hEq⟩
  let S : Matrix ι ι R := choleskySqrtDiagonal D
  refine ⟨L * S, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact isLowerTriangular_mul hLunit.1 (isLowerTriangular_choleskySqrtDiagonal D)
    · simpa [S] using positiveDiagonal_mul_choleskySqrtDiagonal hLunit hDpos
  · have hS : S * Sᵀ = D := by
      simpa [S] using choleskySqrtDiagonal_mul_transpose hDdiag hDpos
    calc
      A = L * D * Lᵀ := hEq
      _ = L * (S * Sᵀ) * Lᵀ := by
        rw [hS]
      _ = (L * S) * (L * S)ᵀ := by
        rw [Matrix.transpose_mul]
        simp [Matrix.mul_assoc]

/-- Positive definite matrices have a Cholesky decomposition. -/
theorem exists_cholesky_decomposition
    {R : Type*} [RCLike R] [TrivialStar R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) (hA : A.PosDef) :
    HasCholesky A :=
  hasCholesky_of_hasLDL (exists_ldl_decomposition A hA)

end Presentation

end MatDecompFormal.Instances
