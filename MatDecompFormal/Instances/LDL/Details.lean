/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Components.Properties.PositiveDiagonal
import MatDecompFormal.Components.Properties.Triangular
import Mathlib.LinearAlgebra.Matrix.IsDiag

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties

section Presentation

variable {ι R : Type*}

/--
LDL schema on finite square matrices.

Equation form: `A = L * D * Lᵀ`, where `L` is unit lower triangular and `D` is
diagonal with positive diagonal entries.
-/
def LDL_Schema [Fintype ι] [LinearOrder ι] [Semiring R] [PartialOrder R] :
    DecompositionSchema ι ι R where
  Factors := Matrix ι ι R × Matrix ι ι R
  property := fun (L, D) =>
    IsUnitLowerTriangular L ∧ D.IsDiag ∧ PositiveDiagonal D
  equation := fun A (L, D) => A = L * D * Lᵀ

/-- Existence proposition for the strengthened LDL schema. -/
def HasLDLDecomposition [Fintype ι] [LinearOrder ι] [Semiring R] [PartialOrder R]
    (A : Matrix ι ι R) : Prop :=
  HasDecomposition LDL_Schema A

/-- Empty-index LDL witness, used for the zero-dimensional base case. -/
theorem base_ldl_empty
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Semiring R]
    [PartialOrder R] [IsEmpty ι] (A : Matrix ι ι R) :
    HasLDLDecomposition A := by
  refine ⟨(1, A), ?_, ?_⟩
  · refine ⟨isUnitLowerTriangular_one, ?_, ?_⟩
    · intro i _j _hij
      exact isEmptyElim i
    · intro i
      exact isEmptyElim i
  · simp [LDL_Schema]

end Presentation

end MatDecompFormal.Instances
