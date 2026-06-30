/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Framework.UniverseDecomposition

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties
open MatDecompFormal.Framework

/-!
# LU Details

This file contains the LU schema and base cases. LU is the no-pivot analogue of
PLU, so the recursive theorem consumes an explicit no-pivot readiness predicate.
-/

section Presentation

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Semiring R]

/-- Canonical LU schema on finite square matrices. -/
def LU_Schema : DecompositionSchema ι ι R where
  Factors := Matrix ι ι R × Matrix ι ι R
  property := fun (L, U) =>
    IsUnitLowerTriangular L ∧ IsUpperTriangular U
  equation := fun A (L, U) => A = L * U

/-- Canonical LU existence proposition on finite square matrices. -/
def HasLU (A : Matrix ι ι R) : Prop :=
  HasDecomposition LU_Schema A

end Presentation

/-- Any square matrix on a subsingleton index type has a trivial LU decomposition. -/
lemma base_lu_subsingleton
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Semiring R]
    [Subsingleton ι] (A : Matrix ι ι R) :
    HasLU A := by
  refine ⟨(1, A), ?_, ?_⟩
  · constructor
    · exact isUnitLowerTriangular_one
    · exact isUpperTriangular_of_subsingleton A
  · simp [LU_Schema]

/-- Base case for zero-dimensional square universes. -/
lemma base_lu_zero_dim_sq {R : Type*} [Semiring R]
    {x : SquareUniverse R} (h_zero : Fintype.card x.ι = 0) :
    HasLU x.A := by
  classical
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp h_zero
  simpa using base_lu_subsingleton x.A

end MatDecompFormal.Instances
