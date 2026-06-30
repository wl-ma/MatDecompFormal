/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Framework.UniverseDecomposition
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties

/-!
# PLU Details

This file contains the non-assembly PLU implementation details used by the
top-level `Instances.PLU` main-line file:

* the canonical type-indexed PLU schema;
* the semantic existence wrapper used by the main-line theorem;
* the zero-dimensional square-universe base case.
-/

section Presentation

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Semiring R]

/-- Canonical PLU schema on finite square matrices. -/
def PLU_Schema : DecompositionSchema ι ι R where
  Factors := Matrix ι ι R × Matrix ι ι R × Matrix ι ι R
  property := fun (P, L, U) =>
    IsPermutation P ∧ IsUnitLowerTriangular L ∧ IsUpperTriangular U
  equation := fun A (P, L, U) => P * A = L * U

/-- Canonical PLU existence proposition on finite square matrices. -/
def HasPLU (A : Matrix ι ι R) : Prop :=
  HasDecomposition PLU_Schema A

end Presentation

/-- Any square matrix on a subsingleton index type admits a trivial PLU decomposition. -/
lemma base_plu_subsingleton {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Semiring R]
    [Subsingleton ι] (A : Matrix ι ι R) :
    HasPLU A := by
  refine ⟨(1, 1, A), ?_, ?_⟩
  · constructor
    · refine ⟨Equiv.refl ι, ?_⟩
      ext i j
      simp [Matrix.one_apply]
    · constructor
      · exact isUnitLowerTriangular_one
      · exact isUpperTriangular_of_subsingleton A
  · rfl

/-- Base case (Square universe): zero-dimensional square matrices have a trivial PLU. -/
lemma base_plu_zero_dim_sq {R : Type*} [Semiring R]
    {x : SquareUniverse R} (h_zero : Fintype.card x.ι = 0) :
    HasPLU x.A := by
  classical
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp h_zero
  simpa using base_plu_subsingleton x.A

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Semiring R]

end MatDecompFormal.Instances
