/-
Copyright (c) 2026 Wanli Ma, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanli Ma, Zichen Wang
-/
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Abstractions.Transformation

namespace MatDecompFormal.Abstractions

/-!
# Reduction Strategy

This file defines `ReductionStrategy`, which combines a transformation and a reduction
into a complete induction step executable on matrices indexed by general row
and column types.
-/

/--
`ReductionStrategy`

*   `ι`, `κ`: index types of the original matrix.
*   `ιs`, `κs`: index types of the sliced subproblem matrix.
*   `R`: the ring type.
-/
structure ReductionStrategy (ι κ ιs κs : Type*) (R : Type*) where
  /-- The transformation used to reach a sliceable state. -/
  transform : Transformation (Matrix ι κ R)
  /-- The reduction method used to decompose the problem. -/
  reduction : ReductionMethod ι κ ιs κs R
  /--
  Compatibility assertion: the transformation target `Goal` must be logically
  equivalent to the reduction method’s `IsSliceable` condition.
  -/
  goal_is_sliceable : transform.Goal = reduction.IsSliceable

  /-- Measure function for the original problem. -/
  μ : Matrix ι κ R → ℕ

  /-- Measure function for the sliced subproblem. -/
  μ_slice : Matrix ιs κs R → ℕ

  /--
  Measure monotonicity: transformations do not increase the measure, acting on
  the same matrix type.
  -/
  μ_mono :
    ∀ (A : Matrix ι κ R) (t : transform.T),
      μ (transform.apply t A) ≤ μ A

  /--
  Slice progress: the sliced measure, computed with μ_slice, is strictly smaller
  than the original problem measure, computed with μ.
  -/
  slice_progress :
    ∀ (A : Matrix ι κ R) (hA : reduction.IsSliceable A),
      μ_slice (reduction.slice A hA) < μ A

/--
`ReductionStrategy.r` defines the transformation relation allowed by the strategy.
-/
def ReductionStrategy.r {ι κ ιs κs R}
    (S : ReductionStrategy ι κ ιs κs R) (y x : Matrix ι κ R) : Prop :=
  (y = x) ∨ (∃ (t : S.transform.T), y = S.transform.apply t x)

/--
`ReductionStrategy.mk_reach` automatically constructs from a strategy the `reach` proof
required by subtype induction instances.
-/
noncomputable def ReductionStrategy.mk_reach {ι κ ιs κs R}
    (S : ReductionStrategy ι κ ιs κs R) (μ_base : ℕ)
    (_h_nonempty : Nonempty ι ∧ Nonempty κ)
    (A : Matrix ι κ R)
    (_h_mu_gt_base : S.μ A > μ_base)
    : Σ' (B : Matrix ι κ R),
        Σ' (hB : S.reduction.IsSliceable B),
          S.r B A ∧ S.μ_slice (S.reduction.slice B hB) < S.μ A := by
  by_cases h_goal : S.transform.Goal A
  · refine ⟨A, ?_⟩
    have hA_sliceable : S.reduction.IsSliceable A := by
      rw [← S.goal_is_sliceable]; exact h_goal
    refine ⟨hA_sliceable, ?_⟩
    exact ⟨Or.inl rfl, S.slice_progress A hA_sliceable⟩
  · let t := S.transform.find A h_goal
    let B := S.transform.apply t A
    refine ⟨B, ?_⟩
    have hB_sliceable : S.reduction.IsSliceable B := by
      rw [← S.goal_is_sliceable]; exact S.transform.find_spec A h_goal
    refine ⟨hB_sliceable, ?_⟩
    refine ⟨Or.inr ⟨t, rfl⟩, ?_⟩
    have hprog : S.μ_slice (S.reduction.slice B hB_sliceable) < S.μ B :=
      S.slice_progress B hB_sliceable
    have hmono : S.μ B ≤ S.μ A := by
      simpa [B] using S.μ_mono A t
    exact lt_of_lt_of_le hprog hmono

end MatDecompFormal.Abstractions
