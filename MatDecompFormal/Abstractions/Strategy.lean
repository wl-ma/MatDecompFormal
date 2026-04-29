import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Abstractions.Transformation

namespace MatDecompFormal.Abstractions

/-!
# Reduction Strategy

This file defines `ReductionStrategy`, which combines a transformation and a reduction
into a complete induction step executable on `Fin m × Fin n` matrices.
-/

/--
`ReductionStrategy`

*   `m`, `n`: dimensions of the original matrix.
*   `slice_m`, `slice_n`: dimensions of the subproblem matrix.
*   `R`: the ring type.
-/
structure ReductionStrategy (m n slice_m slice_n : ℕ) (R : Type*) [CommRing R] where
  /-- The transformation used to reach a sliceable state. -/
  transform : Transformation (Matrix (Fin m) (Fin n) R)
  /-- The reduction method used to decompose the problem. -/
  reduction : ReductionMethod m n slice_m slice_n R
  /--
  Compatibility assertion: the transformation target `Goal` must be logically
  equivalent to the reduction method’s `IsSliceable` condition.
  -/
  goal_is_sliceable : transform.Goal = reduction.IsSliceable

  /-- Measure function for the original problem size (m×n). -/
  μ : Matrix (Fin m) (Fin n) R → ℕ

  /-- Measure function for the sliced problem size (slice_m×slice_n). -/
  μ_slice : Matrix (Fin slice_m) (Fin slice_n) R → ℕ

  /--
  Measure monotonicity: transformations do not increase the measure, acting on
  the same m×n size.
  -/
  μ_mono :
    ∀ (A : Matrix (Fin m) (Fin n) R) (t : transform.T),
      μ (transform.apply t A) ≤ μ A

  /--
  Slice progress: the sliced measure, computed with μ_slice, is strictly smaller
  than the original problem measure, computed with μ.
  -/
  slice_progress :
    ∀ (A : Matrix (Fin m) (Fin n) R) (hA : reduction.IsSliceable A),
      μ_slice (reduction.slice A hA) < μ A

/--
`ReductionStrategy.r` defines the transformation relation allowed by the strategy.
-/
def ReductionStrategy.r {m n slice_m slice_n R} [CommRing R]
    (S : ReductionStrategy m n slice_m slice_n R) (y x : Matrix (Fin m) (Fin n) R) : Prop :=
  (y = x) ∨ (∃ (t : S.transform.T), y = S.transform.apply t x)

/--
`ReductionStrategy.mk_reach` automatically constructs from a strategy the `reach` proof
required by subtype induction instances.
-/
noncomputable def ReductionStrategy.mk_reach {m n slice_m slice_n R} [CommRing R]
    (S : ReductionStrategy m n slice_m slice_n R) (μ_base : ℕ)
    (_h_pos : m > 0 ∧ n > 0)
    (A : Matrix (Fin m) (Fin n) R)
    (_h_mu_gt_base : S.μ A > μ_base)
    : Σ' (B : Matrix (Fin m) (Fin n) R),
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
