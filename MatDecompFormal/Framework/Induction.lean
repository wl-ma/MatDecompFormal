import Mathlib
import MatDecompFormal.Framework.Universe -- Explicitly note that the universe types come from here


namespace MatDecompFormal.Framework

/-!
# General Induction Framework

This file defines the core induction principle for the whole formalization project.
It is based on a “universe” type `X` containing matrices of all possible sizes.
Inducting over this unified type cleanly handles cross-type, dimension-reducing
reductions.

In this project, the universe `X` is instantiated as `Σ n, SquareMatFamily n R`,
the dependent sum type of square matrices of all dimensions.

### Framework Layers
1.  **`X` (universe type)**:
    A unified type encapsulating matrices of all possible sizes.

2.  **`induction_by_reduction` (core engine)**:
    The lowest-level unified induction principle, operating on the universe `X`.
    It decomposes the proof task into handling an explicitly specified base-case
    set (`BaseSet`) and a reduction step.

3.  **`wellFounded_induction_via_reduction` (generic API)**:
    A convenience wrapper around `induction_by_reduction` for the common case where
    the base cases are exactly the minimal elements under the induction relation.

4.  **`transformSliceInduction` (domain-specific API)**:
    Another convenience wrapper, designed specifically for this project, for
    induction based on a natural-number measure `μ` where the base cases are the
    states with measure zero. This is the theorem most often called directly in
    this project.
-/

variable {X : Type*}

/--
`Transport r P` states that the proposition `P` can be transported along the
transformation relation `r`.
-/
def Transport (r : X → X → Prop) (P : X → Prop) : Prop :=
  ∀ (x y : X), r x y → P x → P y


-- ==================================================================
-- L0: THE CORE ENGINE (on X)
-- ==================================================================

/--
`induction_by_reduction` is the core unified induction principle of this framework,
operating on the universe `X`.
-/
theorem induction_by_reduction
    {rel : X → X → Prop} (hwf : WellFounded rel)
    (BaseSet : X → Prop)
    {r : X → X → Prop} {P : X → Prop}
    (h_trans : Transport r P)
    (IsReducible : X → Prop)
    (decompose : ∀ {x : X}, IsReducible x → X)
    (reconstruct : ∀ {x : X} (hx : IsReducible x), P (decompose hx) → P x)
    (prove_on_base : ∀ {x : X}, BaseSet x → P x)
    (reach_from_non_base : ∀ {x : X}, ¬ BaseSet x →
      ∃ y, ∃ (hy : IsReducible y), r y x ∧ rel (decompose hy) x)
    : ∀ (x : X), P x := by
  intro x_to_prove
  apply hwf.induction x_to_prove
  clear x_to_prove
  intro x ih
  by_cases h_is_base : BaseSet x
  · exact prove_on_base h_is_base
  · rcases reach_from_non_base h_is_base with ⟨y, hy, h_r_yx, h_rel_decompose⟩
    have p_decompose : P (decompose hy) := ih (decompose hy) h_rel_decompose
    have p_y : P y := reconstruct hy p_decompose
    exact h_trans y x h_r_yx p_y

-- ==================================================================
-- L1: CONVENIENCE APIS (Corollaries of the Core Engine)
-- ==================================================================

/--
`wellFounded_induction_via_reduction` is an instance of `induction_by_reduction`
for the case where the base cases are the minimal elements, operating on the universe `X`.
-/
theorem wellFounded_induction_via_reduction
    {rel : X → X → Prop} (hwf : WellFounded rel)
    {r : X → X → Prop} {P : X → Prop}
    (h_trans : Transport r P)
    (IsReducible : X → Prop)
    (decompose : ∀ {x : X}, IsReducible x → X)
    (reconstruct : ∀ {x : X} (hx : IsReducible x), P (decompose hx) → P x)
    (reachability : ∀ {x : X}, (∃ y, rel y x) →
      ∃ y, ∃ (hy : IsReducible y), r y x ∧ rel (decompose hy) x)
    (base_case : ∀ {x : X}, (¬ ∃ y, rel y x) → P x)
    : ∀ (x : X), P x := by
  -- Call the core engine with BaseSet defined as the set of minimal elements.
  apply induction_by_reduction hwf
    (BaseSet := fun x ↦ ¬ ∃ y, rel y x)
    h_trans IsReducible decompose reconstruct
    (prove_on_base := base_case)
    (reach_from_non_base := by
      -- `¬ (¬ ∃ y, rel y x)` is equivalent to `∃ y, rel y x`
      intro x h_non_minimal
      push_neg at h_non_minimal
      exact reachability h_non_minimal)


/--
`transformSliceInduction` is a convenience API for well-founded induction in the
universe `X`, and is an instance of `wellFounded_induction_via_reduction`.
-/
theorem transformSliceInduction
    (μ : X → Nat)
    (P : X → Prop)
    {r : X → X → Prop}
    (h_trans : Transport r P)
    (IsSliceable : X → Prop)
    (slice : ∀ {x : X}, IsSliceable x → X)
    (lift_from_slice : ∀ {x : X} (hx : IsSliceable x), P (slice hx) → P x)
    (reach_metric : ∀ {x : X}, μ x > 0 →
      ∃ y, ∃ (hy : IsSliceable y), r y x ∧ μ (slice hy) < μ x)
    (base_metric : ∀ {x : X}, μ x = 0 → P x)
    : ∀ (x : X), P x := by
  -- Call the core engine directly, explicitly defining the base-case set.
  apply induction_by_reduction (WellFounded.onFun wellFounded_lt)
    (BaseSet := fun x ↦ μ x = 0)
    (h_trans := h_trans)
    (IsReducible := IsSliceable)
    (decompose := slice)
    (reconstruct := lift_from_slice)
    (prove_on_base := base_metric)
    (reach_from_non_base := by
      -- Prove that `¬ BaseSet x` implies the `reach` condition
      -- `¬ (μ x = 0)` is equivalent to `μ x ≠ 0`.
      intro x h_non_base
      -- For natural numbers, `μ x ≠ 0` is equivalent to `μ x > 0`.
      have h_mu_pos : μ x > 0 := Nat.pos_of_ne_zero h_non_base
      -- Apply `reach_metric` directly
      exact reach_metric h_mu_pos)

variable {X : Type*}

/--
`transformSliceInductionGeneral` is an extended version of `transformSliceInduction`
allowing the base cases to be an arbitrary given measure lower bound `μ_base`, rather
than only 0.

When `μ x > μ_base`, one must find a reducible state whose sliced measure is strictly
smaller. When `μ x ≤ μ_base`, use `base_metric` directly.
-/
theorem transformSliceInductionGeneral
    (μ : X → Nat) (μ_base : Nat)
    (P : X → Prop)
    {r : X → X → Prop}
    (h_trans : Transport r P)
    (IsSliceable : X → Prop)
    (slice : ∀ {x : X}, IsSliceable x → X)
    (lift_from_slice : ∀ {x : X} (hx : IsSliceable x), P (slice hx) → P x)
    (reach_metric : ∀ {x : X}, μ x > μ_base →
      ∃ y, ∃ (hy : IsSliceable y), r y x ∧ μ (slice hy) < μ x)
    (base_metric : ∀ {x : X}, μ x ≤ μ_base → P x)
    : ∀ (x : X), P x := by
  -- Call the core engine directly with base-case set `μ x ≤ μ_base`.
  apply induction_by_reduction (WellFounded.onFun wellFounded_lt)
    (BaseSet := fun x ↦ μ x ≤ μ_base)
    (h_trans := h_trans)
    (IsReducible := IsSliceable)
    (decompose := slice)
    (reconstruct := lift_from_slice)
    (prove_on_base := base_metric)
    (reach_from_non_base := by
      intro x h_non_base
      -- `¬ (μ x ≤ μ_base)` is equivalent to `μ x > μ_base`.
      have h_mu_pos : μ x > μ_base := Nat.lt_of_not_ge h_non_base
      -- Use the provided `reach_metric` directly
      exact reach_metric h_mu_pos)


/--
`induction_on_subtype`

This is a powerful principle tailored for subtype-driven induction proofs. It performs
well-founded induction over a general universe `X`, while its core transformation and
reduction logic only acts on a specified subtype `SubX`.

This theorem captures the pattern used in matrix decomposition: we induct over the
universe of all matrices, but apply the more complex decomposition algorithm only
to the subtype of positive-dimensional matrices.

Parameters:
*   `X`: the general universe type where induction takes place.
*   `SubX`: a subtype of `X` representing the objects we actually care about
    and need to process in detail.
*   `μ`: the measure function defined on the whole universe `X`.
*   `μ_base`: the measure bound for induction base cases.
*   `P`: the property to prove over the whole universe `X`.
*   `P_sub`: the subtype-level version of `P` on `SubX`.
*   `P_compat`: guarantees that `P` and `P_sub` are equivalent on the subtype.
*   `r_sub`: the transformation relation defined only between members of `SubX`.
*   `IsSliceable_sub`: the sliceability predicate defined only for members of `SubX`.
*   `slice_sub`: extracts a subproblem, possibly in `X`, from a sliceable member of `SubX`.
*   `transport_sub`, `lift_from_slice_sub`, `reach_sub`:
    all core induction-step lemmas, defined and proved only in the `SubX` context.
*   `base_univ`: provides a uniform base-case proof for all objects in the universe `X`
    that are **not in** `SubX`, or whose measure is `≤ μ_base`.
-/
theorem induction_on_subtype
    (SubX : Type*) (toX : SubX → X)
    (μ : X → Nat) (μ_base : Nat)
    (P : X → Prop)
    (P_sub : SubX → Prop)
    (P_compat : ∀ (x_sub : SubX), P_sub x_sub ↔ P (toX x_sub))
    (r_sub : SubX → SubX → Prop)
    (IsSliceable_sub : SubX → Prop)
    (slice_sub : ∀ (x_sub : SubX), IsSliceable_sub x_sub → X)
    (transport_sub : Transport r_sub P_sub)
    (lift_from_slice_sub : ∀ (x_sub : SubX) (hx : IsSliceable_sub x_sub),
                           P (slice_sub x_sub hx) → P_sub x_sub)
    (reach_sub : ∀ (x_sub : SubX), μ (toX x_sub) > μ_base →
                 Σ' (y_sub : SubX), Σ' (hy : IsSliceable_sub y_sub),
                   r_sub y_sub x_sub ∧ μ (slice_sub y_sub hy) < μ (toX x_sub))
    (base_univ :
      ∀ (x : X), (∀ (x_sub : SubX), toX x_sub ≠ x) ∨ μ x ≤ μ_base → P x)
    : ∀ (x : X), P x := by
  refine (WellFounded.fix (InvImage.wf μ wellFounded_lt) (C := fun _ => P _) ?_)
  intro x ih
  by_cases h_in_sub : ∃ (x_sub : SubX), toX x_sub = x
  · rcases h_in_sub with ⟨x_sub, rfl⟩
    -- Prove P (toX x_sub) via the subtype predicate P_sub.
    have hP_sub : P_sub x_sub := by
      by_cases h_mu : μ (toX x_sub) > μ_base
      · rcases reach_sub x_sub h_mu with ⟨y_sub, hy, h_r, h_prog⟩
        let slice_obj := slice_sub y_sub hy
        have h_slice_p : P slice_obj := ih slice_obj h_prog
        have h_y_p : P_sub y_sub := lift_from_slice_sub y_sub hy h_slice_p
        exact transport_sub _ _ h_r h_y_p
      · -- Subtype base case: use base_univ, then convert by compatibility.
        have hP : P (toX x_sub) :=
          base_univ (toX x_sub) (Or.inr (le_of_not_gt h_mu))
        exact (P_compat x_sub).2 hP
    exact (P_compat x_sub).1 hP_sub
  · -- Universe base case
    -- Convert `¬ ∃ x_sub, toX x_sub = x` into the required universal form
    have h_forall : ∀ (x_sub : SubX), toX x_sub ≠ x := by
      intro x_sub hx
      exact h_in_sub ⟨x_sub, hx⟩
    exact base_univ x (Or.inl h_forall)

variable {α : Type*}
/--
`induction_on_subtype` (generalized version):

This is the same “subtype-driven” induction principle as before, but generalized from
`μ : X → Nat` (with `<`) to an arbitrary measure type `α` equipped with a well-founded
relation `relα`.

You also provide a base predicate `BaseSet : X → Prop` instead of a fixed
measure-bound base condition.
-/
theorem induction_on_subtype'
    (SubX : Type*) (toX : SubX → X)
    (μ : X → α) (relα : α → α → Prop) (hwf : WellFounded relα)
    (P : X → Prop)
    (P_sub : SubX → Prop)
    (P_compat : ∀ (x_sub : SubX), P_sub x_sub ↔ P (toX x_sub))
    (r_sub : SubX → SubX → Prop)
    (IsSliceable_sub : SubX → Prop)
    (slice_sub : ∀ (x_sub : SubX), IsSliceable_sub x_sub → X)
    (transport_sub :
      ∀ {x_sub y_sub}, r_sub y_sub x_sub → P_sub y_sub → P_sub x_sub)
    (lift_from_slice_sub :
      ∀ (x_sub : SubX) (hx : IsSliceable_sub x_sub),
        P (slice_sub x_sub hx) → P_sub x_sub)
    (BaseSet : X → Prop)
    (reach_sub :
      ∀ (x_sub : SubX), ¬ BaseSet (toX x_sub) →
        Σ' (y_sub : SubX), Σ' (hy : IsSliceable_sub y_sub),
          r_sub y_sub x_sub ∧ relα (μ (slice_sub y_sub hy)) (μ (toX x_sub)))
    (base_univ :
      ∀ (x : X), (∀ (x_sub : SubX), toX x_sub ≠ x) ∨ BaseSet x → P x)
    : ∀ (x : X), P x := by
  classical
  -- Well-founded recursion on the inv-image relation `InvImage relα μ` on `X`.
  refine
    (WellFounded.fix (InvImage.wf (f := μ) hwf) (C := fun _ => P _) ?_)
  intro x ih

  by_cases h_in_sub : ∃ (x_sub : SubX), toX x_sub = x
  · rcases h_in_sub with ⟨x_sub, rfl⟩

    have hP_sub : P_sub x_sub := by
      by_cases h_base : BaseSet (toX x_sub)
      · -- Subtype base case: use `base_univ`, then convert via `P_compat`.
        have hP : P (toX x_sub) := base_univ (toX x_sub) (Or.inr h_base)
        exact (P_compat x_sub).2 hP
      · -- Non-base: use `reach_sub`, then recurse on the slice.
        rcases reach_sub x_sub h_base with ⟨y_sub, hy, h_r, h_prog⟩
        let slice_obj := slice_sub y_sub hy
        have h_slice_p : P slice_obj := ih slice_obj h_prog
        have h_y_p : P_sub y_sub := lift_from_slice_sub y_sub hy h_slice_p
        exact transport_sub h_r h_y_p

    exact (P_compat x_sub).1 hP_sub
  · -- Universe base case: not in the subtype, so discharge with `base_univ`.
    have h_forall : ∀ (x_sub : SubX), toX x_sub ≠ x := by
      intro x_sub hx
      exact h_in_sub ⟨x_sub, hx⟩
    exact base_univ x (Or.inl h_forall)

end MatDecompFormal.Framework
