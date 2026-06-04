import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Tactic.SplitIfs -- Explicitly import `split_ifs`

namespace MatDecompFormal.Abstractions

/-!
# Transformation

This file defines the `Transformation` structure, which provides a unified,
goal-directed abstraction interface for matrix transformations. The core idea is
that a transformation is not merely a function, but is also associated with an
explicit goal.

A `Transformation` instance packages the following data:
1.  **Transformation type (`T`)**: the parameter type for a concrete
    transformation. For row swaps, `T` can be a pair of row indices `ι × ι`;
    for a Householder transformation, `T` can be a vector.
2.  **Goal (`Goal`)**: a predicate describing the state the transformation
    aims to make the matrix satisfy. For example,
    “the pivot is nonzero” or “a specific entry in the first column is zero”.
3.  **Decidability (`decGoal`)**: a proof ensuring that `Goal` is decidable.
    This is the key to using `if ... then ... else` in proofs and computation.
4.  **Application (`apply`)**: how to apply a concrete transformation instance `t : T` to a matrix.
5.  **Search (`find`)**: a constructive function. If a matrix does not yet satisfy `Goal`, `find`
    can find a concrete transformation `t : T`.
6.  **Reduction (`find_spec`)**: the correctness proof for `find`, ensuring
    that the transformation `t` it finds
    really makes the matrix satisfy `Goal` after application.

In addition, this file defines two ways to compose transformations:
- `compose`: strict sequential composition where every step must be executed.
- `compose_sequential`: flexible sequential composition where only necessary steps are executed.
-/


/--
`Transformation` is a structure describing a goal-directed matrix transformation.

*   `X`: the type of objects being transformed, usually `Matrix ι κ R` in this project.
*   `T`: the type of transformation parameters.
*   `Goal`: the target state the transformation aims to reach, as a predicate.
*   `decGoal`: an instance proving that `Goal` is a decidable predicate.
*   `apply`: applies a transformation parameter `t : T` to an object `x : X`.
*   `find`: when object `x` does not satisfy `Goal`, finds a transformation
    parameter `t` that makes it satisfy `Goal`.
*   `find_spec`: proves that the `t` found by `find` is valid.
-/
structure Transformation (X : Type*) where
  /-- The type of transformation parameters. For example, for row swaps, it is `ι × ι`. -/
  T : Type*
  /--
  The target state the transformation aims to reach, for example
  `fun A ↦ A i₀ j₀ ≠ 0`.
  -/
  Goal : X → Prop
  /--
  Proof that `Goal` is a decidable predicate. This is the prerequisite for
  using `if` expressions.
  -/
  [decGoal : DecidablePred Goal]
  /-- Apply the transformation to an object. -/
  apply : T → X → X
  /--
  When the goal has not been reached, find a valid transformation.
  This is the constructive core.
  -/
  find : (x : X) → (h : ¬ Goal x) → T
  /-- Correctness proof for `find`, ensuring that `find` found the correct transformation. -/
  find_spec : ∀ (x : X) (h : ¬ Goal x), Goal (apply (find x h) x)

-- Register `decGoal` as a typeclass instance for `if T.Goal x then ...`.
attribute [instance] Transformation.decGoal


/--
The `Transformation.compose` function strictly sequences two transformations `T₁` and `T₂`,
forming a new macro transformation.

This composition applies when `T₁` should always be executed before `T₂`;
for example, when `T₁` prepares the preconditions for `T₂`.

*   **`h_precond`**: a key helper function. The caller must provide a way
    to derive that the first-step goal `T₁.Goal` is also unmet from the fact
    that the final goal `T₂.Goal` is unmet.
    This formalizes the idea that `T₁` is a necessary preliminary step for `T₂`.
*   **`h_preserves`**: another assumption ensuring that applying `T₁` does not
    accidentally fix the `T₂` problem,
    thereby ensuring that `T₂.find` can always be called.
-/
def Transformation.compose {X} (T₁ T₂ : Transformation X)
    (h_precond : ∀ x, ¬ T₂.Goal x → ¬ T₁.Goal x)
    (h_preserves : ∀ (x : X) (h₁ : ¬ T₁.Goal x),
      ¬ T₂.Goal x → ¬ T₂.Goal (T₁.apply (T₁.find x h₁) x))
    : Transformation X where
  T := T₁.T × T₂.T
  Goal := T₂.Goal
  decGoal := T₂.decGoal
  apply := fun (t₁, t₂) x ↦ T₂.apply t₂ (T₁.apply t₁ x)
  find := fun x h_goal_not_met ↦
    -- Use h_precond to derive that the first-step goal is unmet from the final goal being unmet
    let h₁ := h_precond x h_goal_not_met
    let t₁_inst := T₁.find x h₁
    let x' := T₁.apply t₁_inst x
    -- Use h_preserves to prove that after applying T₁, the T₂ goal is still unmet
    let h₂ := h_preserves x h₁ h_goal_not_met
    let t₂_inst := T₂.find x' h₂
    (t₁_inst, t₂_inst)
  find_spec := by
    intro x h_goal_not_met
    -- Unfold `find` and `apply` enough to make the goal clearer.
    -- However, because `find` uses `let` internally, plain `simp` may not work well.
    -- A more robust proof manually simulates the logic of `find`.
    let h₁ := h_precond x h_goal_not_met
    let t₁_inst := T₁.find x h₁
    let x' := T₁.apply t₁_inst x
    let h₂ := h_preserves x h₁ h_goal_not_met
    let t₂_inst := T₂.find x' h₂
    -- This is exactly the conclusion of `T₂.find_spec`.
    exact T₂.find_spec x' h₂

/--
`Transformation.compose_sequential` is a more flexible sequential combinator.

It applies when we want to first achieve the goal of `T₁`, then the goal of
`T₂`, while either step may be skipped because its goal has already been achieved.

*   **Transformation type `T`**: `Option T₁.T × Option T₂.T`. `none` means
    the transformation for that step
    is unnecessary because the goal has already been achieved.
*   **New `find` logic**: it precisely computes which transformation steps are necessary.
-/
def Transformation.compose_sequential {X} (T₁ T₂ : Transformation X) :
    Transformation X where
  T := Option T₁.T × Option T₂.T
  Goal := T₂.Goal
  decGoal := T₂.decGoal
  apply := fun
    | (some t₁, some t₂) => fun x ↦ T₂.apply t₂ (T₁.apply t₁ x)
    | (some t₁, none)    => fun x ↦ T₁.apply t₁ x
    | (none,    some t₂) => fun x ↦ T₂.apply t₂ x
    | (none,    none)    => fun x ↦ x
  find := fun x h_t2_goal_not_met ↦
    if h₁ : T₁.Goal x then
      -- Step 1 goal is already achieved; only execute step 2.
      (none, some (T₂.find x h_t2_goal_not_met))
    else
      -- Step 1 goal is not achieved; step 1 must be executed first.
      let t₁_inst := T₁.find x h₁
      let x' := T₁.apply t₁_inst x
      if h₂ : T₂.Goal x' then
        -- After applying T₁, the step 2 goal is unexpectedly achieved; no need to execute step 2.
        (some t₁_inst, none)
      else
        -- After applying T₁, the step 2 goal is still not achieved; continue with step 2.
        (some t₁_inst, some (T₂.find x' h₂))
  find_spec := by
    intro x h_t2_goal_not_met
    -- Expose the `if` expressions in `find` to `split_ifs`.
    simp only
    -- Prove by cases on the `if` conditions in the `find` function.
    split_ifs with h₁ h₂
    · -- Branch 1: T₁.Goal x (h₁) is true.
      -- `find` returns (none, some ...), and `apply` applies T₂.
      -- The goal `T₂.Goal (T₂.apply ...)` is guaranteed by `T₂.find_spec`.
      simp only
      exact T₂.find_spec x h_t2_goal_not_met
    · -- Branch 2: ¬ T₁.Goal x (h₁), and T₂.Goal (T₁.apply ... x) (h₂) is true.
      -- `find` returns (some ..., none), and `apply` applies T₁.
      -- The goal `T₂.Goal (T₁.apply ... x)` is exactly assumption `h₂`.
      exact h₂
    · -- Branch 3: ¬ T₁.Goal x (h₁), and ¬ T₂.Goal (T₁.apply ... x) (h₂).
      -- `find` returns (some ..., some ...), and `apply` applies T₁ and then T₂.
      -- The goal `T₂.Goal (T₂.apply ... (T₁.apply ... x))` is guaranteed by `T₂.find_spec`.
      simp only
      let x' := T₁.apply (T₁.find x h₁) x
      exact T₂.find_spec x' h₂

end MatDecompFormal.Abstractions
