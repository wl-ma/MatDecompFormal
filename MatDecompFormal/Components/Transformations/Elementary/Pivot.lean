import Mathlib.LinearAlgebra.Matrix.Permutation
import MatDecompFormal.Abstractions.Transformation
import Mathlib.LinearAlgebra.Matrix.Swap

namespace MatDecompFormal.Components.Transformations.Elementary

open Matrix

/-!
# Pivoting Transformation

This file defines `PivotTransform`, a `Transformation` instance implemented in the
`Fin n` world. Its goal is to ensure the matrix entry `A 0 0` is nonzero by swapping rows.

### Design
- **NeZero constraints**: To make `0` a valid index on `Fin n` and `Fin m`,
  `PivotTransform` requires `n` and `m` to be nonzero, namely `[NeZero n]`
  and `[NeZero m]`. This ensures that `Fin n` and `Fin m` are nonempty, making
  `0` a valid index.
- **Decoupled mechanism and strategy**: the mechanism that performs the swap is
  decoupled from the externally provided strategy that finds the target row to
  swap with.
-/

/--
`PivotTransform` is a `Transformation` instance that ensures the pivot entry
`A 0 0` is nonzero by swapping rows.

*   `[NeZero n]`, `[NeZero m]`: key assumptions ensuring that `0` is a valid
    index of `Fin n` and `Fin m`.
*   `search_for_pivot`: an externally provided search algorithm.
*   `search_spec`: a correctness proof for the `search_for_pivot` algorithm.
-/
noncomputable def PivotTransform (n m : ℕ) (R : Type*)
    -- Add NeZero constraints
    [NeZero n] [NeZero m] [Field R] [DecidableEq R]
    (search_for_pivot : (A : Matrix (Fin n) (Fin m) R) → (h : A 0 0 = 0) → Fin n)
    (search_spec : ∀ (A : Matrix (Fin n) (Fin m) R) (h : A 0 0 = 0),
      A (search_for_pivot A h) 0 ≠ 0) :
    Abstractions.Transformation (Matrix (Fin n) (Fin m) R) where
  -- The transformation parameter is the target row index.
  T := Fin n
  -- The goal is that the pivot is nonzero.
  Goal := fun A ↦ A 0 0 ≠ 0
  -- `Field` and `DecidableEq` ensure that `Goal` is decidable.
  decGoal := by infer_instance
  -- Apply the transformation by left-multiplying by the row-swap matrix `swap R 0 i₁`.
  -- This `0` is now type-safe because of the `[NeZero n]` constraint.
  apply := fun i₁ A ↦ (swap R 0 i₁) * A
  -- The `find` operation delegates directly to the externally provided search algorithm.
  find := fun A h_goal_not_met ↦ search_for_pivot A (not_ne_iff.mp h_goal_not_met)
  -- The proof of `find_spec` comes directly from `search_spec`.
  find_spec := by
    intro A h_goal_not_met
    let i₁ := search_for_pivot A (not_ne_iff.mp h_goal_not_met)
    -- `swap_mul_apply_left` also needs `0` to be a valid index.
    rw [swap_mul_apply_left]
    exact search_spec A (not_ne_iff.mp h_goal_not_met)

end MatDecompFormal.Components.Transformations.Elementary
