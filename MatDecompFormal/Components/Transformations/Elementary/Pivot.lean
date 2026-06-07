import Mathlib.LinearAlgebra.Matrix.Swap
import MatDecompFormal.Abstractions.Transformation
import MatDecompFormal.Framework.HeadTail

namespace MatDecompFormal.Components.Transformations.Elementary

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework

/-!
# Pivoting Transformation

This file provides the active pivoting transformation used by the refactored
PLU path. On a finite nonempty linearly ordered index type, it either certifies
that the distinguished head pivot is already nonzero, certifies that the whole
head column is zero, or swaps a row with a nonzero head-column entry into the
head position.
-/

section Pivot

variable {ι R : Type*}
variable [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
variable [Semiring R]

/-- The PLU pivoting goal: either the head pivot is nonzero, or the whole head column vanishes. -/
def PivotReady (A : Matrix ι ι R) : Prop :=
  A (headElem (α := ι)) (headElem (α := ι)) ≠ 0 ∨
    ∀ i, A i (headElem (α := ι)) = 0

/-- Swap a chosen row into the head position. -/
noncomputable def pivotToHeadOrZero : Transformation (Matrix ι ι R) where
  T := ι
  Goal := PivotReady
  decGoal := by
    classical
    intro A
    dsimp [PivotReady]
    infer_instance
  apply i A := Matrix.swap R (headElem (α := ι)) i * A
  find := by
    intro A hA
    classical
    have h_not_zero_col : ¬ ∀ i, A i (headElem (α := ι)) = 0 := by
      intro hcol
      exact hA (Or.inr hcol)
    exact Classical.choose (not_forall.mp h_not_zero_col)
  find_spec := by
    intro A hA
    classical
    have h_not_zero_col : ¬ ∀ i, A i (headElem (α := ι)) = 0 := by
      intro hcol
      exact hA (Or.inr hcol)
    let i : ι := Classical.choose (not_forall.mp h_not_zero_col)
    have hi : A i (headElem (α := ι)) ≠ 0 :=
      Classical.choose_spec (not_forall.mp h_not_zero_col)
    left
    have hswap :
        (Matrix.swap R (headElem (α := ι)) i * A)
          (headElem (α := ι)) (headElem (α := ι)) =
          A i (headElem (α := ι)) := by
      simpa using
        (Matrix.swap_mul_apply_left (i := headElem (α := ι)) (j := i)
          (a := headElem (α := ι)) (g := A))
    exact hswap.trans_ne hi

end Pivot

end MatDecompFormal.Components.Transformations.Elementary
