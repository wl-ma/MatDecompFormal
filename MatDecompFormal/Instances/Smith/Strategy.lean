/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Gauss.Strategy
import MatDecompFormal.Instances.Smith.Details

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Smith Strategy Core

The Smith descent uses rectangular head-tail slicing. The hard algebraic step
is represented by `SmithStepOracle`: after a two-sided invertible transform, the
head row and head column are isolated and the pivot divides every tail entry.
-/

/-- Row tail index for Smith descent: non-head indices of the row type `m`. -/
abbrev SmithTailRowIdx (m : Type*) [Fintype m] [LinearOrder m] [Nonempty m] :=
  { i : m // i ≠ headElem (α := m) }

/-- Column tail index for Smith descent: non-head indices of the column type `n`. -/
abbrev SmithTailColIdx (n : Type*) [Fintype n] [LinearOrder n] [Nonempty n] :=
  { j : n // j ≠ headElem (α := n) }

/-- `SmithDescentReady R m n A` holds when, after reindexing by `headTailEquiv`, the
matrix `A` has a scalar pivot `d` in the `(1,1)` block, zero off-diagonal blocks, and
`d` divides every entry of the lower-right tail block. -/
def SmithDescentReady
    (R : Type v) [CommSemiring R]
    (m n : Type u) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n R) : Prop :=
  let A' := Matrix.reindex (headTailEquiv (α := m)) (headTailEquiv (α := n)) A
  ∃ d : R, A'.toBlocks₁₁ = (fun _ _ : Unit => d) ∧
    A'.toBlocks₁₂ = 0 ∧ A'.toBlocks₂₁ = 0 ∧
      (∀ i j, d ∣ A'.toBlocks₂₂ i j)

noncomputable instance smithDescentReadyDecidable
    (R : Type v) [CommSemiring R]
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    DecidablePred (fun A : Matrix m n R => SmithDescentReady R m n A) := by
  classical
  intro A
  exact Classical.decPred (fun A : Matrix m n R => SmithDescentReady R m n A) A

/-- An oracle providing, for every positive rectangular matrix, invertible matrices `P`, `Q`
such that `P * A * Q` is in `SmithDescentReady` form. -/
structure SmithStepOracle
    (R : Type v) [CommSemiring R]
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  P : Matrix m n R → Matrix m m R
  Q : Matrix m n R → Matrix n n R
  invertible_P : ∀ A, GaussInvertibleMatrix (P A)
  invertible_Q : ∀ A, GaussInvertibleMatrix (Q A)
  descentReady : ∀ A, SmithDescentReady R m n ((P A) * A * (Q A))

/-- The zero matrix is in `SmithDescentReady` form with pivot `0`. -/
theorem smithDescentReady_of_zero
    (R : Type v) [CommSemiring R]
    (m n : Type u) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n] :
    SmithDescentReady R m n (0 : Matrix m n R) := by
  refine ⟨0, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.toBlocks₁₁]
  · ext i j
    simp [Matrix.toBlocks₁₂]
  · ext i j
    simp [Matrix.toBlocks₂₁]
  · intro i j
    simp [Matrix.toBlocks₂₂]

/-- A Gauss block-ready matrix is Smith descent-ready with pivot `1`. -/
theorem smithDescentReady_of_gaussBlockReady
    (R : Type v) [CommSemiring R]
    (m n : Type u) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n]
    {A : Matrix m n R}
    (hA : GaussRankBlockReady (R := R) m n A) :
    SmithDescentReady R m n A := by
  rcases hA with ⟨h11, h12, h21⟩
  refine ⟨1, h11, h12, h21, ?_⟩
  intro i j
  exact one_dvd _

/-- A Gauss rank-descent-ready matrix is Smith descent-ready. -/
theorem smithDescentReady_of_gaussReady
    (R : Type v) [CommSemiring R]
    (m n : Type u) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n]
    {A : Matrix m n R}
    (hA : GaussRankDescentReady (R := R) m n A) :
    SmithDescentReady R m n A := by
  rcases hA with hzero | hblock
  · rw [hzero]
    exact smithDescentReady_of_zero R m n
  · exact smithDescentReady_of_gaussBlockReady R m n hblock

/-- Constructs a `SmithStepOracle` from a `GaussRankStepOracle` by using the Gauss pivot
as a Smith pivot with divisibility guaranteed by `smithDescentReady_of_gaussReady`. -/
noncomputable def smithStepOracleOfGauss
    (R : Type v) [CommSemiring R]
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (oracle : GaussRankStepOracle R m n) :
    SmithStepOracle R m n where
  P := oracle.P
  Q := oracle.Q
  invertible_P := oracle.invertible_P
  invertible_Q := oracle.invertible_Q
  descentReady := by
    intro A
    exact smithDescentReady_of_gaussReady R m n (oracle.ready A)

/-- The `Transformation` that applies the oracle's two-sided invertible similarity to drive
the matrix into `SmithDescentReady` form. -/
noncomputable def smithTwoSidedInvertibleTransform
    (R : Type v) [CommSemiring R]
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (oracle : SmithStepOracle R m n) :
    Transformation (Matrix m n R) where
  T :=
    { PQ : Matrix m m R × Matrix n n R //
      GaussInvertibleMatrix PQ.1 ∧ GaussInvertibleMatrix PQ.2 }
  Goal := SmithDescentReady R m n
  decGoal := smithDescentReadyDecidable R m n
  apply := fun PQ A => PQ.1.1 * A * PQ.1.2
  find := fun A _h =>
    ⟨(oracle.P A, oracle.Q A), oracle.invertible_P A, oracle.invertible_Q A⟩
  find_spec := by
    intro A _h
    exact oracle.descentReady A

/-- The `ReductionMethod` extracting the tail submatrix block from a Smith-ready matrix. -/
noncomputable def smithHeadTailReduction
    (R : Type v) [CommSemiring R]
    (m n : Type u) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n] :
    ReductionMethod m n (SmithTailRowIdx m) (SmithTailColIdx n) R :=
  SubmatrixMethod
    (headTailEquiv (α := m))
    (headTailEquiv (α := n))
    (SmithDescentReady R m n)

/-- The `RectStrategyCore` for Smith, wiring the oracle's two-sided invertible step into the
rectangular descent driver. -/
noncomputable def smith_strategy_core
    (R : Type v) [CommSemiring R]
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SmithStepOracle R m n) :
    RectStrategyCore R where
  RowSliceIdx := fun {m n} fm _ om nm _ _ _ _ => @SmithTailRowIdx m fm om nm
  ColSliceIdx := fun {m n} _ _ _ _ fn _ on nn => @SmithTailColIdx n fn on nn
  rowSliceFintype := by
    intro m n fm dm om nm fn dn on nn
    infer_instance
  rowSliceDecEq := by
    intro m n fm dm om nm fn dn on nn
    infer_instance
  rowSliceLinearOrder := by
    intro m n fm dm om nm fn dn on nn
    infer_instance
  colSliceFintype := by
    intro m n fm dm om nm fn dn on nn
    infer_instance
  colSliceDecEq := by
    intro m n fm dm om nm fn dn on nn
    infer_instance
  colSliceLinearOrder := by
    intro m n fm dm om nm fn dn on nn
    infer_instance
  strategy := by
    intro m n fm dm om nm fn dn on nn
    exact
      { transform := smithTwoSidedInvertibleTransform R m n (oracle (m := m) (n := n))
        reduction := smithHeadTailReduction R m n
        goal_is_sliceable := rfl
        μ := fun _ => min (Fintype.card m) (Fintype.card n)
        μ_slice := fun _ =>
          min (Fintype.card (SmithTailRowIdx m)) (Fintype.card (SmithTailColIdx n))
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hrow :
              Fintype.card (SmithTailRowIdx m) < Fintype.card m := by
            simpa [SmithTailRowIdx] using
              (Fintype.card_subtype_lt
                (p := fun i : m => i ≠ headElem (α := m))
                (x := headElem (α := m))
                (by simp))
          have hcol :
              Fintype.card (SmithTailColIdx n) < Fintype.card n := by
            simpa [SmithTailColIdx] using
              (Fintype.card_subtype_lt
                (p := fun j : n => j ≠ headElem (α := n))
                (x := headElem (α := n))
                (by simp))
          have hmin_row :
              min (Fintype.card (SmithTailRowIdx m)) (Fintype.card (SmithTailColIdx n)) <
                Fintype.card m :=
            lt_of_le_of_lt (Nat.min_le_left _ _) hrow
          have hmin_col :
              min (Fintype.card (SmithTailRowIdx m)) (Fintype.card (SmithTailColIdx n)) <
                Fintype.card n :=
            lt_of_le_of_lt (Nat.min_le_right _ _) hcol
          exact lt_min hmin_row hmin_col }
  μ_eq := by
    intro m n fm dm om nm fn dn on nn A
    rfl
  μ_slice_eq := by
    intro m n fm dm om nm fn dn on nn B
    rfl

end MatDecompFormal.Instances
