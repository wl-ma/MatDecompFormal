/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Gauss.Details

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Gauss Rank Normal Form Strategy

Rectangular descent skeleton for Gauss/rank normal form.  The one-step
row/column elimination is packaged as `GaussRankStepOracle`; the strategy still
uses the shared rectangular driver for reach, transport, slice, and lift.
-/

variable {R : Type v}

/-- Row tail index obtained by removing the distinguished head row. -/
abbrev GaussTailRowIdx (m : Type u) [Fintype m] [LinearOrder m] [Nonempty m] :=
  { i : m // i ≠ headElem (α := m) }

/-- Column tail index obtained by removing the distinguished head column. -/
abbrev GaussTailColIdx (n : Type u) [Fintype n] [LinearOrder n] [Nonempty n] :=
  { j : n // j ≠ headElem (α := n) }

/--
Ready state for a Gauss step: after head-tail reindexing, the head block is the
unit pivot and the rest of the head row/column vanishes.
-/
def GaussRankBlockReady
    (m n : Type u) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n] [Semiring R]
    (A : Matrix m n R) : Prop :=
  let A' := Matrix.reindex (headTailEquiv (α := m)) (headTailEquiv (α := n)) A
  A'.toBlocks₁₁ = 1 ∧ A'.toBlocks₁₂ = 0 ∧ A'.toBlocks₂₁ = 0

/-- The sliceability predicate consumed by the rectangular driver. -/
def GaussRankDescentReady
    (m n : Type u) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n] [Semiring R]
    (A : Matrix m n R) : Prop :=
  A = 0 ∨ GaussRankBlockReady (R := R) m n A

noncomputable instance gaussRankDescentReadyDecidable
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] [Semiring R] :
    DecidablePred (fun A : Matrix m n R => GaussRankDescentReady (R := R) m n A) := by
  classical
  intro A
  exact inferInstance

/--
One-step Gauss elimination oracle.

For positive rectangular index types, it supplies invertible row and column
factors whose two-sided action isolates a unit head pivot and clears the head
row and column.
-/
structure GaussRankStepOracle
    (R : Type v) [Semiring R]
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  P : Matrix m n R → Matrix m m R
  Q : Matrix m n R → Matrix n n R
  invertible_P : ∀ A, GaussInvertibleMatrix (P A)
  invertible_Q : ∀ A, GaussInvertibleMatrix (Q A)
  ready : ∀ A, GaussRankDescentReady (R := R) m n (P A * A * Q A)

/-- Two-sided invertible transformation driven by a Gauss one-step oracle. -/
noncomputable def gaussTwoSidedUnitTransform
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] [Semiring R]
    (oracle : GaussRankStepOracle R m n) :
    Transformation (Matrix m n R) where
  T :=
    { PQ : Matrix m m R × Matrix n n R //
      GaussInvertibleMatrix PQ.1 ∧ GaussInvertibleMatrix PQ.2 }
  Goal := GaussRankDescentReady (R := R) m n
  apply := fun PQ A => PQ.1.1 * A * PQ.1.2
  find := fun A _h =>
    ⟨(oracle.P A, oracle.Q A), oracle.invertible_P A, oracle.invertible_Q A⟩
  find_spec := by
    intro A _h
    exact oracle.ready A

/-- Head-tail lower-right block reduction for a Gauss-ready matrix. -/
noncomputable def gaussHeadTailReduction
    (m n : Type u) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n] [Semiring R] :
    ReductionMethod m n (GaussTailRowIdx m) (GaussTailColIdx n) R :=
  SubmatrixMethod
    (headTailEquiv (α := m))
    (headTailEquiv (α := n))
    (GaussRankDescentReady (R := R) m n)

/-- Rectangular strategy core parameterized by one-step Gauss oracles. -/
noncomputable def gauss_strategy_core [Semiring R]
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        GaussRankStepOracle R m n) :
    RectStrategyCore R where
  RowSliceIdx := fun {m n} fm _ om nm _ _ _ _ => @GaussTailRowIdx m fm om nm
  ColSliceIdx := fun {m n} _ _ _ _ fn _ on nn => @GaussTailColIdx n fn on nn
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
      { transform := gaussTwoSidedUnitTransform m n (oracle (m := m) (n := n))
        reduction := gaussHeadTailReduction (R := R) m n
        goal_is_sliceable := rfl
        μ := fun _ => min (Fintype.card m) (Fintype.card n)
        μ_slice := fun _ =>
          min (Fintype.card (GaussTailRowIdx m)) (Fintype.card (GaussTailColIdx n))
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hrow :
              Fintype.card (GaussTailRowIdx m) < Fintype.card m := by
            simpa [GaussTailRowIdx] using
              (Fintype.card_subtype_lt
                (p := fun i : m => i ≠ headElem (α := m))
                (x := headElem (α := m))
                (by simp))
          have hcol :
              Fintype.card (GaussTailColIdx n) < Fintype.card n := by
            simpa [GaussTailColIdx] using
              (Fintype.card_subtype_lt
                (p := fun j : n => j ≠ headElem (α := n))
                (x := headElem (α := n))
                (by simp))
          have hmin_row :
              min (Fintype.card (GaussTailRowIdx m)) (Fintype.card (GaussTailColIdx n)) <
                Fintype.card m :=
            lt_of_le_of_lt (Nat.min_le_left _ _) hrow
          have hmin_col :
              min (Fintype.card (GaussTailRowIdx m)) (Fintype.card (GaussTailColIdx n)) <
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
