/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.SVD.Strategy
import MatDecompFormal.Instances.UTV.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# UTV Strategy Core

The UTV descent uses the same rectangular head-tail block-ready shape as SVD:
after a two-sided unitary transform, the head row and head column decouple and
the lower-right block is recursively decomposed.
-/

/-- Row tail index for UTV descent, aliased to `SVDTailRowIdx`. -/
abbrev UTVTailRowIdx := SVDTailRowIdx
/-- Column tail index for UTV descent, aliased to `SVDTailColIdx`. -/
abbrev UTVTailColIdx := SVDTailColIdx

/-- `UTVBlockReady m n A` holds when `A` is in SVD block-ready form, i.e., after a two-sided
unitary transformation the head row and column decouple. -/
def UTVBlockReady
    (m n : Type*) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n ℂ) : Prop :=
  SVDBlockReady m n A

/-- `UTVDescentReady` holds when the matrix is in UTV block-ready form (same as `UTVBlockReady`). -/
def UTVDescentReady
    (m n : Type*) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n ℂ) : Prop :=
  UTVBlockReady m n A

noncomputable instance utvDescentReadyDecidable
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    DecidablePred (fun A : Matrix m n ℂ => UTVDescentReady m n A) := by
  classical
  intro A
  exact inferInstance

/-- An oracle providing, for every positive rectangular matrix, unitary matrices `U`, `V` such
that `Uᴴ * A * V` is in `UTVDescentReady` form. -/
structure UTVSimilarityOracle
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  U : Matrix m n ℂ → Matrix m m ℂ
  V : Matrix m n ℂ → Matrix n n ℂ
  unitary_U : ∀ A, IsUnitaryMatrix (U A)
  unitary_V : ∀ A, IsUnitaryMatrix (V A)
  descentReady : ∀ A, UTVDescentReady m n ((U A)ᴴ * A * (V A))

/-- Constructs a `UTVSimilarityOracle` from an `SVDBlockReadyOracle` by direct aliasing. -/
noncomputable def utvSimilarityOracleOfSVDBlockReady
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (oracle : SVDBlockReadyOracle m n) :
    UTVSimilarityOracle m n where
  U := oracle.U
  V := oracle.V
  unitary_U := oracle.unitary_U
  unitary_V := oracle.unitary_V
  descentReady := oracle.blockReady

/-- The `Transformation` that applies the oracle's two-sided unitary similarity to drive
the matrix into `UTVDescentReady` form. -/
noncomputable def utvTwoSidedUnitaryTransform
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (oracle : UTVSimilarityOracle m n) :
    Transformation (Matrix m n ℂ) where
  T :=
    { UV : Matrix m m ℂ × Matrix n n ℂ //
      IsUnitaryMatrix UV.1 ∧ IsUnitaryMatrix UV.2 }
  Goal := UTVDescentReady m n
  apply := fun UV A => UV.1.1ᴴ * A * UV.1.2
  find := fun A _h =>
    ⟨(oracle.U A, oracle.V A), oracle.unitary_U A, oracle.unitary_V A⟩
  find_spec := by
    intro A _h
    exact oracle.descentReady A

/-- The `ReductionMethod` extracting the tail submatrix block from a UTV-ready matrix. -/
noncomputable def utvHeadTailReduction
    (m n : Type*) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n] :
    ReductionMethod m n (UTVTailRowIdx m) (UTVTailColIdx n) ℂ :=
  SubmatrixMethod
    (headTailEquiv (α := m))
    (headTailEquiv (α := n))
    (UTVDescentReady m n)

/-- The `RectStrategyCore` for UTV, wiring the oracle's two-sided unitary step into the
rectangular descent driver. -/
noncomputable def utv_strategy_core
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        UTVSimilarityOracle m n) :
    RectStrategyCore ℂ where
  RowSliceIdx := fun {m n} fm _ om nm _ _ _ _ => @UTVTailRowIdx m fm om nm
  ColSliceIdx := fun {m n} _ _ _ _ fn _ on nn => @UTVTailColIdx n fn on nn
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
      { transform := utvTwoSidedUnitaryTransform m n (oracle (m := m) (n := n))
        reduction := utvHeadTailReduction m n
        goal_is_sliceable := rfl
        μ := fun _ => min (Fintype.card m) (Fintype.card n)
        μ_slice := fun _ =>
          min (Fintype.card (UTVTailRowIdx m)) (Fintype.card (UTVTailColIdx n))
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hrow :
              Fintype.card (UTVTailRowIdx m) < Fintype.card m := by
            simpa [UTVTailRowIdx, SVDTailRowIdx] using
              (Fintype.card_subtype_lt
                (p := fun i : m => i ≠ headElem (α := m))
                (x := headElem (α := m))
                (by simp))
          have hcol :
              Fintype.card (UTVTailColIdx n) < Fintype.card n := by
            simpa [UTVTailColIdx, SVDTailColIdx] using
              (Fintype.card_subtype_lt
                (p := fun j : n => j ≠ headElem (α := n))
                (x := headElem (α := n))
                (by simp))
          have hmin_row :
              min (Fintype.card (UTVTailRowIdx m)) (Fintype.card (UTVTailColIdx n)) <
                Fintype.card m :=
            lt_of_le_of_lt (Nat.min_le_left _ _) hrow
          have hmin_col :
              min (Fintype.card (UTVTailRowIdx m)) (Fintype.card (UTVTailColIdx n)) <
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
