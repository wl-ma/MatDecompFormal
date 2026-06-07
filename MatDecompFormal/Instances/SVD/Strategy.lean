import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.SVD.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# SVD Strategy Core

This file implements the strategy-side skeleton for a rectangular SVD descent.
The hard singular-vector step is isolated in `SVDSimilarityOracle`: given a
positive rectangular matrix universe, it supplies left and right unitary factors
which make the matrix head-tail block-ready.
-/

/-- Row tail index obtained by removing the distinguished head row. -/
abbrev SVDTailRowIdx (m : Type*) [Fintype m] [LinearOrder m] [Nonempty m] :=
  { i : m // i ≠ headElem (α := m) }

/-- Column tail index obtained by removing the distinguished head column. -/
abbrev SVDTailColIdx (n : Type*) [Fintype n] [LinearOrder n] [Nonempty n] :=
  { j : n // j ≠ headElem (α := n) }

/--
The block-ready state for the SVD descent step: after head-tail reindexing, the
off-diagonal head row and head column blocks vanish. The top-left scalar is the
current singular value and is required to be a nonnegative real scalar.
-/
def SVDBlockReady
    (m n : Type*) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n ℂ) : Prop :=
  let A' := Matrix.reindex (headTailEquiv (α := m)) (headTailEquiv (α := n)) A
  ∃ σ : ℝ, 0 ≤ σ ∧ A'.toBlocks₁₁ = (fun _ _ : Unit => (σ : ℂ)) ∧
    A'.toBlocks₁₂ = 0 ∧ A'.toBlocks₂₁ = 0

/--
The slicability predicate used by the rectangular framework.

The final SVD target is unconditional, so every positive rectangular matrix
must become sliceable after the two-sided unitary transform.
-/
def SVDDescentReady
    (m n : Type*) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n ℂ) : Prop :=
  SVDBlockReady m n A

noncomputable instance svdDescentReadyDecidable
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    DecidablePred (fun A : Matrix m n ℂ => SVDDescentReady m n A) := by
  classical
  intro A
  exact inferInstance

/--
Mathematical oracle for the rectangular SVD step: provide left and right
unitary transformations that put the matrix into head-tail block-ready form.
-/
structure SVDSimilarityOracle
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  U : Matrix m n ℂ → Matrix m m ℂ
  V : Matrix m n ℂ → Matrix n n ℂ
  unitary_U : ∀ A, IsUnitaryMatrix (U A)
  unitary_V : ∀ A, IsUnitaryMatrix (V A)
  descentReady : ∀ A, SVDDescentReady m n ((U A)ᴴ * A * (V A))

/--
One-step block-ready oracle for SVD. This is the standard singular-vector
construction packaged at exactly the strength needed by the descent driver:
after a two-sided unitary transform, the active head row and column decouple and
the head scalar is a nonnegative singular value.
-/
structure SVDBlockReadyOracle
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  U : Matrix m n ℂ → Matrix m m ℂ
  V : Matrix m n ℂ → Matrix n n ℂ
  unitary_U : ∀ A, IsUnitaryMatrix (U A)
  unitary_V : ∀ A, IsUnitaryMatrix (V A)
  blockReady : ∀ A, SVDBlockReady m n ((U A)ᴴ * A * (V A))

noncomputable def svdSimilarityOracleOfBlockReady
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (blockOracle : SVDBlockReadyOracle m n) :
    SVDSimilarityOracle m n where
  U := blockOracle.U
  V := blockOracle.V
  unitary_U := blockOracle.unitary_U
  unitary_V := blockOracle.unitary_V
  descentReady := blockOracle.blockReady

/-- Two-sided unitary transformation driven by an SVD oracle. -/
noncomputable def svdTwoSidedUnitaryTransform
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (oracle : SVDSimilarityOracle m n) :
    Transformation (Matrix m n ℂ) where
  T :=
    { UV : Matrix m m ℂ × Matrix n n ℂ //
      IsUnitaryMatrix UV.1 ∧ IsUnitaryMatrix UV.2 }
  Goal := SVDDescentReady m n
  apply := fun UV A => UV.1.1ᴴ * A * UV.1.2
  find := fun A _h =>
    ⟨(oracle.U A, oracle.V A), oracle.unitary_U A, oracle.unitary_V A⟩
  find_spec := by
    intro A _h
    exact oracle.descentReady A

/-- Head-tail lower-right-block reduction for an SVD-ready matrix. -/
noncomputable def svdHeadTailReduction
    (m n : Type*) [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n] :
    ReductionMethod m n (SVDTailRowIdx m) (SVDTailColIdx n) ℂ :=
  SubmatrixMethod
    (headTailEquiv (α := m))
    (headTailEquiv (α := n))
    (SVDDescentReady m n)

/--
SVD strategy core parameterized by two-sided unitary oracles, one for each
positive rectangular index pair.
-/
noncomputable def svd_strategy_core
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SVDSimilarityOracle m n) :
    RectStrategyCore ℂ where
  RowSliceIdx := fun {m n} fm _ om nm _ _ _ _ => @SVDTailRowIdx m fm om nm
  ColSliceIdx := fun {m n} _ _ _ _ fn _ on nn => @SVDTailColIdx n fn on nn
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
      { transform := svdTwoSidedUnitaryTransform m n (oracle (m := m) (n := n))
        reduction := svdHeadTailReduction m n
        goal_is_sliceable := rfl
        μ := fun _ => min (Fintype.card m) (Fintype.card n)
        μ_slice := fun _ =>
          min (Fintype.card (SVDTailRowIdx m)) (Fintype.card (SVDTailColIdx n))
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hrow :
              Fintype.card (SVDTailRowIdx m) < Fintype.card m := by
            simpa [SVDTailRowIdx] using
              (Fintype.card_subtype_lt
                (p := fun i : m => i ≠ headElem (α := m))
                (x := headElem (α := m))
                (by simp))
          have hcol :
              Fintype.card (SVDTailColIdx n) < Fintype.card n := by
            simpa [SVDTailColIdx] using
              (Fintype.card_subtype_lt
                (p := fun j : n => j ≠ headElem (α := n))
                (x := headElem (α := n))
                (by simp))
          have hmin_row :
              min (Fintype.card (SVDTailRowIdx m)) (Fintype.card (SVDTailColIdx n)) <
                Fintype.card m :=
            lt_of_le_of_lt (Nat.min_le_left _ _) hrow
          have hmin_col :
              min (Fintype.card (SVDTailRowIdx m)) (Fintype.card (SVDTailColIdx n)) <
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
