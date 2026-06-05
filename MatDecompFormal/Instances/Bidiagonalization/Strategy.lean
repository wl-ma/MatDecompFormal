import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Bidiagonalization.Details

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Bidiagonalization Strategy Core

This file implements the strategy-side skeleton required by the project's
rectangular descent template. The one-step unitary construction is isolated as
an oracle, while the recursive measure and head-tail slice are concrete.
-/

variable {𝕜 : Type v} [RCLike 𝕜]

/-- Row tail index obtained by removing the distinguished head row. -/
abbrev BidiagonalRowTail
    (m : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m] :=
  { i : m // i ≠ headElem (α := m) }

/-- Column tail index obtained by removing the distinguished head column. -/
abbrev BidiagonalColTail
    (n : Type u) [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :=
  { j : n // j ≠ headElem (α := n) }

theorem bidiagonal_tail_min_card_lt
    {m n : Type u}
    [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (_hm : 0 < Fintype.card m) (_hn : 0 < Fintype.card n) :
    Nat.min
      (Fintype.card (BidiagonalRowTail m))
      (Fintype.card (BidiagonalColTail n)) <
    Nat.min (Fintype.card m) (Fintype.card n) := by
  have hrow :
      Fintype.card (BidiagonalRowTail m) < Fintype.card m := by
    simpa [BidiagonalRowTail] using
      (Fintype.card_subtype_lt
        (p := fun i : m => i ≠ headElem (α := m))
        (x := headElem (α := m))
        (by simp))
  have hcol :
      Fintype.card (BidiagonalColTail n) < Fintype.card n := by
    simpa [BidiagonalColTail] using
      (Fintype.card_subtype_lt
        (p := fun j : n => j ≠ headElem (α := n))
        (x := headElem (α := n))
        (by simp))
  have hmin_row :
      Nat.min (Fintype.card (BidiagonalRowTail m)) (Fintype.card (BidiagonalColTail n)) <
        Fintype.card m :=
    lt_of_le_of_lt (Nat.min_le_left _ _) hrow
  have hmin_col :
      Nat.min (Fintype.card (BidiagonalRowTail m)) (Fintype.card (BidiagonalColTail n)) <
        Fintype.card n :=
    lt_of_le_of_lt (Nat.min_le_right _ _) hcol
  exact lt_min hmin_row hmin_col

/--
Boundary-ready state for one bidiagonalization step after head-tail reindexing.

The oracle-routed template uses a block-ready invariant: the first column is
zero below the head row and the first row tail is zero. This invariant is strong
enough for block-diagonal recursive lifting.
-/
def BidiagonalizationReady
    (m n : Type u) [Fintype m] [LinearOrder m] [Nonempty m]
    [DecidableEq m] [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n 𝕜) : Prop :=
  let A' := Matrix.reindex (headTailLexEquiv (α := m)) (headTailLexEquiv (α := n)) A
  (∀ i : BidiagonalRowTail m, A'.toBlocks₂₁ i () = 0) ∧
    ∀ j : BidiagonalColTail n,
      A'.toBlocks₁₂ () j = 0

def BidiagonalizationDescentReady
    (m n : Type u) [Fintype m] [LinearOrder m] [Nonempty m]
    [DecidableEq m] [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n 𝕜) : Prop :=
  BidiagonalizationReady m n A

noncomputable instance bidiagonalizationDescentReadyDecidable
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    DecidablePred (fun A : Matrix m n 𝕜 => BidiagonalizationDescentReady m n A) := by
  classical
  intro A
  exact inferInstance

/-- One-step unitary oracle for bidiagonalization readiness. -/
structure BidiagonalizationStepOracle
    (𝕜 : Type v) [RCLike 𝕜]
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  U : Matrix m n 𝕜 → Matrix m m 𝕜
  V : Matrix m n 𝕜 → Matrix n n 𝕜
  unitary_U : ∀ A, IsUnitaryMatrix (U A)
  unitary_V : ∀ A, IsUnitaryMatrix (V A)
  ready : ∀ A, BidiagonalizationReady m n ((U A)ᴴ * A * (V A))

/-- Two-sided unitary transformation driven by the one-step oracle. -/
noncomputable def bidiagonalizationTwoSidedUnitaryTransform
    (𝕜 : Type v) [RCLike 𝕜]
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (oracle : BidiagonalizationStepOracle 𝕜 m n) :
    Transformation (Matrix m n 𝕜) where
  T :=
    { UV : Matrix m m 𝕜 × Matrix n n 𝕜 //
      IsUnitaryMatrix UV.1 ∧ IsUnitaryMatrix UV.2 }
  Goal := BidiagonalizationDescentReady m n
  apply := fun UV A => UV.1.1ᴴ * A * UV.1.2
  find := fun A _h =>
    ⟨(oracle.U A, oracle.V A), oracle.unitary_U A, oracle.unitary_V A⟩
  find_spec := by
    intro A _h
    exact oracle.ready A

/-- Head-tail lower-right-block reduction for a ready bidiagonalization state. -/
noncomputable def bidiagonalizationHeadTailReduction
    (𝕜 : Type v) [RCLike 𝕜]
    (m n : Type u) [Fintype m] [LinearOrder m] [Nonempty m]
    [DecidableEq m] [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    ReductionMethod m n (BidiagonalRowTail m) (BidiagonalColTail n) 𝕜 :=
  SubmatrixMethod
    (headTailLexEquiv (α := m))
    (headTailLexEquiv (α := n))
    (BidiagonalizationDescentReady m n)

/-- Rectangular descent strategy core for bidiagonalization. -/
noncomputable def bidiagonalization_strategy_core
    (𝕜 : Type v) [RCLike 𝕜]
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationStepOracle 𝕜 m n) :
    RectStrategyCore 𝕜 where
  RowSliceIdx := fun {m n} fm dm om nm _ _ _ _ => @BidiagonalRowTail m fm dm om nm
  ColSliceIdx := fun {m n} _ _ _ _ fn dn on nn => @BidiagonalColTail n fn dn on nn
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
      { transform :=
          bidiagonalizationTwoSidedUnitaryTransform 𝕜 m n
            (oracle (m := m) (n := n))
        reduction := bidiagonalizationHeadTailReduction 𝕜 m n
        goal_is_sliceable := rfl
        μ := fun _ => Nat.min (Fintype.card m) (Fintype.card n)
        μ_slice := fun _ =>
          Nat.min (Fintype.card (BidiagonalRowTail m)) (Fintype.card (BidiagonalColTail n))
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          exact bidiagonal_tail_min_card_lt
            (m := m) (n := n)
            (by simpa using Fintype.card_pos_iff.mpr nm)
            (by simpa using Fintype.card_pos_iff.mpr nn) }
  μ_eq := by
    intro m n fm dm om nm fn dn on nn A
    rfl
  μ_slice_eq := by
    intro m n fm dm om nm fn dn on nn B
    rfl

end MatDecompFormal.Instances
