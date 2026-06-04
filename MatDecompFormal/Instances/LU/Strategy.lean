import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.PLU.Strategy
import MatDecompFormal.Instances.LU.Details
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Abstractions

/-!
# LU Strategy Core

The LU strategy is the no-pivot Schur-complement descent. Unlike PLU, the
transformation is identity; the recursive theorem is conditional on explicit
`LURecursivePivotReady` evidence.
-/

variable {R : Type*}

/-- LU uses the same head-tail tail index as PLU. -/
abbrev LUTailIdx (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  PLUTailIdx ι

/-- The head pivot is nonzero, so no row permutation is needed. -/
def LUPivotReady
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Zero R]
    (A : Matrix ι ι R) : Prop :=
  PLUPivotReady ι A

/-- Head-tail reindexing reused from PLU. -/
noncomputable def luHeadTailPlain
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι R) : Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R :=
  pluHeadTailPlain ι A

/-- No-pivot lower multiplier reused from PLU's pivot branch. -/
noncomputable def luPivotLowerFactor
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Semiring R] [Inv R]
    (A : Matrix ι ι R) : Matrix (LUTailIdx ι) Unit R :=
  pluPivotLowerFactor ι A

/-- No-pivot Schur-complement slice. -/
noncomputable def luSchurSlice
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Ring R] [Inv R]
    (A : Matrix ι ι R) : Matrix (LUTailIdx ι) (LUTailIdx ι) R :=
  pluSchurSlice ι A

/-- Recursive no-pivot LU readiness: every recursive head pivot is nonzero. -/
noncomputable def LURecursivePivotReady
    {R : Type*} [DivisionRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) : Prop :=
  if hbase : Fintype.card ι ≤ 1 then
    True
  else
    have hcard : 1 < Fintype.card ι := Nat.lt_of_not_ge hbase
    letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
    letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hcard
    LUPivotReady ι A ∧ LURecursivePivotReady (luSchurSlice ι A)
termination_by Fintype.card ι
decreasing_by
  classical
  have hcard : 1 < Fintype.card ι := Nat.lt_of_not_ge hbase
  letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
  letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hcard
  have hlt : Fintype.card (LUTailIdx ι) < Fintype.card ι := by
    simpa [LUTailIdx, PLUTailIdx] using
      (Fintype.card_subtype_lt
        (p := fun a : ι => a ≠ headElem (α := ι))
        (x := headElem (α := ι))
        (by simp))
  exact hlt

/-- User-facing no-pivot LU hypothesis, stated as a recursive determinant criterion.

At every descent step, the current `1 × 1` leading principal block has nonzero
determinant, and the Schur complement satisfies the same condition.  The theorem
`hasNoZeroLUPivots_iff_recursivePivotReady` below is the bridge from this
determinant API to the internal pivot-readiness predicate consumed by the
descent driver.
-/
noncomputable def HasNoZeroLUPivots
    {R : Type*} [Field R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) : Prop :=
  if hbase : Fintype.card ι ≤ 1 then
    True
  else
    have hcard : 1 < Fintype.card ι := Nat.lt_of_not_ge hbase
    letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
    letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hcard
    (luHeadTailPlain ι A).toBlocks₁₁.det ≠ 0 ∧
      HasNoZeroLUPivots (luSchurSlice ι A)
termination_by Fintype.card ι
decreasing_by
  classical
  have hcard : 1 < Fintype.card ι := Nat.lt_of_not_ge hbase
  letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
  letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hcard
  have hlt : Fintype.card (LUTailIdx ι) < Fintype.card ι := by
    simpa [LUTailIdx, PLUTailIdx] using
      (Fintype.card_subtype_lt
        (p := fun a : ι => a ≠ headElem (α := ι))
        (x := headElem (α := ι))
        (by simp))
  exact hlt

lemma luRecursivePivotReady_of_card_le_one
    {R : Type*} [DivisionRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R} (hbase : Fintype.card ι ≤ 1) :
    LURecursivePivotReady A := by
  rw [LURecursivePivotReady]
  simp [hbase]

lemma hasNoZeroLUPivots_of_card_le_one
    {R : Type*} [Field R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R} (hbase : Fintype.card ι ≤ 1) :
    HasNoZeroLUPivots A := by
  rw [HasNoZeroLUPivots]
  simp [hbase]

lemma luRecursivePivotReady_step_iff
    {R : Type*} [DivisionRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Nontrivial ι]
    {A : Matrix ι ι R} (hbase : ¬ Fintype.card ι ≤ 1) :
    LURecursivePivotReady A ↔
      LUPivotReady ι A ∧ LURecursivePivotReady (luSchurSlice ι A) := by
  rw [LURecursivePivotReady]
  simp [hbase]

lemma hasNoZeroLUPivots_step_iff
    {R : Type*} [Field R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Nontrivial ι]
    {A : Matrix ι ι R} (hbase : ¬ Fintype.card ι ≤ 1) :
    HasNoZeroLUPivots A ↔
      (luHeadTailPlain ι A).toBlocks₁₁.det ≠ 0 ∧
        HasNoZeroLUPivots (luSchurSlice ι A) := by
  rw [HasNoZeroLUPivots]
  simp [hbase]

lemma luHeadPivotDet_ne_zero_iff
    {R : Type*} [Field R]
    {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι R) :
    (luHeadTailPlain ι A).toBlocks₁₁.det ≠ 0 ↔ LUPivotReady ι A := by
  classical
  rw [Matrix.det_eq_elem_of_subsingleton _ ()]
  simp [LUPivotReady, PLUPivotReady, luHeadTailPlain, pluHeadTailPlain, Matrix.toBlocks₁₁]

/--
The determinant-style public LU hypothesis is equivalent to the internal
recursive pivot-readiness predicate used by the descent driver.
-/
theorem hasNoZeroLUPivots_iff_recursivePivotReady
    {R : Type*} [Field R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R} :
    HasNoZeroLUPivots A ↔ LURecursivePivotReady A := by
  classical
  by_cases hbase : Fintype.card ι ≤ 1
  · rw [HasNoZeroLUPivots, LURecursivePivotReady]
    simp [hbase]
  · have hcard : 1 < Fintype.card ι := Nat.lt_of_not_ge hbase
    letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
    letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hcard
    rw [hasNoZeroLUPivots_step_iff (A := A) hbase,
      luRecursivePivotReady_step_iff (A := A) hbase]
    exact and_congr (luHeadPivotDet_ne_zero_iff A)
      (hasNoZeroLUPivots_iff_recursivePivotReady (A := luSchurSlice ι A))
termination_by Fintype.card ι
decreasing_by
  classical
  have hcard : 1 < Fintype.card ι := Nat.lt_of_not_ge hbase
  letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
  letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hcard
  have hlt : Fintype.card (LUTailIdx ι) < Fintype.card ι := by
    simpa [LUTailIdx, PLUTailIdx] using
      (Fintype.card_subtype_lt
        (p := fun a : ι => a ≠ headElem (α := ι))
        (x := headElem (α := ι))
        (by simp))
  exact hlt

/-- Pivot-ready Schur-complement reduction for no-pivot LU. -/
noncomputable def luSchurReduction
    (ι : Type*)
    [Fintype ι] [LinearOrder ι] [Nonempty ι] [Ring R] [Inv R] :
    ReductionMethod ι ι (LUTailIdx ι) (LUTailIdx ι) R where
  IsSliceable := fun _ => True
  slice := fun A _hA => luSchurSlice ι A
  reconstruct := fun A _hA slice_sol =>
    let A' := luHeadTailPlain ι A
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    let L₂₁ := luPivotLowerFactor ι A
    let A₂₂ := slice_sol + L₂₁ * A₁₂
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).reindex
      (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm
  reconstruct_slice_eq := by
    intro A _
    classical
    let A' : Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R :=
      Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A
    let Hinv : Matrix Unit Unit R := pluHeadInv ι A
    have h_reconstructed_eq_A' :
        fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁
          (A'.toBlocks₂₂ - (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂ +
            (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂) = A' := by
      have h22 :
          A'.toBlocks₂₂ - (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂ +
              (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂ = A'.toBlocks₂₂ := by
        abel
      rw [h22]
      exact fromBlocks_toBlocks A'
    change
      (fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁
        (A'.toBlocks₂₂ - A'.toBlocks₂₁ * Hinv * A'.toBlocks₁₂ +
          A'.toBlocks₂₁ * Hinv * A'.toBlocks₁₂)).reindex
          (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm = A
    rw [h_reconstructed_eq_A']
    ext i j
    simp [A']

/-- No-pivot LU strategy core: identity transform, then Schur-complement slice. -/
noncomputable def lu_strategy_core [DivisionRing R] : SquareStrategyCore R where
  SliceIdx := fun {ι} fι dι oι nι => @LUTailIdx ι fι oι nι
  sliceFintype := by
    intro ι fι dι oι nι
    infer_instance
  sliceDecEq := by
    intro ι fι dι oι nι
    infer_instance
  sliceLinearOrder := by
    intro ι fι dι oι nι
    infer_instance
  strategy := by
    intro ι fι dι oι nι
    refine
      { transform := trivialSquareTransform _
        reduction := luSchurReduction ι
        goal_is_sliceable := by rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (LUTailIdx ι)
        μ_mono := ?_
        slice_progress := ?_ }
    · intro A t
      cases t
      simp
    · intro A hA
      have hlt : Fintype.card (LUTailIdx ι) < Fintype.card ι := by
        simpa [LUTailIdx, PLUTailIdx] using
          (Fintype.card_subtype_lt
            (p := fun a : ι => a ≠ headElem (α := ι))
            (x := headElem (α := ι))
            (by simp))
      simpa using hlt
  μ_eq := by
    intro ι fι dι oι nι A
    rfl
  μ_slice_eq := by
    intro ι fι dι oι nι B
    rfl

end MatDecompFormal.Instances
