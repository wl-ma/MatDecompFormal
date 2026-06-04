import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Abstractions.ReductionCombinators
import MatDecompFormal.Components.Reductions.ZeroColumn
import MatDecompFormal.Components.Transformations.Elementary.Pivot

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Components.Transformations.Elementary

/-!
# PLU Strategy Core

This file contains the active strategy-side core used by the current PLU
framework driver. It now performs a genuine pivot search on the head column,
then slices by a head-tail block decomposition in either the pivot-ready or
zero-column branch.
-/

variable {R : Type*}

/-- Tail index type obtained by removing the distinguished head element. -/
abbrev PLUTailIdx (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { a : ι // a ≠ headElem (α := ι) }

/-- Pivot-ready branch: the head pivot is nonzero, so recurse on the Schur complement. -/
def PLUPivotReady
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Zero R]
    (A : Matrix ι ι R) : Prop :=
  A (headElem (α := ι)) (headElem (α := ι)) ≠ 0

/-- Zero-column branch: the whole head column vanishes. -/
def PLUZeroColumnReady
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Zero R]
    (A : Matrix ι ι R) : Prop :=
  ∀ i, A i (headElem (α := ι)) = 0

/-- Combined PLU slicing goal used by the active pivot transform and reduction. -/
def PLUSliceable
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Zero R]
    (A : Matrix ι ι R) : Prop :=
  PLUPivotReady ι A ∨ PLUZeroColumnReady ι A

noncomputable def pluHeadTailPlain
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι R) : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R :=
  Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A

noncomputable def pluHeadInv
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Inv R]
    (A : Matrix ι ι R) : Matrix Unit Unit R :=
  fun _ _ => (A (headElem (α := ι)) (headElem (α := ι)))⁻¹

noncomputable def pluPivotLowerFactor
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Semiring R] [Inv R]
    (A : Matrix ι ι R) : Matrix (PLUTailIdx ι) Unit R :=
  let A' := pluHeadTailPlain ι A
  A'.toBlocks₂₁ * pluHeadInv ι A

noncomputable def pluSchurSlice
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Ring R] [Inv R]
    (A : Matrix ι ι R) : Matrix (PLUTailIdx ι) (PLUTailIdx ι) R :=
  let A' := pluHeadTailPlain ι A
  A'.toBlocks₂₂ - pluPivotLowerFactor ι A * A'.toBlocks₁₂

/-- Pivot-ready Schur-complement reduction. -/
noncomputable def pluPivotSchurReduction
    (ι : Type)
    [Fintype ι] [LinearOrder ι] [Nonempty ι] [Ring R] [Inv R] :
    ReductionMethod ι ι (PLUTailIdx ι) (PLUTailIdx ι) R where
  IsSliceable := PLUPivotReady ι
  slice := fun A _hA => pluSchurSlice ι A
  reconstruct := fun A _hA slice_sol =>
    let A' := pluHeadTailPlain ι A
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    let L₂₁ := pluPivotLowerFactor ι A
    let A₂₂ := slice_sol + L₂₁ * A₁₂
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).reindex (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm
  reconstruct_slice_eq := by
    intro A hA
    classical
    let A' : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R :=
      Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A
    let Hinv : Matrix Unit Unit R := pluHeadInv ι A
    have h_reconstructed_eq_A' :
        fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁
          (A'.toBlocks₂₂ - (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂ + (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂) = A' := by
      have h22 :
          A'.toBlocks₂₂ - (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂ + (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂ =
            A'.toBlocks₂₂ := by
        abel
      rw [h22]
      exact fromBlocks_toBlocks A'
    change
      (fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁
        (A'.toBlocks₂₂ - A'.toBlocks₂₁ * Hinv * A'.toBlocks₁₂ + A'.toBlocks₂₁ * Hinv * A'.toBlocks₁₂)).reindex
          (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm = A
    rw [h_reconstructed_eq_A']
    ext i j
    simp [A']

/-- Zero-column lower-right block reduction. -/
noncomputable def pluZeroColumnReduction
    (ι : Type)
    [Fintype ι] [LinearOrder ι] [Nonempty ι] [Zero R] :
    ReductionMethod ι ι (PLUTailIdx ι) (PLUTailIdx ι) R :=
  ZeroColumnMethod
    (headTailEquiv (α := ι))
    (headTailEquiv (α := ι))

/-- Active PLU reduction: pivot-ready branch first, zero-column branch second. -/
noncomputable def pluHeadTailReduction
    (ι : Type)
    [Fintype ι] [LinearOrder ι] [Nonempty ι] [Ring R] [Inv R] :
    ReductionMethod ι ι (PLUTailIdx ι) (PLUTailIdx ι) R :=
  ReductionMethod.try_else
    (pluPivotSchurReduction ι)
    (pluZeroColumnReduction ι)

/-- Active PLU strategy core: pivot into head position, then recurse on the tail block. -/
noncomputable def pluHeadTailSubmatrixStrategyCore [Ring R] [Inv R] : SquareStrategyCore R where
  SliceIdx := fun {ι} fι dι oι nι => @PLUTailIdx ι fι oι nι
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
      { transform := pivotToHeadOrZero
        reduction := pluHeadTailReduction ι
        goal_is_sliceable := by
          funext A
          apply propext
          constructor
          · intro h
            rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (by
                simpa [pluZeroColumnReduction, MatDecompFormal.Components.Reductions.ZeroColumnMethod,
                  headTailEquiv] using h)
          · intro h
            rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (by
                simpa [pluZeroColumnReduction, MatDecompFormal.Components.Reductions.ZeroColumnMethod,
                  headTailEquiv] using h)
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (PLUTailIdx ι)
        μ_mono := ?_
        slice_progress := ?_ }
    · intro A t
      simp
    · intro A hA
      have hlt : Fintype.card (PLUTailIdx ι) < Fintype.card ι := by
        simpa [PLUTailIdx] using
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
