import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Hessenberg.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Hessenberg Strategy Core

This file defines the head-tail strategy skeleton for Hessenberg reduction. The
hard one-step column-zeroing construction is isolated in
`HessenbergSimilarityOracle`; the strategy itself is assembled through the
square descent framework.
-/

/-- Tail index obtained by removing the distinguished head element. -/
abbrev HessenbergTailIdx (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { i : ι // i ≠ headElem (α := ι) }

/-- Lower-right head-tail slice used by the Hessenberg descent. -/
noncomputable def hessenbergTailSlice
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} (A : Matrix ι ι R) :
    Matrix (HessenbergTailIdx ι) (HessenbergTailIdx ι) R :=
  A.submatrix
    (fun i : HessenbergTailIdx ι => (headTailEquiv (α := ι)).symm (Sum.inr i))
    (fun j : HessenbergTailIdx ι => (headTailEquiv (α := ι)).symm (Sum.inr j))

/--
Readiness predicate for the Hessenberg slice.

The predicate is deliberately proof-relevant: a ready matrix is one for which a
Hessenberg witness for the lower-right head-tail slice can be lifted to a
Hessenberg witness for the full matrix. Concrete column-zeroing/block-shape
lemmas should discharge this predicate.
-/
def HessenbergLiftReady
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Semiring R] (A : Matrix ι ι R) : Prop :=
  HasHessenberg (hessenbergTailSlice ι A) → HasHessenberg A

/-- Slicability predicate used by the strategy. -/
def HessenbergDescentReady
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Semiring R] (A : Matrix ι ι R) : Prop :=
  HessenbergLiftReady ι A

noncomputable instance hessenbergDescentReadyDecidable
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Semiring R] :
    DecidablePred (fun A : Matrix ι ι R => HessenbergDescentReady ι A) := by
  classical
  intro A
  exact inferInstance

/--
One-step similarity oracle. It supplies an invertible similarity transform that
puts the active matrix in a sliceable Hessenberg-ready state.
-/
structure HessenbergSimilarityOracle
    (R ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Semiring R] where
  P : Matrix ι ι R → Matrix ι ι R
  Pinv : Matrix ι ι R → Matrix ι ι R
  inverse_P : ∀ A, HasMatrixInverse (P A) (Pinv A)
  descentReady : ∀ A, HessenbergDescentReady ι ((Pinv A) * A * (P A))

/--
Plan-facing one-step oracle. After the similarity transform, it provides exactly
the lift-ready condition required by the recursive slice.
-/
structure HessenbergStepOracle
    (R ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Semiring R] where
  P : Matrix ι ι R → Matrix ι ι R
  Pinv : Matrix ι ι R → Matrix ι ι R
  inverse_P : ∀ A, HasMatrixInverse (P A) (Pinv A)
  liftReady : ∀ A, HessenbergLiftReady ι ((Pinv A) * A * (P A))

noncomputable def hessenbergSimilarityOracleOfStepOracle
    (R ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Semiring R] (step : HessenbergStepOracle R ι) :
    HessenbergSimilarityOracle R ι where
  P := step.P
  Pinv := step.Pinv
  inverse_P := step.inverse_P
  descentReady := step.liftReady

/-- Similarity transform driven by a Hessenberg one-step oracle. -/
noncomputable def hessenbergSimilarityTransform
    (R ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Semiring R]
    (oracle : HessenbergSimilarityOracle R ι) :
    Transformation (Matrix ι ι R) where
  T := { PP : Matrix ι ι R × Matrix ι ι R // HasMatrixInverse PP.1 PP.2 }
  Goal := HessenbergDescentReady ι
  apply := fun PP A => PP.1.2 * A * PP.1.1
  find := fun A _h => ⟨(oracle.P A, oracle.Pinv A), oracle.inverse_P A⟩
  find_spec := by
    intro A _h
    exact oracle.descentReady A

/-- Head-tail lower-right-block reduction for a Hessenberg-ready matrix. -/
noncomputable def hessenbergHeadTailReduction
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (R : Type*) [Semiring R] :
    ReductionMethod ι ι (HessenbergTailIdx ι) (HessenbergTailIdx ι) R :=
  SubmatrixMethod
    (headTailEquiv (α := ι))
    (headTailEquiv (α := ι))
    (HessenbergDescentReady ι)

/-- Hessenberg strategy core parameterized by one similarity oracle per index type. -/
noncomputable def hessenberg_strategy_core
    {R : Type u} [Semiring R]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        HessenbergSimilarityOracle R ι) :
    SquareStrategyCore R where
  SliceIdx := fun {ι} fι _ oι nι => @HessenbergTailIdx ι fι oι nι
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
    exact
      { transform := hessenbergSimilarityTransform R ι (oracle (ι := ι))
        reduction := hessenbergHeadTailReduction ι R
        goal_is_sliceable := rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (HessenbergTailIdx ι)
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hlt : Fintype.card (HessenbergTailIdx ι) < Fintype.card ι := by
            simpa [HessenbergTailIdx] using
              (Fintype.card_subtype_lt
                (p := fun i : ι => i ≠ headElem (α := ι))
                (x := headElem (α := ι))
                (by simp))
          simpa using hlt }
  μ_eq := by
    intro ι fι dι oι nι A
    rfl
  μ_slice_eq := by
    intro ι fι dι oι nι B
    rfl

end MatDecompFormal.Instances
