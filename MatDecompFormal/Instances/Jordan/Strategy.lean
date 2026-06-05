import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Jordan.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Jordan Strategy Core

The concrete one-step Jordan block isolation is isolated in `JordanStepOracle`.
The strategy itself is the project square descent template.
-/

/-- Tail index obtained by removing the distinguished head element. -/
abbrev JordanTailIdx (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { i : ι // i ≠ headElem (α := ι) }

/-- Lower-right head-tail slice used by the Jordan descent. -/
noncomputable def jordanTailSlice
    (ι : Type u) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {K : Type u} (A : Matrix ι ι K) :
    Matrix (JordanTailIdx ι) (JordanTailIdx ι) K :=
  A.submatrix
    (fun i : JordanTailIdx ι =>
      (headTailEquiv (α := ι)).symm (Sum.inr i))
    (fun j : JordanTailIdx ι =>
      (headTailEquiv (α := ι)).symm (Sum.inr j))

/--
Readiness predicate: a recursive Jordan theorem for the tail slice can be
lifted to the full matrix, assuming the full matrix characteristic polynomial
splits.
-/
def JordanLiftReady
    (K : Type u) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K) : Prop :=
  A.charpoly.Splits (RingHom.id K) →
    Jordan_P (SquareUniverse.ofMatrix (jordanTailSlice ι A)) →
      HasJordanMatrix A

/-- Slicability predicate consumed by the square strategy. -/
def JordanDescentReady
    (K : Type u) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K) : Prop :=
  JordanLiftReady K ι A

noncomputable instance jordanDescentReadyDecidable
    (K : Type u) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    DecidablePred (JordanDescentReady K ι) := by
  classical
  intro A
  exact inferInstance

/--
One-step Jordan oracle: choose an invertible similarity putting the matrix into
a state from which the recursive tail Jordan theorem lifts to the whole matrix.
-/
structure JordanStepOracle
    (K ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  P : Matrix ι ι K → Matrix ι ι K
  invertible_P : ∀ A, InvertibleMatrix (P A)
  ready : ∀ A, JordanDescentReady K ι ((P A)⁻¹ * A * (P A))

/-- Invertible-similarity transformation driven by a `JordanStepOracle`. -/
noncomputable def jordanSimilarityTransform
    (K ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (oracle : JordanStepOracle K ι) :
    Transformation (Matrix ι ι K) where
  T := { P : Matrix ι ι K // InvertibleMatrix P }
  Goal := JordanDescentReady K ι
  apply := fun P A => P.1⁻¹ * A * P.1
  find := fun A _h => ⟨oracle.P A, oracle.invertible_P A⟩
  find_spec := by
    intro A _h
    exact oracle.ready A

/-- Head-tail lower-right-block reduction for a Jordan-ready matrix. -/
noncomputable def jordanHeadTailReduction
    (K ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    ReductionMethod ι ι (JordanTailIdx ι) (JordanTailIdx ι) K :=
  SubmatrixMethod
    (headTailEquiv (α := ι))
    (headTailEquiv (α := ι))
    (JordanDescentReady K ι)

/--
Jordan strategy core parameterized by a family of one-step similarity oracles,
one for each nonempty finite linearly ordered index type.
-/
noncomputable def jordan_strategy_core
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        JordanStepOracle K ι) :
    SquareStrategyCore K where
  SliceIdx := fun {ι} fι dι oι nι => @JordanTailIdx ι fι oι nι
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
      { transform := jordanSimilarityTransform K ι (oracle (ι := ι))
        reduction := jordanHeadTailReduction K ι
        goal_is_sliceable := rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (JordanTailIdx ι)
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hlt : Fintype.card (JordanTailIdx ι) < Fintype.card ι := by
            simpa [JordanTailIdx] using
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
