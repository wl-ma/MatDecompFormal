import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Normal.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Normal Matrix Strategy Core

This file implements the strategy-side skeleton for normal spectral
decomposition. The hard spectral step is isolated in `NormalSimilarityOracle`:
given a matrix, it supplies a unitary similarity that puts the matrix into a
head-tail block-ready form.

The oracle is not an unsupported placeholder. It is an explicit parameter to the conditional
framework theorem, and the remaining project work is to construct it from the
complex spectral/eigenvector lemmas.
-/

/-- Tail index obtained by removing the distinguished head element. -/
abbrev NormalTailIdx (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { a : ι // a ≠ headElem (α := ι) }

/--
The block-ready state for the normal-matrix descent step: after reindexing by
the head-tail equivalence, both off-diagonal blocks vanish. Normality is kept in
the predicate because the recursive target consumes it on the tail.
-/
def NormalBlockReady
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) : Prop :=
  IsNormalMatrix A ∧
    let A' := Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A
    A'.toBlocks₁₂ = 0 ∧ A'.toBlocks₂₁ = 0

noncomputable instance normalBlockReadyDecidable
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    DecidablePred (fun A : Matrix ι ι ℂ => NormalBlockReady ι A) := by
  classical
  intro A
  exact inferInstance

/--
The high-level spectral step required by the strategy: every matrix can be
unitarily transformed into a block-ready matrix.

This is the main mathematical hook left by the first implementation pass.
-/
structure NormalSimilarityOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  Q : Matrix ι ι ℂ → Matrix ι ι ℂ
  unitary_Q : ∀ A, IsUnitaryMatrix (Q A)
  blockReady : ∀ A, NormalBlockReady ι ((Q A)ᴴ * A * (Q A))

/-- Unitary similarity transformation driven by a `NormalSimilarityOracle`. -/
noncomputable def normalUnitarySimilarityTransform
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (oracle : NormalSimilarityOracle ι) :
    Transformation (Matrix ι ι ℂ) where
  T := { Q : Matrix ι ι ℂ // IsUnitaryMatrix Q }
  Goal := NormalBlockReady ι
  apply := fun Q A => Q.1ᴴ * A * Q.1
  find := fun A _h => ⟨oracle.Q A, oracle.unitary_Q A⟩
  find_spec := by
    intro A _h
    exact oracle.blockReady A

/-- Head-tail lower-right-block reduction for a block-ready normal matrix. -/
noncomputable def normalHeadTailReduction
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :
    ReductionMethod ι ι (NormalTailIdx ι) (NormalTailIdx ι) ℂ :=
  SubmatrixMethod
    (headTailEquiv (α := ι))
    (headTailEquiv (α := ι))
    (NormalBlockReady ι)

/--
Normal spectral strategy core parameterized by a family of unitary-similarity
oracles, one for each nonempty finite linearly ordered index type.
-/
noncomputable def normal_strategy_core
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι) :
    SquareStrategyCore ℂ where
  SliceIdx := fun {ι} fι dι oι nι => @NormalTailIdx ι fι oι nι
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
      { transform := normalUnitarySimilarityTransform ι (oracle (ι := ι))
        reduction := normalHeadTailReduction ι
        goal_is_sliceable := rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (NormalTailIdx ι)
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hlt : Fintype.card (NormalTailIdx ι) < Fintype.card ι := by
            simpa [NormalTailIdx] using
              (Fintype.card_subtype_lt
                (p := fun a : ι => a ≠ headElem (α := ι))
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
