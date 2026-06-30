/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Schur.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Algebraic and Unitary Schur Strategy Core

This file implements the strategy-side skeletons for Schur triangularization.
The algebraic path uses arbitrary invertible similarities via
`SchurStepOracle`; the complex unitary path is separate and uses
`UnitarySchurStepOracle`.
-/

/-- Tail index obtained by removing the distinguished head element. -/
abbrev SchurTailIdx (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { a : ι // a ≠ headElem (α := ι) }

/--
The block-ready state for the Schur descent step: after head-tail reindexing,
the lower-left block vanishes.
-/
def SchurDescentReady
    (K ι : Type*) [Zero K] [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K) : Prop :=
  let A' := Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A
  A'.toBlocks₂₁ = 0

noncomputable instance schurDescentReadyDecidable
    (K ι : Type*) [Zero K] [Fintype ι] [LinearOrder ι] [Nonempty ι] :
    DecidablePred (SchurDescentReady K ι) := by
  classical
  intro A
  unfold SchurDescentReady
  infer_instance

/--
One-step Schur oracle: choose an invertible similarity putting the matrix into
lower-left-zero head-tail form.
-/
structure SchurStepOracle
    (K ι : Type*) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  P : Matrix ι ι K → Matrix ι ι K
  invertible_P : ∀ A, InvertibleMatrix (P A)
  ready : ∀ A, SchurDescentReady K ι ((P A)⁻¹ * A * (P A))

/--
One-step unitary Schur oracle.

This is the complex analogue of `SchurStepOracle`: it explicitly requires a
unitary similarity.  It is exposed separately because constructing `Q` requires
an orthonormal eigenvector/basis-completion step, not just algebraic basis
completion.
-/
structure UnitarySchurStepOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  Q : Matrix ι ι ℂ → Matrix ι ι ℂ
  unitary_Q : ∀ A, IsUnitaryMatrix (Q A)
  ready : ∀ A, SchurDescentReady ℂ ι ((Q A)ᴴ * A * (Q A))

/-- Invertible-similarity transformation driven by a `SchurStepOracle`. -/
noncomputable def schurSimilarityTransform
    (K ι : Type*) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (oracle : SchurStepOracle K ι) :
    Transformation (Matrix ι ι K) where
  T := { P : Matrix ι ι K // InvertibleMatrix P }
  Goal := SchurDescentReady K ι
  apply := fun P A => P.1⁻¹ * A * P.1
  find := fun A _h => ⟨oracle.P A, oracle.invertible_P A⟩
  find_spec := by
    intro A _h
    exact oracle.ready A

/-- Unitary-similarity transformation driven by a `UnitarySchurStepOracle`. -/
noncomputable def unitarySchurSimilarityTransform
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (oracle : UnitarySchurStepOracle ι) :
    Transformation (Matrix ι ι ℂ) where
  T := { Q : Matrix ι ι ℂ // IsUnitaryMatrix Q }
  Goal := SchurDescentReady ℂ ι
  apply := fun Q A => Q.1ᴴ * A * Q.1
  find := fun A _h => ⟨oracle.Q A, oracle.unitary_Q A⟩
  find_spec := by
    intro A _h
    exact oracle.ready A

/-- Head-tail lower-right-block reduction for a Schur-ready matrix. -/
noncomputable def schurHeadTailReduction
    (K ι : Type*) [Zero K] [Fintype ι] [LinearOrder ι] [Nonempty ι] :
    ReductionMethod ι ι (SchurTailIdx ι) (SchurTailIdx ι) K :=
  SubmatrixMethod
    (headTailEquiv (α := ι))
    (headTailEquiv (α := ι))
    (SchurDescentReady K ι)

/--
Schur strategy core parameterized by a family of one-step similarity oracles,
one for each nonempty finite linearly ordered index type.
-/
noncomputable def schur_strategy_core
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        SchurStepOracle K ι) :
    SquareStrategyCore K where
  SliceIdx := fun {ι} fι dι oι nι => @SchurTailIdx ι fι oι nι
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
      { transform := schurSimilarityTransform K ι (oracle (ι := ι))
        reduction := schurHeadTailReduction K ι
        goal_is_sliceable := rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (SchurTailIdx ι)
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hlt : Fintype.card (SchurTailIdx ι) < Fintype.card ι := by
            simpa [SchurTailIdx] using
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

/--
Unitary Schur strategy core parameterized by one unitary step oracle per
nonempty finite linearly ordered index type.
-/
noncomputable def unitary_schur_strategy_core
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        UnitarySchurStepOracle ι) :
    SquareStrategyCore ℂ where
  SliceIdx := fun {ι} fι dι oι nι => @SchurTailIdx ι fι oι nι
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
      { transform := unitarySchurSimilarityTransform ι (oracle (ι := ι))
        reduction := schurHeadTailReduction ℂ ι
        goal_is_sliceable := rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (SchurTailIdx ι)
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hlt : Fintype.card (SchurTailIdx ι) < Fintype.card ι := by
            simpa [SchurTailIdx] using
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
