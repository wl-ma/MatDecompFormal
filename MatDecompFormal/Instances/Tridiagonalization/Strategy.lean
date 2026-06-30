/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Tridiagonalization.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Tridiagonalization Strategy Core

This file defines the strict square-descent skeleton for unitary
tridiagonalization.  The hard Householder/Givens step is isolated as a unitary
similarity oracle.
-/

/-- Tail index obtained by removing the distinguished head element. -/
abbrev TridiagonalTailIdx (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { i : ι // i ≠ headElem (α := ι) }

/-- Head-tail block view used by the concrete tridiagonal boundary condition. -/
noncomputable def tridiagonalHeadTailMatrix
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) :
    Matrix (Unit ⊕ TridiagonalTailIdx ι) (Unit ⊕ TridiagonalTailIdx ι) ℂ :=
  Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A

/-- Lower-right head-tail slice used by the tridiagonalization descent. -/
noncomputable def tridiagonalTailSlice
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) :
    Matrix (TridiagonalTailIdx ι) (TridiagonalTailIdx ι) ℂ :=
  A.submatrix
    (fun i : TridiagonalTailIdx ι => (headTailEquiv (α := ι)).symm (Sum.inr i))
    (fun j : TridiagonalTailIdx ι => (headTailEquiv (α := ι)).symm (Sum.inr j))

/-- The recursive slice is exactly the lower-right head-tail block. -/
theorem tridiagonalTailSlice_eq_lowerRightBlock
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) :
    tridiagonalTailSlice ι A =
      (tridiagonalHeadTailMatrix ι A).toBlocks₂₂ := by
  rfl

/-- Removing the head index strictly decreases the square measure. -/
theorem tridiagonal_tail_card_lt
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    Fintype.card (TridiagonalTailIdx ι) < Fintype.card ι := by
  simpa [TridiagonalTailIdx] using
    (Fintype.card_subtype_lt
      (p := fun i : ι => i ≠ headElem (α := ι))
      (x := headElem (α := ι))
      (by simp))

/--
Concrete first-column readiness for tridiagonalization.

In head-tail form this says that, inside the lower-left block, every entry
below the first tail coordinate is zero.  For Hermitian matrices the matching
first-row zeros follow by conjugate symmetry.
-/
def TridiagonalizationReady
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) : Prop :=
  let A' := tridiagonalHeadTailMatrix ι A
  ∀ i : TridiagonalTailIdx ι,
    0 < finiteOrderRank (TridiagonalTailIdx ι) i →
      A'.toBlocks₂₁ i () = 0

lemma tridiagonalTailSlice_isHermitian
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (tridiagonalTailSlice ι A).IsHermitian :=
  hA.submatrix _

/--
Lift-ready state for the tridiagonalization descent.

This is the precise proof obligation needed by the recursive driver: after the
one-step unitary transform, a tridiagonalization of the lower-right tail slice
lifts to a tridiagonalization of the full matrix.
-/
def TridiagonalizationLiftReady
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) : Prop :=
  Tridiagonalization_P (SquareUniverse.ofMatrix (tridiagonalTailSlice ι A)) →
    Tridiagonalization_P (SquareUniverse.ofMatrix A)

/-- Slicability predicate used by the strategy. -/
def TridiagonalizationDescentReady
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) : Prop :=
  TridiagonalizationLiftReady ι A

noncomputable instance tridiagonalizationDescentReadyDecidable
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    DecidablePred (fun A : Matrix ι ι ℂ => TridiagonalizationDescentReady ι A) := by
  classical
  intro A
  exact inferInstance

/--
One-step unitary similarity oracle. It supplies a unitary transform that puts
the active matrix in a lift-ready state.
-/
structure TridiagonalizationSimilarityOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  Q : Matrix ι ι ℂ → Matrix ι ι ℂ
  unitary_Q : ∀ A, IsUnitaryMatrix (Q A)
  descentReady :
    ∀ A, TridiagonalizationDescentReady ι ((Q A)ᴴ * A * (Q A))

/-!
Plan-facing oracle with the same strength as the strategy's slicability
predicate.  Future Householder/Givens files should construct this structure.
-/
structure TridiagonalizationStepOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  Q : Matrix ι ι ℂ → Matrix ι ι ℂ
  unitary_Q : ∀ A, IsUnitaryMatrix (Q A)
  liftReady :
    ∀ A, TridiagonalizationLiftReady ι ((Q A)ᴴ * A * (Q A))

/--
Concrete plan-facing oracle: a one-step unitary similarity that establishes
the explicit head-tail tridiagonal boundary condition.

The bridge to `TridiagonalizationStepOracle` needs a block lift theorem.  This
is separated so Householder/Givens construction work can target the concrete
boundary predicate without weakening the square-descent driver.
-/
structure TridiagonalizationBlockReadyOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  Q : Matrix ι ι ℂ → Matrix ι ι ℂ
  unitary_Q : ∀ A, IsUnitaryMatrix (Q A)
  ready : ∀ A, TridiagonalizationReady ι ((Q A)ᴴ * A * (Q A))

def TridiagonalizationBlockLiftTheorem
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] : Prop :=
  ∀ A : Matrix ι ι ℂ,
    TridiagonalizationReady ι A →
      TridiagonalizationLiftReady ι A

noncomputable def tridiagonalizationStepOracleOfBlockReadyOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (blockLift : TridiagonalizationBlockLiftTheorem ι)
    (oracle : TridiagonalizationBlockReadyOracle ι) :
    TridiagonalizationStepOracle ι where
  Q := oracle.Q
  unitary_Q := oracle.unitary_Q
  liftReady := by
    intro A
    exact blockLift ((oracle.Q A)ᴴ * A * (oracle.Q A)) (oracle.ready A)

noncomputable def tridiagonalizationSimilarityOracleOfStepOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (step : TridiagonalizationStepOracle ι) :
    TridiagonalizationSimilarityOracle ι where
  Q := step.Q
  unitary_Q := step.unitary_Q
  descentReady := step.liftReady

/-- Unitary similarity transformation driven by a tridiagonalization oracle. -/
noncomputable def tridiagonalizationUnitaryTransform
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (oracle : TridiagonalizationSimilarityOracle ι) :
    Transformation (Matrix ι ι ℂ) where
  T := { Q : Matrix ι ι ℂ // IsUnitaryMatrix Q }
  Goal := TridiagonalizationDescentReady ι
  apply := fun Q A => Q.1ᴴ * A * Q.1
  find := fun A _h => ⟨oracle.Q A, oracle.unitary_Q A⟩
  find_spec := by
    intro A _h
    exact oracle.descentReady A

/-- Head-tail lower-right-block reduction for a lift-ready matrix. -/
noncomputable def tridiagonalizationHeadTailReduction
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    ReductionMethod ι ι (TridiagonalTailIdx ι) (TridiagonalTailIdx ι) ℂ :=
  SubmatrixMethod
    (headTailEquiv (α := ι))
    (headTailEquiv (α := ι))
    (TridiagonalizationDescentReady ι)

/-- Tridiagonalization strategy core parameterized by one oracle per index type. -/
noncomputable def tridiagonalization_strategy_core
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        TridiagonalizationSimilarityOracle ι) :
    SquareStrategyCore ℂ where
  SliceIdx := fun {ι} fι _ oι nι => @TridiagonalTailIdx ι fι oι nι
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
      { transform := tridiagonalizationUnitaryTransform ι (oracle (ι := ι))
        reduction := tridiagonalizationHeadTailReduction ι
        goal_is_sliceable := rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (TridiagonalTailIdx ι)
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hlt : Fintype.card (TridiagonalTailIdx ι) < Fintype.card ι :=
            tridiagonal_tail_card_lt (ι := ι)
          simpa using hlt }
  μ_eq := by
    intro ι fι dι oι nι A
    rfl
  μ_slice_eq := by
    intro ι fι dι oι nι B
    rfl

end MatDecompFormal.Instances
