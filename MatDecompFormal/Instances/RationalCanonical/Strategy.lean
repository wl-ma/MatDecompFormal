/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Framework.Reindex
import MatDecompFormal.Instances.RationalCanonical.Details

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Rational Canonical Form Strategy Core

The concrete cyclic-summand construction is isolated in
`RationalCanonicalStepOracle`. The strategy itself is the project square
descent template: similarity transform, head-tail slice, progress by removing
the head index, transport, and lift.
-/

/-- Tail index obtained by removing the distinguished head element. -/
abbrev RationalCanonicalTailIdx
    (ι : Type u) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { i : ι // i ≠ headElem (α := ι) }

/-- Lower-right head-tail slice used by the rational-canonical descent. -/
noncomputable def rationalCanonicalTailSlice
    (ι : Type u) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {K : Type v} (A : Matrix ι ι K) :
    Matrix (RationalCanonicalTailIdx ι) (RationalCanonicalTailIdx ι) K :=
  A.submatrix
    (fun i : RationalCanonicalTailIdx ι =>
      (headTailEquiv (α := ι)).symm (Sum.inr i))
    (fun j : RationalCanonicalTailIdx ι =>
      (headTailEquiv (α := ι)).symm (Sum.inr j))

/--
Readiness predicate: a recursive rational-canonical witness for the tail slice
can be lifted to the full matrix.
-/
def RationalCanonicalLiftReady
    (K : Type v) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K) : Prop :=
  HasRationalCanonical (rationalCanonicalTailSlice ι A) →
    HasRationalCanonical A

/-- Slicability predicate consumed by the square strategy. -/
def RationalCanonicalDescentReady
    (K : Type v) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K) : Prop :=
  RationalCanonicalLiftReady K ι A

/--
The lower-right block of the lexicographic head-tail reindexing is exactly the
tail slice consumed by the square descent driver.
-/
theorem rationalCanonicalTailSlice_eq_toBlocks₂₂
    {K : Type v} {ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K) :
    (Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A).toBlocks₂₂ =
      rationalCanonicalTailSlice ι A := by
  ext i j
  change A ((headTailLexEquiv (α := ι)).symm (Sum.inrₗ i))
        ((headTailLexEquiv (α := ι)).symm (Sum.inrₗ j)) = A ↑i ↑j
  simp

/--
Structured one-step lift payload: after the head-tail reindexing, the matrix is
a block diagonal rational-canonical head block and the recursive tail slice.

This is the concrete shape expected from a cyclic-summand module bridge; the
raw `RationalCanonicalLiftReady` consumed by the framework is derived from this
data below.
-/
structure RationalCanonicalHeadTailBlockReady
    (K : Type v) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K) where
  head : Matrix Unit Unit K
  head_isRC : IsRationalCanonicalMatrix head
  block_eq :
    Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A =
      rationalCanonicalBlockDiagLex head (rationalCanonicalTailSlice ι A)

/--
For the current one-index head-tail driver, a block equation with a `Unit`
head block is enough to produce structured readiness: every `Unit × Unit`
head block is the companion block of `X - a`.
-/
def rationalCanonicalHeadTailBlockReady_of_unit_block_eq
    {K : Type v} {ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι K}
    (head : Matrix Unit Unit K)
    (block_eq :
      Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A =
        rationalCanonicalBlockDiagLex head (rationalCanonicalTailSlice ι A)) :
    RationalCanonicalHeadTailBlockReady K ι A where
  head := head
  head_isRC := isRationalCanonicalMatrix_unit head
  block_eq := block_eq

/--
A structured head-tail block decomposition provides the lift predicate required
by the square descent template.
-/
theorem rationalCanonicalLiftReady_of_headTailBlockReady
    {K : Type v} {ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι K}
    (ready : RationalCanonicalHeadTailBlockReady K ι A) :
    RationalCanonicalLiftReady K ι A := by
  intro hTail
  have hBlock :
      HasRationalCanonical
        (rationalCanonicalBlockDiagLex ready.head (rationalCanonicalTailSlice ι A)) :=
    hasRationalCanonical_blockDiag_lex ready.head (rationalCanonicalTailSlice ι A)
      (hasRationalCanonical_of_isRationalCanonicalMatrix ready.head_isRC) hTail
  have hReindexed :
      HasRationalCanonical
        (Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A) := by
    rw [ready.block_eq]
    exact hBlock
  have hBack :=
    hasRationalCanonical_reindex (e := (headTailLexEquiv (α := ι)).symm) hReindexed
  simpa [reindex_reindex] using hBack

noncomputable instance rationalCanonicalDescentReadyDecidable
    (K : Type v) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    DecidablePred (RationalCanonicalDescentReady K ι) := by
  classical
  intro A
  exact inferInstance

/--
One-step oracle for the rational-canonical descent.

Future algebraic work should construct this from the `K[X]` module-structure
theorem by isolating one cyclic summand and proving the companion-block lift.
-/
structure RationalCanonicalStepOracle
    (K : Type v) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  P : Matrix ι ι K → Matrix ι ι K
  Pinv : Matrix ι ι K → Matrix ι ι K
  inverse_P : ∀ A, HasMatrixInverse (P A) (Pinv A)
  liftReady :
    ∀ A, RationalCanonicalLiftReady K ι ((Pinv A) * A * (P A))

/-- Similarity transform driven by a rational-canonical step oracle. -/
noncomputable def rationalCanonicalSimilarityTransform
    (K : Type v) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (oracle : RationalCanonicalStepOracle K ι) :
    Transformation (Matrix ι ι K) where
  T := { PP : Matrix ι ι K × Matrix ι ι K // HasMatrixInverse PP.1 PP.2 }
  Goal := RationalCanonicalDescentReady K ι
  apply := fun PP A => PP.1.2 * A * PP.1.1
  find := fun A _h => ⟨(oracle.P A, oracle.Pinv A), oracle.inverse_P A⟩
  find_spec := by
    intro A _h
    exact oracle.liftReady A

/-- Head-tail lower-right-block reduction for a ready matrix. -/
noncomputable def rationalCanonicalHeadTailReduction
    (K : Type v) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    ReductionMethod ι ι
      (RationalCanonicalTailIdx ι) (RationalCanonicalTailIdx ι) K :=
  SubmatrixMethod
    (headTailEquiv (α := ι))
    (headTailEquiv (α := ι))
    (RationalCanonicalDescentReady K ι)

/-- Rational-canonical square strategy core. -/
noncomputable def rationalCanonical_strategy_core
    (K : Type v) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        RationalCanonicalStepOracle K ι) :
    SquareStrategyCore K where
  SliceIdx := fun {ι} fι _ oι nι => @RationalCanonicalTailIdx ι fι oι nι
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
      { transform := rationalCanonicalSimilarityTransform K ι (oracle (ι := ι))
        reduction := rationalCanonicalHeadTailReduction K ι
        goal_is_sliceable := rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (RationalCanonicalTailIdx ι)
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hlt : Fintype.card (RationalCanonicalTailIdx ι) <
              Fintype.card ι := by
            simpa [RationalCanonicalTailIdx] using
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
