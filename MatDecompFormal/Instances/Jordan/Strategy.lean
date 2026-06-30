/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
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

/-- Removing the distinguished head index strictly decreases cardinality. -/
theorem jordan_tail_card_lt
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    Fintype.card (JordanTailIdx ι) < Fintype.card ι := by
  simpa [JordanTailIdx] using
    (Fintype.card_subtype_lt
      (p := fun i : ι => i ≠ headElem (α := ι))
      (x := headElem (α := ι))
      (by simp))

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

/-- Slice selected by an arbitrary block/complement decomposition. -/
noncomputable def jordanBlockSlice
    {K : Type u} {ι β γ : Type u}
    (e : ι ≃ β ⊕ₗ γ) (A : Matrix ι ι K) :
    Matrix γ γ K :=
  (Matrix.reindex e e A).toBlocks₂₂

/--
Block-step payload for Jordan descent.  It records a whole removed block, the
recursive complement, and the block-diagonal equation after reindexing.

This is the interface needed when the algebra removes an entire Jordan block,
split companion block, or primary component at once instead of one head
coordinate.
-/
structure JordanBlockStepReady
    (K : Type u) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (β γ : Type u) [Fintype β] [DecidableEq β] [LinearOrder β]
    [Fintype γ] [DecidableEq γ] [LinearOrder γ]
    (A : Matrix ι ι K) where
  e : ι ≃ β ⊕ₗ γ
  head : Matrix β β K
  head_hasJordan : HasJordanMatrix head
  head_nonempty : Nonempty β
  block_eq :
    Matrix.reindex e e A =
      jordanBlockDiagLex head (jordanBlockSlice e A)

/--
In a block-step state, splitting of the full characteristic polynomial implies
splitting of the recursive complement characteristic polynomial.
-/
theorem jordan_block_tail_splits_of_blockStepReady
    {K : Type u} {ι β γ : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype β] [DecidableEq β] [LinearOrder β]
    [Fintype γ] [DecidableEq γ] [LinearOrder γ]
    {A : Matrix ι ι K}
    (ready : JordanBlockStepReady K ι β γ A)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    (jordanBlockSlice ready.e A).charpoly.Splits (RingHom.id K) := by
  classical
  have hcharReindex :
      (Matrix.reindex ready.e ready.e A).charpoly = A.charpoly :=
    Matrix.charpoly_reindex ready.e A
  have hcharBlock :
      (jordanBlockDiagLex ready.head (jordanBlockSlice ready.e A)).charpoly =
        ready.head.charpoly * (jordanBlockSlice ready.e A).charpoly := by
    calc
      (jordanBlockDiagLex ready.head (jordanBlockSlice ready.e A)).charpoly =
          (Matrix.fromBlocks ready.head 0 0 (jordanBlockSlice ready.e A) :
            Matrix (β ⊕ γ) (β ⊕ γ) K).charpoly := by
        simpa [jordanBlockDiagLex] using
          Matrix.charpoly_reindex
            (sumToLexEquiv β γ)
            (Matrix.fromBlocks ready.head 0 0 (jordanBlockSlice ready.e A) :
              Matrix (β ⊕ γ) (β ⊕ γ) K)
      _ = ready.head.charpoly * (jordanBlockSlice ready.e A).charpoly := by
        simp
  have hprod :
      ready.head.charpoly * (jordanBlockSlice ready.e A).charpoly = A.charpoly := by
    rw [← hcharBlock, ← ready.block_eq, hcharReindex]
  have htail_dvd : (jordanBlockSlice ready.e A).charpoly ∣ A.charpoly := by
    refine ⟨ready.head.charpoly, ?_⟩
    rw [mul_comm, hprod]
  exact Polynomial.splits_of_splits_of_dvd (RingHom.id K)
    (Matrix.charpoly_monic A).ne_zero hsplit htail_dvd

/--
A structured block step lifts a recursive Jordan witness on the complement to
a Jordan witness for the full matrix.
-/
theorem jordanLiftReady_of_blockStepReady
    {K : Type u} {ι β γ : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype β] [DecidableEq β] [LinearOrder β]
    [Fintype γ] [DecidableEq γ] [LinearOrder γ]
    {A : Matrix ι ι K}
    (ready : JordanBlockStepReady K ι β γ A)
    (hTail :
      (jordanBlockSlice ready.e A).charpoly.Splits (RingHom.id K) →
        HasJordanMatrix (jordanBlockSlice ready.e A)) :
    A.charpoly.Splits (RingHom.id K) → HasJordanMatrix A := by
  intro hsplit
  have hTailJordan : HasJordanMatrix (jordanBlockSlice ready.e A) :=
    hTail (jordan_block_tail_splits_of_blockStepReady ready hsplit)
  have hBlock :
      HasJordanMatrix (jordanBlockDiagLex ready.head (jordanBlockSlice ready.e A)) :=
    hasJordanMatrix_blockDiag_lex ready.head (jordanBlockSlice ready.e A)
      ready.head_hasJordan
      hTailJordan
  have hReindexed :
      HasJordanMatrix (Matrix.reindex ready.e ready.e A) := by
    rw [ready.block_eq]
    exact hBlock
  have hBack := hasJordanMatrix_reindex (e := ready.e.symm) hReindexed
  simpa [reindex_reindex] using hBack

/-- A block step strictly decreases dimension when the removed block is nonempty. -/
theorem jordan_block_slice_card_lt
    {K : Type u} {ι β γ : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype β] [DecidableEq β] [LinearOrder β]
    [Fintype γ] [DecidableEq γ] [LinearOrder γ]
    {A : Matrix ι ι K}
    (ready : JordanBlockStepReady K ι β γ A) :
    Fintype.card γ < Fintype.card ι := by
  have hcard : Fintype.card ι = Fintype.card (β ⊕ₗ γ) :=
    Fintype.card_congr ready.e
  have hβpos : 0 < Fintype.card β :=
    Fintype.card_pos_iff.mpr ready.head_nonempty
  rw [hcard, Fintype.card_lex, Fintype.card_sum]
  omega

/--
For a head-tail block diagonal state, splitting of the full characteristic
polynomial implies splitting of the recursive tail characteristic polynomial.
-/
theorem jordan_tail_splits_of_headTailBlockEq
    {K : Type u} {ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι K}
    (head : Matrix Unit Unit K)
    (block_eq :
      Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A =
        jordanBlockDiagLex head (jordanTailSlice ι A))
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    (jordanTailSlice ι A).charpoly.Splits (RingHom.id K) := by
  classical
  have hcharReindex :
      (Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A).charpoly =
        A.charpoly :=
    Matrix.charpoly_reindex (headTailLexEquiv (α := ι)) A
  have hcharBlock :
      (jordanBlockDiagLex head (jordanTailSlice ι A)).charpoly =
        head.charpoly * (jordanTailSlice ι A).charpoly := by
    calc
      (jordanBlockDiagLex head (jordanTailSlice ι A)).charpoly =
          (Matrix.fromBlocks head 0 0 (jordanTailSlice ι A) :
            Matrix (Unit ⊕ JordanTailIdx ι) (Unit ⊕ JordanTailIdx ι) K).charpoly := by
        simpa [jordanBlockDiagLex] using
          Matrix.charpoly_reindex
            (sumToLexEquiv Unit (JordanTailIdx ι))
            (Matrix.fromBlocks head 0 0 (jordanTailSlice ι A) :
              Matrix (Unit ⊕ JordanTailIdx ι) (Unit ⊕ JordanTailIdx ι) K)
      _ = head.charpoly * (jordanTailSlice ι A).charpoly := by
        simp
  have hprod :
      head.charpoly * (jordanTailSlice ι A).charpoly = A.charpoly := by
    rw [← hcharBlock, ← block_eq, hcharReindex]
  have htail_dvd : (jordanTailSlice ι A).charpoly ∣ A.charpoly := by
    refine ⟨head.charpoly, ?_⟩
    rw [mul_comm, hprod]
  exact Polynomial.splits_of_splits_of_dvd (RingHom.id K)
    (Matrix.charpoly_monic A).ne_zero hsplit htail_dvd

/--
Structured one-step lift payload for the head-tail square driver.

The transformed matrix is, after lexicographic head-tail reindexing, a
one-dimensional Jordan head block plus the recursive tail slice.  The payload
is concrete algebraic data; tail splitting is derived from the block equation.
-/
structure JordanHeadTailBlockReady
    (K : Type u) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K) where
  head : Matrix Unit Unit K
  block_eq :
    Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A =
      jordanBlockDiagLex head (jordanTailSlice ι A)

theorem jordanLiftReady_of_headTailBlockReady
    {K : Type u} {ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι K}
    (ready : JordanHeadTailBlockReady K ι A) :
    JordanLiftReady K ι A := by
  intro hsplit hTail
  have hTailJordan : HasJordanMatrix (jordanTailSlice ι A) :=
    hTail (jordan_tail_splits_of_headTailBlockEq ready.head ready.block_eq hsplit)
  have hBlock :
      HasJordanMatrix
        (jordanBlockDiagLex ready.head (jordanTailSlice ι A)) :=
    hasJordanMatrix_blockDiag_lex ready.head (jordanTailSlice ι A)
      (hasJordanMatrix_of_isJordanMatrix (isJordanMatrix_unit ready.head))
      hTailJordan
  have hReindexed :
      HasJordanMatrix
        (Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A) := by
    rw [ready.block_eq]
    exact hBlock
  have hBack :=
    hasJordanMatrix_reindex (e := (headTailLexEquiv (α := ι)).symm) hReindexed
  simpa [reindex_reindex] using hBack

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

/--
Structured one-step oracle.  This is the algebraic target for discharging the
Jordan recursion: the step must produce concrete head-tail block data, not just
an arbitrary proof of `JordanDescentReady`.
-/
structure JordanStructuredStepOracle
    (K ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  P : Matrix ι ι K → Matrix ι ι K
  invertible_P : ∀ A, InvertibleMatrix (P A)
  head_tail_ready :
    ∀ A, JordanHeadTailBlockReady K ι ((P A)⁻¹ * A * (P A))

/-- Convert structured head-tail block data to the framework step oracle. -/
noncomputable def JordanStructuredStepOracle.toStepOracle
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (oracle : JordanStructuredStepOracle K ι) :
    JordanStepOracle K ι where
  P := oracle.P
  invertible_P := oracle.invertible_P
  ready := fun A =>
    jordanLiftReady_of_headTailBlockReady (oracle.head_tail_ready A)

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
          simpa using (jordan_tail_card_lt (ι := ι)) }
  μ_eq := by
    intro ι fι dι oι nι A
    rfl
  μ_slice_eq := by
    intro ι fι dι oι nι B
    rfl

end MatDecompFormal.Instances
