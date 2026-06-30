/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Framework.UniverseDecompositionSquareSubtype
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Hessenberg.Details
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.AdjoinRoot

universe u v w u' v'

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open scoped Polynomial

/-!
# Rational Canonical Form Details

This file contains the matrix-level target predicate for rational canonical
form. The concrete companion-block algebra is represented as data; the descent
driver and its oracle live in the later files.
-/

variable {K : Type w} {ι : Type u}

/--
Standard companion matrix for a monic polynomial, indexed by
`Fin p.natDegree`.

With this convention, the matrix sends the cyclic basis vector `e_j` to
`e_{j+1}` for `j + 1 < p.natDegree`; the last column records the negative lower
coefficients of `p`.
-/
def companionMatrixFin [Field K] (p : K[X]) :
    Matrix (Fin p.natDegree) (Fin p.natDegree) K :=
  fun i j =>
    if (j : Nat) + 1 = i then
      1
    else if (j : Nat) = p.natDegree - 1 then
      -p.coeff i
    else
      0

/--
Data witnessing that a matrix has rational canonical block form.

The matrix-level block shape is not stored as an arbitrary proof token.  Instead
`blockIndexEquiv` explicitly decomposes the ambient matrix index into a
dependent family of block coordinates, and `block_form` says that after this
reindexing the matrix is the block diagonal matrix of the corresponding
companion matrices.
-/
structure RationalCanonicalMatrixData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (C : Matrix ι ι K) where
  block : Type u
  [fintype_block : Fintype block]
  [decEq_block : DecidableEq block]
  invariantFactor : block → K[X]
  invariantFactor_monic : ∀ b, (invariantFactor b).Monic
  blockSize : block → Nat
  blockSize_pos : ∀ b, 0 < blockSize b
  blockSize_eq_natDegree : ∀ b, blockSize b = (invariantFactor b).natDegree
  total_size : (∑ b, blockSize b) = Fintype.card ι
  blockIndexEquiv : ι ≃ (b : block) × Fin (blockSize b)
  block_form :
    Matrix.reindex blockIndexEquiv blockIndexEquiv C =
      Matrix.blockDiagonal' fun b =>
        Matrix.reindex
          (finCongr (blockSize_eq_natDegree b).symm)
          (finCongr (blockSize_eq_natDegree b).symm)
          (companionMatrixFin (invariantFactor b))

attribute [instance] RationalCanonicalMatrixData.fintype_block
attribute [instance] RationalCanonicalMatrixData.decEq_block

/-- Matrix-level rational-canonical predicate. -/
def IsRationalCanonicalMatrix
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (C : Matrix ι ι K) : Prop :=
  Nonempty (RationalCanonicalMatrixData C)

/--
Entrywise statement that `C` is the companion matrix of `p`, up to a reindexing
of the matrix indices by `Fin p.natDegree`.
-/
def IsCompanionMatrix
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (C : Matrix ι ι K) (p : K[X]) : Prop :=
  ∃ e : ι ≃ Fin p.natDegree,
    Matrix.reindex e e C = companionMatrixFin p

/--
Single companion-block payload.  This is the local target for the cyclic
summand produced by a one-step module-structure bridge.
-/
def SingleCompanionBlockForm
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (C : Matrix ι ι K) (p : K[X]) : Prop :=
  p.Monic ∧ 0 < p.natDegree ∧ p.natDegree = Fintype.card ι ∧
    IsCompanionMatrix C p

theorem singleCompanionBlockForm_card_eq_natDegree
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]}
    (h : SingleCompanionBlockForm C p) :
    Fintype.card ι = p.natDegree :=
  h.2.2.1.symm

/--
Promote a verified single companion block to rational-canonical matrix data.
The proof obligation is now the explicit companion-matrix predicate above,
while the block count, monicity, and degree/size match are fixed.
-/
theorem isRationalCanonicalMatrix_singleCompanion
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (C : Matrix ι ι K) (p : K[X])
    (h : SingleCompanionBlockForm C p) :
    IsRationalCanonicalMatrix C := by
  classical
  refine ⟨{
    block := PUnit
    invariantFactor := fun _ => p
    invariantFactor_monic := fun _ => h.1
    blockSize := fun _ => p.natDegree
    blockSize_pos := fun _ => ?_
    blockSize_eq_natDegree := fun _ => ?_
    total_size := ?_
    blockIndexEquiv := ?_
    block_form := ?_
  }⟩
  · exact h.2.1
  · rfl
  · simpa using h.2.2.1
  · let e := Classical.choose h.2.2.2
    exact
      { toFun := fun i => ⟨PUnit.unit, e i⟩
        invFun := fun x => e.symm x.2
        left_inv := by
          intro i
          simp
        right_inv := by
          intro x
          cases x.1
          simp }
  · let e := Classical.choose h.2.2.2
    have he := Classical.choose_spec h.2.2.2
    ext x y
    cases x with
    | mk bx ix =>
      cases y with
      | mk bY iy =>
        cases bx
        cases bY
        have hentry := congrFun (congrFun he ix) iy
        simpa [Matrix.reindex_apply, Matrix.blockDiagonal'] using hentry

/-- The standard companion matrix is a companion matrix for its polynomial. -/
theorem isCompanionMatrix_companionMatrixFin
    [Field K] (p : K[X]) :
    IsCompanionMatrix (K := K) (ι := Fin p.natDegree)
      (companionMatrixFin p) p := by
  refine ⟨Equiv.refl _, ?_⟩
  ext i j
  simp [Matrix.reindex_apply]

/--
The standard companion matrix gives a verified single companion block whenever
the polynomial is monic and has positive degree.
-/
theorem singleCompanionBlockForm_companionMatrixFin
    [Field K] (p : K[X]) (hmonic : p.Monic) (hpos : 0 < p.natDegree) :
    SingleCompanionBlockForm (K := K) (ι := Fin p.natDegree)
      (companionMatrixFin p) p := by
  refine ⟨hmonic, hpos, ?_, isCompanionMatrix_companionMatrixFin p⟩
  simp

/--
For a monic polynomial, multiplication by the adjoined root in the standard
power basis is the companion matrix used by this development.
-/
theorem isCompanionMatrix_adjoinRoot_leftMulMatrix_powerBasis
    [Field K] (p : K[X]) (hmonic : p.Monic) :
    IsCompanionMatrix (K := K) (ι := Fin p.natDegree)
      ((Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hmonic).basis)
        (AdjoinRoot.powerBasis' hmonic).gen) p := by
  refine ⟨Equiv.refl _, ?_⟩
  ext i j
  have hminpolyGen : (AdjoinRoot.powerBasis' hmonic).minpolyGen = p := by
    rw [PowerBasis.minpolyGen_eq]
    rw [AdjoinRoot.powerBasis'_gen]
    simpa [hmonic.leadingCoeff] using (AdjoinRoot.minpoly_root hmonic.ne_zero)
  rw [PowerBasis.leftMulMatrix]
  change
    (if (j : Nat) + 1 = (AdjoinRoot.powerBasis' hmonic).dim then
      -((AdjoinRoot.powerBasis' hmonic).minpolyGen).coeff (i : Nat)
    else if (i : Nat) = (j : Nat) + 1 then 1 else 0) =
      companionMatrixFin p i j
  simp only [hminpolyGen, AdjoinRoot.powerBasis'_dim]
  by_cases hlast : (j : Nat) + 1 = p.natDegree
  · have hnot_shift : ¬(j : Nat) + 1 = (i : Nat) := by
      intro hji
      have hi_eq : (i : Nat) = p.natDegree := by omega
      exact Nat.ne_of_lt i.2 hi_eq
    unfold companionMatrixFin
    rw [if_pos hlast, if_neg hnot_shift]
    have hjlast : (j : Nat) = p.natDegree - 1 := by omega
    rw [if_pos hjlast]
  · have hnot_last : ¬(j : Nat) = p.natDegree - 1 := by
      intro hj
      have : (j : Nat) + 1 = p.natDegree := by omega
      exact hlast this
    by_cases hshift : (i : Nat) = (j : Nat) + 1
    · have hshift' : (j : Nat) + 1 = (i : Nat) := by omega
      unfold companionMatrixFin
      rw [if_neg hlast, if_pos hshift, if_pos hshift']
    · have hshift' : ¬(j : Nat) + 1 = (i : Nat) := by omega
      unfold companionMatrixFin
      rw [if_neg hlast, if_neg hshift, if_neg hshift', if_neg hnot_last]

/--
The standard power basis of `AdjoinRoot p` supplies a verified single companion
block for every monic positive-degree polynomial `p`.
-/
theorem singleCompanionBlockForm_adjoinRoot_leftMulMatrix_powerBasis
    [Field K] (p : K[X]) (hmonic : p.Monic) (hpos : 0 < p.natDegree) :
    SingleCompanionBlockForm (K := K) (ι := Fin p.natDegree)
      ((Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hmonic).basis)
        (AdjoinRoot.powerBasis' hmonic).gen) p := by
  refine ⟨hmonic, hpos, ?_, ?_⟩
  · simp
  · exact isCompanionMatrix_adjoinRoot_leftMulMatrix_powerBasis p hmonic

/--
Universe-lifted version of the `AdjoinRoot` power-basis companion block.  This
is the block-index shape used by higher-universe matrix decompositions.
-/
theorem singleCompanionBlockForm_adjoinRoot_leftMulMatrix_powerBasis_ulift
    [Field K] (p : K[X]) (hmonic : p.Monic) (hpos : 0 < p.natDegree) :
    SingleCompanionBlockForm (K := K) (ι := ULift.{u, 0} (Fin p.natDegree))
      (Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm
        ((Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hmonic).basis)
          (AdjoinRoot.powerBasis' hmonic).gen)) p := by
  have hfin : SingleCompanionBlockForm (K := K) (ι := Fin p.natDegree)
      ((Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hmonic).basis)
        (AdjoinRoot.powerBasis' hmonic).gen) p :=
    singleCompanionBlockForm_adjoinRoot_leftMulMatrix_powerBasis p hmonic hpos
  rcases hfin with ⟨hp, hdeg, hcard, hcomp⟩
  refine ⟨hp, hdeg, ?_, ?_⟩
  · simpa using hcard
  · rcases hcomp with ⟨e, he⟩
    refine ⟨Equiv.ulift.trans e, ?_⟩
    simpa [Matrix.reindex, Function.comp_def] using he

/-- The standard companion matrix has characteristic polynomial `p`. -/
theorem companionMatrixFin_charpoly
    [Field K] {p : K[X]} (hmonic : p.Monic) :
    (companionMatrixFin p).charpoly = p := by
  classical
  let pb := AdjoinRoot.powerBasis' hmonic
  let L : Matrix (Fin p.natDegree) (Fin p.natDegree) K :=
    (Algebra.leftMulMatrix pb.basis) pb.gen
  have hIsComp :
      IsCompanionMatrix (K := K) (ι := Fin p.natDegree) L p := by
    simpa [L, pb] using
      isCompanionMatrix_adjoinRoot_leftMulMatrix_powerBasis (K := K) p hmonic
  let e := Classical.choose hIsComp
  have he : Matrix.reindex e e L = companionMatrixFin p :=
    Classical.choose_spec hIsComp
  have hcharComp : (companionMatrixFin p).charpoly = L.charpoly := by
    have hcharReindex : (Matrix.reindex e e L).charpoly = L.charpoly :=
      Matrix.charpoly_reindex e L
    rwa [he] at hcharReindex
  have hcharLeft : L.charpoly = minpoly K pb.gen := by
    simpa [L, pb] using (charpoly_leftMulMatrix (R := K) pb)
  have hmin : minpoly K pb.gen = p := by
    have hminpolyGen : pb.minpolyGen = p := by
      rw [PowerBasis.minpolyGen_eq]
      rw [AdjoinRoot.powerBasis'_gen]
      simpa [hmonic.leadingCoeff] using
        (AdjoinRoot.minpoly_root hmonic.ne_zero)
    simpa [pb] using hminpolyGen
  exact hcharComp.trans (hcharLeft.trans hmin)

/-- A verified single companion block has characteristic polynomial `p`. -/
theorem singleCompanionBlockForm_charpoly
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]}
    (h : SingleCompanionBlockForm C p) :
    C.charpoly = p := by
  classical
  rcases h.2.2.2 with ⟨e, he⟩
  have hcharReindex : (Matrix.reindex e e C).charpoly = C.charpoly :=
    Matrix.charpoly_reindex e C
  rw [he] at hcharReindex
  exact hcharReindex.symm.trans (companionMatrixFin_charpoly (K := K) h.1)

/-- Single companion-block form is invariant under index reindexing. -/
theorem singleCompanionBlockForm_reindex
    [Field K]
    {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    (e : ι ≃ κ) {C : Matrix ι ι K} {p : K[X]}
    (h : SingleCompanionBlockForm C p) :
    SingleCompanionBlockForm (Matrix.reindex e e C) p := by
  rcases h with ⟨hmonic, hpos, hcard, hcomp⟩
  refine ⟨hmonic, hpos, ?_, ?_⟩
  · simpa [Fintype.card_congr e] using hcard
  · rcases hcomp with ⟨toFin, htoFin⟩
    refine ⟨e.symm.trans toFin, ?_⟩
    ext i j
    simpa [Matrix.reindex_apply] using congrFun (congrFun htoFin i) j

/-- The standard companion matrix is rational-canonical matrix data. -/
theorem isRationalCanonicalMatrix_companionMatrixFin
    [Field K] (p : K[X]) (hmonic : p.Monic) (hpos : 0 < p.natDegree) :
    IsRationalCanonicalMatrix (companionMatrixFin p) :=
  isRationalCanonicalMatrix_singleCompanion
    (companionMatrixFin p) p
    (singleCompanionBlockForm_companionMatrixFin p hmonic hpos)

/--
Every one-dimensional block is the companion matrix of the linear polynomial
`X - a`, where `a` is its unique entry.
-/
theorem isCompanionMatrix_unit_X_sub_C
    [Field K] (C : Matrix Unit Unit K) :
    IsCompanionMatrix C (Polynomial.X - Polynomial.C (C () ())) := by
  let p : K[X] := Polynomial.X - Polynomial.C (C () ())
  have hdeg : p.natDegree = 1 := by
    simp [p]
  have hpos : 0 < p.natDegree := by
    rw [hdeg]
    decide
  let e : Unit ≃ Fin p.natDegree := {
    toFun := fun _ => ⟨0, hpos⟩
    invFun := fun _ => ()
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      apply Fin.ext
      have hx : x.1 < 1 := by
        simpa [hdeg] using x.2
      omega
  }
  refine ⟨e, ?_⟩
  ext i j
  have hi0 : (i : Nat) = 0 := by
    have hx : i.1 < 1 := by
      simpa [hdeg] using i.2
    omega
  have hj0 : (j : Nat) = 0 := by
    have hx : j.1 < 1 := by
      simpa [hdeg] using j.2
    omega
  simp [e, companionMatrixFin, p, hdeg, hi0, hj0]

/--
Every one-dimensional block has rational-canonical matrix data, with invariant
factor `X - a`.
-/
theorem singleCompanionBlockForm_unit_X_sub_C
    [Field K] (C : Matrix Unit Unit K) :
    SingleCompanionBlockForm C (Polynomial.X - Polynomial.C (C () ())) := by
  let p : K[X] := Polynomial.X - Polynomial.C (C () ())
  have hdeg : p.natDegree = 1 := by
    simp [p]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [p] using Polynomial.monic_X_sub_C (C () ())
  · rw [hdeg]
    decide
  · simp
  · simpa [p] using isCompanionMatrix_unit_X_sub_C C

/-- Every one-dimensional block is rational-canonical. -/
theorem isRationalCanonicalMatrix_unit
    [Field K] (C : Matrix Unit Unit K) :
    IsRationalCanonicalMatrix C :=
  isRationalCanonicalMatrix_singleCompanion C
    (Polynomial.X - Polynomial.C (C () ()))
    (singleCompanionBlockForm_unit_X_sub_C C)

/-- Rational-canonical matrix data is invariant under reindexing. -/
theorem isRationalCanonicalMatrix_reindex
    [Field K]
    {ι κ : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    (e : ι ≃ κ) {C : Matrix ι ι K}
    (hC : IsRationalCanonicalMatrix C) :
    IsRationalCanonicalMatrix (Matrix.reindex e e C) := by
  rcases hC with ⟨d⟩
  refine ⟨{
    block := d.block
    invariantFactor := d.invariantFactor
    invariantFactor_monic := d.invariantFactor_monic
    blockSize := d.blockSize
    blockSize_pos := d.blockSize_pos
    blockSize_eq_natDegree := d.blockSize_eq_natDegree
    total_size := ?_
    blockIndexEquiv := e.symm.trans d.blockIndexEquiv
    block_form := ?_
  }⟩
  · simpa [Fintype.card_congr e] using d.total_size
  · ext x y
    simpa [Matrix.reindex_apply] using congrFun (congrFun d.block_form x) y

/-- Block-diagonal matrix on the lexicographic sum index used by head-tail descent. -/
noncomputable def rationalCanonicalBlockDiagLex
    [Zero K] {α : Type u} {β : Type v}
    (A : Matrix α α K) (B : Matrix β β K) :
    Matrix (α ⊕ₗ β) (α ⊕ₗ β) K :=
  Matrix.reindex (sumToLexEquiv α β) (sumToLexEquiv α β)
    (Matrix.fromBlocks A 0 0 B : Matrix (α ⊕ β) (α ⊕ β) K)

/-- Reindexing both blocks reindexes the lexicographic block diagonal matrix. -/
theorem rationalCanonicalBlockDiagLex_reindex
    [Zero K]
    {α : Type u} {α' : Type u'} {β : Type v} {β' : Type v'}
    (eα : α ≃ α') (eβ : β ≃ β')
    (A : Matrix α α K) (B : Matrix β β K) :
    Matrix.reindex
        ((sumToLexEquiv α β).symm.trans
          ((Equiv.sumCongr eα eβ).trans
            (sumToLexEquiv α' β')))
        ((sumToLexEquiv α β).symm.trans
          ((Equiv.sumCongr eα eβ).trans
            (sumToLexEquiv α' β')))
        (rationalCanonicalBlockDiagLex A B) =
      rationalCanonicalBlockDiagLex
        (Matrix.reindex eα eα A)
        (Matrix.reindex eβ eβ B) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [rationalCanonicalBlockDiagLex, Matrix.reindex_apply]

/--
Block-diagonal rational-canonical matrices combine to another
rational-canonical matrix.

The matrix is indexed by the lexicographic sum because this is the index shape
used by the project head-tail descent template.
-/
theorem isRationalCanonicalMatrix_blockDiag_lex
    [Field K]
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [LinearOrder α] [LinearOrder β]
    (C₁ : Matrix α α K) (C₂ : Matrix β β K)
    (h₁ : IsRationalCanonicalMatrix C₁) (h₂ : IsRationalCanonicalMatrix C₂) :
    IsRationalCanonicalMatrix (rationalCanonicalBlockDiagLex C₁ C₂) := by
  classical
  rcases h₁ with ⟨d₁⟩
  rcases h₂ with ⟨d₂⟩
  refine ⟨{
    block := ULift.{max u v, u} d₁.block ⊕ ULift.{max u v, v} d₂.block
    invariantFactor := fun b => match b with
      | Sum.inl b => d₁.invariantFactor b.down
      | Sum.inr b => d₂.invariantFactor b.down
    invariantFactor_monic := ?_
    blockSize := fun b => match b with
      | Sum.inl b => d₁.blockSize b.down
      | Sum.inr b => d₂.blockSize b.down
    blockSize_pos := ?_
    blockSize_eq_natDegree := ?_
    total_size := ?_
    blockIndexEquiv := ?_
    block_form := ?_
  }⟩
  · intro b
    cases b with
    | inl b => exact d₁.invariantFactor_monic b.down
    | inr b => exact d₂.invariantFactor_monic b.down
  · intro b
    cases b with
    | inl b => exact d₁.blockSize_pos b.down
    | inr b => exact d₂.blockSize_pos b.down
  · intro b
    cases b with
    | inl b => exact d₁.blockSize_eq_natDegree b.down
    | inr b => exact d₂.blockSize_eq_natDegree b.down
  · have hsum₁ : (∑ b : ULift.{max u v, u} d₁.block, d₁.blockSize b.down) =
        ∑ b : d₁.block, d₁.blockSize b := by
      exact Fintype.sum_equiv Equiv.ulift (fun b => d₁.blockSize b.down)
        (fun b => d₁.blockSize b) (fun b => rfl)
    have hsum₂ : (∑ b : ULift.{max u v, v} d₂.block, d₂.blockSize b.down) =
        ∑ b : d₂.block, d₂.blockSize b := by
      exact Fintype.sum_equiv Equiv.ulift (fun b => d₂.blockSize b.down)
        (fun b => d₂.blockSize b) (fun b => rfl)
    simp [Fintype.card_sum, Fintype.card_lex, hsum₁, hsum₂,
      d₁.total_size, d₂.total_size]
  · exact
      (sumToLexEquiv α β).symm.trans <|
        (Equiv.sumCongr d₁.blockIndexEquiv d₂.blockIndexEquiv).trans <|
        (Equiv.sumCongr
          (Equiv.sigmaCongr Equiv.ulift.symm
            (fun b => Equiv.cast (by simp)))
          (Equiv.sigmaCongr Equiv.ulift.symm
            (fun b => Equiv.cast (by simp)))).trans <|
          (Equiv.sumSigmaDistrib
            (fun b : ULift.{max u v, u} d₁.block ⊕
                ULift.{max u v, v} d₂.block =>
              Fin <|
                match b with
                | Sum.inl b => d₁.blockSize b.down
                | Sum.inr b => d₂.blockSize b.down)).symm
  · ext x y
    rcases x with ⟨bx, ix⟩
    rcases y with ⟨bY, iy⟩
    cases bx with
    | inl bx =>
      cases bY with
      | inl bRight =>
        have hentry := congrFun (congrFun d₁.block_form ⟨bx.down, ix⟩) ⟨bRight.down, iy⟩
        simpa [rationalCanonicalBlockDiagLex, Matrix.reindex_apply,
          Matrix.blockDiagonal'] using hentry
      | inr bRight =>
        simp [rationalCanonicalBlockDiagLex, Matrix.reindex_apply,
          Matrix.blockDiagonal']
    | inr bx =>
      cases bY with
      | inl bRight =>
        simp [rationalCanonicalBlockDiagLex, Matrix.reindex_apply,
          Matrix.blockDiagonal']
      | inr bRight =>
        have hentry := congrFun (congrFun d₂.block_form ⟨bx.down, ix⟩) ⟨bRight.down, iy⟩
        simpa [rationalCanonicalBlockDiagLex, Matrix.reindex_apply,
          Matrix.blockDiagonal'] using hentry

/-- Similarity target for rational canonical form. -/
def HasRationalCanonical
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ P : Matrix ι ι K, ∃ Pinv : Matrix ι ι K, ∃ C : Matrix ι ι K,
    HasMatrixInverse P Pinv ∧
    IsRationalCanonicalMatrix C ∧
    A = P * C * Pinv

/--
Explicit block-data witness for rational canonical form.

This Prop-level wrapper exposes the final similarity matrices and an actual
`RationalCanonicalMatrixData` payload for the canonical matrix.  It is
equivalent to `HasRationalCanonical`, but avoids hiding the block payload behind
only the final public theorem.
-/
def RationalCanonicalBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ P : Matrix ι ι K, ∃ Pinv : Matrix ι ι K, ∃ C : Matrix ι ι K,
    HasMatrixInverse P Pinv ∧
    (∃ _data : RationalCanonicalMatrixData C, True) ∧
    A = P * C * Pinv

/--
Route-tagged rational-canonical block data.

The tag records whether a theorem came from the one-index framework, the
module bridge, or the cyclic block bridge.  The payload remains the explicit
final block data.
-/
def RationalCanonicalBridgeBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (tag : String) (A : Matrix ι ι K) : Prop :=
  tag = tag ∧ RationalCanonicalBlockData A

abbrev RationalCanonicalTrace
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  RationalCanonicalBlockData A

theorem hasRationalCanonical_of_blockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K} :
    RationalCanonicalBlockData A → HasRationalCanonical A := by
  intro hA
  rcases hA with ⟨P, Pinv, C, hInv, hData, hEq⟩
  rcases hData with ⟨data, _⟩
  exact ⟨P, Pinv, C, hInv, ⟨data⟩, hEq⟩

theorem rationalCanonicalBlockData_of_hasRationalCanonical
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K} :
    HasRationalCanonical A → RationalCanonicalBlockData A := by
  intro hA
  rcases hA with ⟨P, Pinv, C, hInv, hC, hEq⟩
  rcases hC with ⟨data⟩
  exact ⟨P, Pinv, C, hInv, ⟨data, trivial⟩, hEq⟩

theorem rationalCanonicalBlockData_of_bridgeBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {tag : String} {A : Matrix ι ι K} :
    RationalCanonicalBridgeBlockData tag A → RationalCanonicalBlockData A := by
  intro hA
  exact hA.2

theorem rationalCanonicalBridgeBlockData_of_blockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (tag : String) {A : Matrix ι ι K} :
    RationalCanonicalBlockData A → RationalCanonicalBridgeBlockData tag A := by
  intro hA
  exact ⟨rfl, hA⟩

theorem hasRationalCanonical_of_rationalCanonicalBridgeBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {tag : String} {A : Matrix ι ι K} :
    RationalCanonicalBridgeBlockData tag A → HasRationalCanonical A :=
  hasRationalCanonical_of_blockData ∘ rationalCanonicalBlockData_of_bridgeBlockData

/-- A rational-canonical matrix is trivially similar to itself. -/
theorem hasRationalCanonical_of_isRationalCanonicalMatrix
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K} (hA : IsRationalCanonicalMatrix A) :
    HasRationalCanonical A := by
  refine ⟨1, 1, A, ?_, hA, ?_⟩
  · constructor <;> simp
  · simp

/-- Every one-dimensional block has a rational-canonical similarity witness. -/
theorem hasRationalCanonical_unit
    [Field K] (C : Matrix Unit Unit K) :
    HasRationalCanonical C :=
  hasRationalCanonical_of_isRationalCanonicalMatrix
    (isRationalCanonicalMatrix_unit C)

/-- Rational-canonical similarity witnesses are invariant under reindexing. -/
theorem hasRationalCanonical_reindex
    [Field K]
    {ι κ : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    (e : ι ≃ κ) {A : Matrix ι ι K}
    (hA : HasRationalCanonical A) :
    HasRationalCanonical (Matrix.reindex e e A) := by
  rcases hA with ⟨P, Pinv, C, hInv, hC, hEq⟩
  refine ⟨Matrix.reindex e e P, Matrix.reindex e e Pinv,
    Matrix.reindex e e C, ?_, ?_, ?_⟩
  · constructor
    · simpa [Matrix.submatrix_mul_equiv] using congrArg (Matrix.reindex e e) hInv.1
    · simpa [Matrix.submatrix_mul_equiv] using congrArg (Matrix.reindex e e) hInv.2
  · exact isRationalCanonicalMatrix_reindex e hC
  · simpa [Matrix.submatrix_mul_equiv] using congrArg (Matrix.reindex e e) hEq

/-- Block-diagonal matrix inverses combine over the lexicographic sum index. -/
theorem hasMatrixInverse_blockDiag_lex
    [Field K]
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {P₁ Pinv₁ : Matrix α α K} {P₂ Pinv₂ : Matrix β β K}
    (h₁ : HasMatrixInverse P₁ Pinv₁) (h₂ : HasMatrixInverse P₂ Pinv₂) :
    HasMatrixInverse
      (rationalCanonicalBlockDiagLex P₁ P₂)
      (rationalCanonicalBlockDiagLex Pinv₁ Pinv₂) := by
  constructor
  · simp [rationalCanonicalBlockDiagLex, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, h₁.1, h₂.1]
  · simp [rationalCanonicalBlockDiagLex, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, h₁.2, h₂.2]

/--
Block-diagonal rational-canonical witnesses combine over the lexicographic sum
index.  This is the reusable matrix-level block lift needed by the eventual
cyclic-summand descent hook.
-/
theorem hasRationalCanonical_blockDiag_lex
    [Field K]
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [LinearOrder α] [LinearOrder β]
    (A₁ : Matrix α α K) (A₂ : Matrix β β K)
    (h₁ : HasRationalCanonical A₁) (h₂ : HasRationalCanonical A₂) :
    HasRationalCanonical (rationalCanonicalBlockDiagLex A₁ A₂) := by
  rcases h₁ with ⟨P₁, Pinv₁, C₁, hInv₁, hC₁, hEq₁⟩
  rcases h₂ with ⟨P₂, Pinv₂, C₂, hInv₂, hC₂, hEq₂⟩
  let P := rationalCanonicalBlockDiagLex P₁ P₂
  let Pinv := rationalCanonicalBlockDiagLex Pinv₁ Pinv₂
  let C := rationalCanonicalBlockDiagLex C₁ C₂
  refine ⟨P, Pinv, C, ?_, ?_, ?_⟩
  · exact hasMatrixInverse_blockDiag_lex hInv₁ hInv₂
  · exact isRationalCanonicalMatrix_blockDiag_lex C₁ C₂ hC₁ hC₂
  · simp [P, Pinv, C, rationalCanonicalBlockDiagLex, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, hEq₁, hEq₂, Matrix.mul_assoc]

/--
The standard companion matrix has the rational-canonical similarity witness
with identity change-of-basis matrices.
-/
theorem hasRationalCanonical_companionMatrixFin
    [Field K] (p : K[X]) (hmonic : p.Monic) (hpos : 0 < p.natDegree) :
    HasRationalCanonical (companionMatrixFin p) := by
  refine ⟨1, 1, companionMatrixFin p, ?_, ?_, ?_⟩
  · constructor <;> simp
  · exact isRationalCanonicalMatrix_companionMatrixFin p hmonic hpos
  · simp

/-- Universe-level predicate used by the square-subtype induction framework. -/
def RationalCanonical_P [Field K] (x : SquareUniverse K) : Prop :=
  HasRationalCanonical x.A

def RationalCanonical_P_sub [Field K] (x_sub : PosSquareUniverse K) : Prop :=
  RationalCanonical_P (x_sub : SquareUniverse K)

@[simp] theorem rationalCanonical_P_compat [Field K] (x_sub : PosSquareUniverse K) :
    RationalCanonical_P_sub x_sub ↔
      RationalCanonical_P (x_sub : SquareUniverse K) :=
  Iff.rfl

/-- Empty matrices have empty rational-canonical block data. -/
theorem isRationalCanonicalMatrix_empty
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι] [IsEmpty ι]
    (C : Matrix ι ι K) :
    IsRationalCanonicalMatrix C := by
  refine ⟨{
    block := ULift.{u} Empty
    invariantFactor := fun b => Empty.elim b.down
    invariantFactor_monic := fun b => Empty.elim b.down
    blockSize := fun b => Empty.elim b.down
    blockSize_pos := fun b => Empty.elim b.down
    blockSize_eq_natDegree := fun b => Empty.elim b.down
    total_size := ?_
    blockIndexEquiv := ?_
    block_form := ?_
  }⟩
  · simp
  · exact
      { toFun := fun i => False.elim (IsEmpty.false i)
        invFun := fun x => Empty.elim x.1.down
        left_inv := fun i => False.elim (IsEmpty.false i)
        right_inv := fun x => Empty.elim x.1.down }
  · ext x
    exact Empty.elim x.1.down

/-- Empty matrices have a trivial rational-canonical similarity witness. -/
theorem base_rationalCanonical_empty
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι] [IsEmpty ι]
    (A : Matrix ι ι K) :
    HasRationalCanonical A := by
  refine ⟨1, 1, A, ?_, ?_, ?_⟩
  · constructor <;> simp
  · exact isRationalCanonicalMatrix_empty A
  · simp

/--
Transport a rational-canonical witness backward across an invertible
similarity.
-/
theorem rationalCanonical_transport_similarity
    {K : Type v} {ι : Type u} [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (P Pinv : Matrix ι ι K) (A B : Matrix ι ι K)
    (hInv : HasMatrixInverse P Pinv)
    (hB : B = Pinv * A * P)
    (hRC : HasRationalCanonical B) :
    HasRationalCanonical A := by
  rcases hRC with ⟨S, Sinv, C, hSInv, hC, hEqB⟩
  refine ⟨P * S, Sinv * Pinv, C, ?_, hC, ?_⟩
  · constructor
    · calc
        (Sinv * Pinv) * (P * S) = Sinv * (Pinv * P) * S := by
          simp [Matrix.mul_assoc]
        _ = Sinv * S := by
          rw [hInv.1]
          simp
        _ = 1 := hSInv.1
    · calc
        (P * S) * (Sinv * Pinv) = P * (S * Sinv) * Pinv := by
          simp [Matrix.mul_assoc]
        _ = P * Pinv := by
          rw [hSInv.2]
          simp
        _ = 1 := hInv.2
  · have hA_back : A = P * B * Pinv := by
      calc
        A = (P * Pinv) * A * (P * Pinv) := by
          simp [hInv.2]
        _ = P * (Pinv * A * P) * Pinv := by
          simp [Matrix.mul_assoc]
        _ = P * B * Pinv := by
          rw [← hB]
    calc
      A = P * B * Pinv := hA_back
      _ = P * (S * C * Sinv) * Pinv := by
        rw [hEqB]
      _ = (P * S) * C * (Sinv * Pinv) := by
        simp [Matrix.mul_assoc]

end MatDecompFormal.Instances
