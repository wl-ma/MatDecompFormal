import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.QR.Details
import MatDecompFormal.Instances.QR.Strategy
import MatDecompFormal.Instances.QR.Recursive
import MatDecompFormal.Instances.QR.Driver
import MatDecompFormal.Components.Properties.Triangular

namespace MatDecompFormal.Instances

universe u v

open Matrix
open MatDecompFormal.Components.Properties
open MatDecompFormal.Framework

/-!
# Givens QR Groundwork

This file now contains both scalar normalization facts and the first matrix-level
building blocks for a Givens rotation step. The recursive framework and tail-slice
proof glue are shared with the Householder path; what remains is folding these
pairwise rotations into a full transformation that reaches `QRReady`.
-/

noncomputable def givensRadius (a b : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + b ^ 2)

noncomputable def givensC (a b : ℝ) : ℝ :=
  if _h : givensRadius a b = 0 then 1 else a / givensRadius a b

noncomputable def givensS (a b : ℝ) : ℝ :=
  if _h : givensRadius a b = 0 then 0 else b / givensRadius a b

lemma givensRadius_sq (a b : ℝ) : givensRadius a b ^ 2 = a ^ 2 + b ^ 2 := by
  unfold givensRadius
  simpa using (Real.sq_sqrt (show 0 ≤ a ^ 2 + b ^ 2 by positivity))

lemma givensRadius_eq_zero_imp (a b : ℝ) (h : givensRadius a b = 0) : a = 0 ∧ b = 0 := by
  have hs : a ^ 2 + b ^ 2 = 0 := by
    have hsq : givensRadius a b ^ 2 = 0 := by simpa [h]
    rw [givensRadius_sq] at hsq
    exact hsq
  have ha : a = 0 := by nlinarith
  have hb : b = 0 := by nlinarith
  exact ⟨ha, hb⟩

lemma givensC_sq_add_givensS_sq (a b : ℝ) :
    givensC a b ^ 2 + givensS a b ^ 2 = 1 := by
  by_cases h : givensRadius a b = 0
  · simp [givensC, givensS, h]
  · have hr2 : givensRadius a b ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 h
    have hc : givensC a b = a / givensRadius a b := by simp [givensC, h]
    have hs : givensS a b = b / givensRadius a b := by simp [givensS, h]
    rw [hc, hs]
    calc
      (a / givensRadius a b) ^ 2 + (b / givensRadius a b) ^ 2
          = (a ^ 2 + b ^ 2) / (givensRadius a b ^ 2) := by
              field_simp [h]
      _ = (givensRadius a b ^ 2) / (givensRadius a b ^ 2) := by rw [← givensRadius_sq]
      _ = 1 := by exact div_self hr2

lemma givens_annihilate_second (a b : ℝ) :
    -(givensS a b) * a + (givensC a b) * b = 0 := by
  by_cases h : givensRadius a b = 0
  · rcases givensRadius_eq_zero_imp a b h with ⟨ha, hb⟩
    simp [givensC, givensS, ha, hb]
  · have hc : givensC a b = a / givensRadius a b := by simp [givensC, h]
    have hs : givensS a b = b / givensRadius a b := by simp [givensS, h]
    rw [hc, hs]
    field_simp [h]
    ring

lemma givens_head_value (a b : ℝ) :
    (givensC a b) * a + (givensS a b) * b = givensRadius a b := by
  by_cases h : givensRadius a b = 0
  · rcases givensRadius_eq_zero_imp a b h with ⟨ha, hb⟩
    simp [givensC, givensS, h, givensRadius, ha, hb]
  · have hc : givensC a b = a / givensRadius a b := by simp [givensC, h]
    have hs : givensS a b = b / givensRadius a b := by simp [givensS, h]
    rw [hc, hs]
    calc
      (a / givensRadius a b) * a + (b / givensRadius a b) * b
          = (a ^ 2 + b ^ 2) / givensRadius a b := by
              field_simp [h]
      _ = givensRadius a b ^ 2 / givensRadius a b := by rw [← givensRadius_sq]
      _ = givensRadius a b := by
            field_simp [h]

section PairSplit

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]

abbrev GivensRestIdx (i : QRTailIdx ι) := {x : QRTailIdx ι // x ≠ i}

noncomputable def singledTailEquivUnit (i : QRTailIdx ι) :
    {x : QRTailIdx ι // x = i} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨i, rfl⟩
  left_inv := by intro x; rcases x with ⟨x, rfl⟩; rfl
  right_inv := by intro u; cases u; rfl

noncomputable def givensTailSplitEquiv (i : QRTailIdx ι) :
    QRTailIdx ι ≃ Unit ⊕ GivensRestIdx i :=
  (Equiv.sumCompl fun x : QRTailIdx ι => x = i).symm.trans
    (Equiv.sumCongr (singledTailEquivUnit i) (Equiv.refl _))

noncomputable def givensPairEquiv (i : QRTailIdx ι) :
    ι ≃ (Unit ⊕ Unit) ⊕ GivensRestIdx i :=
  (headTailEquiv (α := ι)).trans <|
    (Equiv.sumCongr (Equiv.refl _) (givensTailSplitEquiv i)).trans <|
      (Equiv.sumAssoc Unit Unit (GivensRestIdx i)).symm

@[simp] theorem givensPairEquiv_apply_head (i : QRTailIdx ι) :
    givensPairEquiv i (headElem (α := ι)) = Sum.inl (Sum.inl ()) := by
  simp [givensPairEquiv]

@[simp] theorem givensPairEquiv_apply_target (i : QRTailIdx ι) :
    givensPairEquiv i i.1 = Sum.inl (Sum.inr ()) := by
  simp [givensPairEquiv, givensTailSplitEquiv]

@[simp] theorem givensPairEquiv_symm_apply_head (i : QRTailIdx ι) :
    (givensPairEquiv i).symm (Sum.inl (Sum.inl ())) = headElem (α := ι) := by
  apply (givensPairEquiv i).injective
  simp

@[simp] theorem givensPairEquiv_symm_apply_target (i : QRTailIdx ι) :
    (givensPairEquiv i).symm (Sum.inl (Sum.inr ())) = i.1 := by
  apply (givensPairEquiv i).injective
  simp

end PairSplit

section MatrixStep

section GenericCSDefinitions

variable {R : Type v} [Semiring R] [Neg R]

noncomputable def givens2x2CS (c s : R) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) R :=
  fromBlocks
    (fun _ _ => c)
    (fun _ _ => s)
    (fun _ _ => -s)
    (fun _ _ => c)

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

noncomputable def givensEmbeddedBlockMatrix
    (γ : Type u) [Fintype γ] [DecidableEq γ] (c s : R) :
    Matrix ((Unit ⊕ Unit) ⊕ γ) ((Unit ⊕ Unit) ⊕ γ) R :=
  fromBlocks (givens2x2CS c s) 0 0 1

noncomputable def givensEmbeddedMatrix
    {γ : Type u} [Fintype γ] [DecidableEq γ]
    (e : ι ≃ (Unit ⊕ Unit) ⊕ γ) (c s : R) : Matrix ι ι R :=
  Matrix.reindex e.symm e.symm (givensEmbeddedBlockMatrix γ c s)

def IsGivensMatrix (Q : Matrix ι ι R) : Prop :=
  ∃ (γ : Type u) (_ : Fintype γ) (_ : DecidableEq γ)
      (e : ι ≃ (Unit ⊕ Unit) ⊕ γ) (c s : R),
    c ^ 2 + s ^ 2 = 1 ∧ Q = givensEmbeddedMatrix e c s

def IsGivensProduct (Q : Matrix ι ι R) : Prop :=
  IsProductOf IsGivensMatrix Q

end GenericCSDefinitions

section GenericCSTranspose

variable {R : Type v} [Semiring R] [InvolutiveNeg R]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

omit [Semiring R] in
lemma givens2x2CS_transpose (c s : R) :
    (givens2x2CS c s)ᵀ = givens2x2CS c (-s) := by
  ext i j <;> cases i <;> cases j <;> simp [givens2x2CS]

lemma givensEmbeddedBlockMatrix_transpose
    {γ : Type u} [Fintype γ] [DecidableEq γ] (c s : R) :
    (givensEmbeddedBlockMatrix γ c s)ᵀ = givensEmbeddedBlockMatrix γ c (-s) := by
  simp [givensEmbeddedBlockMatrix, givens2x2CS_transpose, Matrix.fromBlocks_transpose]

lemma givensEmbeddedMatrix_transpose
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {γ : Type u} [Fintype γ] [DecidableEq γ]
    (e : ι ≃ (Unit ⊕ Unit) ⊕ γ) (c s : R) :
    (givensEmbeddedMatrix e c s)ᵀ = givensEmbeddedMatrix e c (-s) := by
  simp [givensEmbeddedMatrix, givensEmbeddedBlockMatrix_transpose, Matrix.transpose_reindex]

end GenericCSTranspose

section GenericCS

variable {R : Type v} [Semiring R] [InvolutiveNeg R]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

lemma isGivensMatrix_transpose_of_neg_sq
    (hneg_sq : ∀ s : R, (-s) ^ 2 = s ^ 2)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι R}
    (hQ : IsGivensMatrix Q) :
    IsGivensMatrix Qᵀ := by
  rcases hQ with ⟨γ, _, _, e, c, s, hcs, rfl⟩
  refine ⟨γ, inferInstance, inferInstance, e, c, -s, ?_, ?_⟩
  · calc
      c ^ 2 + (-s) ^ 2 = c ^ 2 + s ^ 2 := by rw [hneg_sq s]
      _ = 1 := hcs
  · simpa using givensEmbeddedMatrix_transpose (e := e) c s

lemma isGivensMatrix_transpose
    {R : Type v} [Ring R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι R}
    (hQ : IsGivensMatrix Q) :
    IsGivensMatrix Qᵀ := by
  exact isGivensMatrix_transpose_of_neg_sq (fun s => by noncomm_ring) hQ

end GenericCS

section GenericCSOrthogonal

variable {R : Type v} [Semiring R] [Neg R]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

lemma isOrthogonalMatrix_givens2x2CS_of_entries (c s : R)
    (hdiag₁ : c * c + (-s) * (-s) = 1)
    (hoff₁ : c * s + (-s) * c = 0)
    (hoff₂ : s * c + c * (-s) = 0)
    (hdiag₂ : s * s + c * c = 1) :
    IsOrthogonalMatrix (givens2x2CS c s) := by
  rw [IsOrthogonalMatrix]
  ext i j <;> cases i <;> cases j <;>
    simp [givens2x2CS, Matrix.mul_apply, Fintype.sum_sum_type,
      hdiag₁, hoff₁, hoff₂, hdiag₂]

lemma isOrthogonalMatrix_givens2x2CS
    {R : Type v} [Ring R] (c s : R)
    (hcomm : c * s = s * c) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsOrthogonalMatrix (givens2x2CS c s) := by
  exact isOrthogonalMatrix_givens2x2CS_of_entries c s
    (by
      calc
        c * c + (-s) * (-s) = c ^ 2 + s ^ 2 := by noncomm_ring
        _ = 1 := hcs)
    (by
      rw [neg_mul, hcomm]
      abel)
    (by
      rw [mul_neg, ← hcomm]
      abel)
    (by
      rw [add_comm]
      simpa [pow_two] using hcs)

end GenericCSOrthogonal

section GenericCSCommSemiring

variable {R : Type v} [CommSemiring R] [InvolutiveNeg R]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

lemma isGivensProduct_transpose_of_neg_sq
    (hneg_sq : ∀ s : R, (-s) ^ 2 = s ^ 2)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι R}
    (hQ : IsGivensProduct Q) :
    IsGivensProduct Qᵀ := by
  exact isProductOf_transpose
    IsGivensMatrix
    (h_mem := fun M hM => isGivensMatrix_transpose_of_neg_sq hneg_sq hM)
    hQ

lemma isGivensProduct_transpose
    {R : Type v} [CommRing R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι R}
    (hQ : IsGivensProduct Q) :
    IsGivensProduct Qᵀ := by
  exact isGivensProduct_transpose_of_neg_sq (fun s => by ring) hQ

end GenericCSCommSemiring

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

abbrev HasGivensQR {R : Type v} [Semiring R] [Neg R] (A : Matrix ι ι R) : Prop :=
  HasStructuredQR IsGivensProduct A

abbrev HasGivensProductQR {R : Type v} [Semiring R] [Neg R] (A : Matrix ι ι R) : Prop :=
  HasGivensQR A

abbrev GivensQRTrace {R : Type v} [Semiring R] [Neg R] (A : Matrix ι ι R) : Prop :=
  QRProductTrace IsGivensMatrix A

variable [Nonempty ι]

noncomputable def givens2x2 (a b : ℝ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ :=
  givens2x2CS (givensC a b) (givensS a b)

lemma isOrthogonalMatrix_givens2x2 (a b : ℝ) :
    IsOrthogonalMatrix (givens2x2 a b) := by
  exact isOrthogonalMatrix_givens2x2CS (givensC a b) (givensS a b)
    (mul_comm (givensC a b) (givensS a b))
    (givensC_sq_add_givensS_sq a b)

noncomputable def givensPairBlockMatrix (i : QRTailIdx ι) (A : Matrix ι ι ℝ) :
    Matrix ((Unit ⊕ Unit) ⊕ GivensRestIdx i) ((Unit ⊕ Unit) ⊕ GivensRestIdx i) ℝ :=
  fromBlocks
    (givens2x2 (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
    0 0 1

noncomputable def givensPairBlockMatrixCS {R : Type v} [Semiring R] [Neg R]
    (i : QRTailIdx ι) (c s : R) :
    Matrix ((Unit ⊕ Unit) ⊕ GivensRestIdx i) ((Unit ⊕ Unit) ⊕ GivensRestIdx i) R :=
  givensEmbeddedBlockMatrix (GivensRestIdx i) c s

noncomputable def givensPairMatrix (i : QRTailIdx ι) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.reindex (givensPairEquiv i).symm (givensPairEquiv i).symm
    (givensPairBlockMatrix i A)

noncomputable def givensPairMatrixCS {R : Type v} [Semiring R] [Neg R]
    (i : QRTailIdx ι) (c s : R) : Matrix ι ι R :=
  givensEmbeddedMatrix (givensPairEquiv i) c s

lemma givensPairMatrixCS_isGivensMatrix
    {R : Type v} [Semiring R] [Neg R]
    (i : QRTailIdx ι) (c s : R) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsGivensMatrix (givensPairMatrixCS i c s) := by
  refine ⟨GivensRestIdx i, inferInstance, inferInstance,
    (show ι ≃ (Unit ⊕ Unit) ⊕ GivensRestIdx i from givensPairEquiv i), c, s, hcs, ?_⟩
  rfl

lemma givensPairMatrixCS_isGivensProduct
    {R : Type v} [Semiring R] [Neg R]
    (i : QRTailIdx ι) (c s : R) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsGivensProduct (givensPairMatrixCS i c s) := by
  refine ⟨[givensPairMatrixCS i c s], ?_, ?_⟩
  · intro M hM
    simp at hM
    rcases hM with rfl
    exact givensPairMatrixCS_isGivensMatrix i c s hcs
  · simp [matrixProduct]

lemma isOrthogonalMatrix_givensPairBlockMatrixCS_of_orthogonal
    {R : Type v} [Semiring R] [Neg R]
    (i : QRTailIdx ι) (c s : R)
    (h2 : IsOrthogonalMatrix (givens2x2CS c s)) :
    IsOrthogonalMatrix (givensPairBlockMatrixCS i c s) := by
  rw [givensPairBlockMatrixCS, givensEmbeddedBlockMatrix, IsOrthogonalMatrix]
  change (givens2x2CS c s)ᵀ * givens2x2CS c s = 1 at h2
  calc
    (fromBlocks (givens2x2CS c s) 0 0 (1 : Matrix (GivensRestIdx i) (GivensRestIdx i) R))ᵀ *
        fromBlocks (givens2x2CS c s) 0 0 (1 : Matrix (GivensRestIdx i) (GivensRestIdx i) R)
      = fromBlocks ((givens2x2CS c s)ᵀ * givens2x2CS c s) 0 0
          (1 : Matrix (GivensRestIdx i) (GivensRestIdx i) R) := by
            simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    _ = fromBlocks (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) R) 0 0
          (1 : Matrix (GivensRestIdx i) (GivensRestIdx i) R) := by rw [h2]
    _ = 1 := Matrix.fromBlocks_one

lemma isOrthogonalMatrix_givensPairBlockMatrixCS
    {R : Type v} [Ring R]
    (i : QRTailIdx ι) (c s : R)
    (hcomm : c * s = s * c) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsOrthogonalMatrix (givensPairBlockMatrixCS i c s) := by
  exact isOrthogonalMatrix_givensPairBlockMatrixCS_of_orthogonal i c s
    (isOrthogonalMatrix_givens2x2CS c s hcomm hcs)

lemma isOrthogonalMatrix_givensPairMatrixCS_of_block
    {R : Type v} [Semiring R] [Neg R]
    (i : QRTailIdx ι) (c s : R)
    (hblock : IsOrthogonalMatrix (givensPairBlockMatrixCS i c s)) :
    IsOrthogonalMatrix (givensPairMatrixCS i c s) := by
  rw [givensPairMatrixCS]
  exact (isOrthogonalMatrix_reindex (e := givensPairEquiv i)
    (Q := Matrix.reindex (givensPairEquiv i).symm (givensPairEquiv i).symm
      (givensPairBlockMatrixCS i c s))).2 (by
        simpa [givensEmbeddedMatrix, givensPairMatrixCS, givensPairBlockMatrixCS] using hblock)

lemma isOrthogonalMatrix_givensPairMatrixCS_of_orthogonal
    {R : Type v} [Semiring R] [Neg R]
    (i : QRTailIdx ι) (c s : R)
    (h2 : IsOrthogonalMatrix (givens2x2CS c s)) :
    IsOrthogonalMatrix (givensPairMatrixCS i c s) := by
  exact isOrthogonalMatrix_givensPairMatrixCS_of_block i c s
    (isOrthogonalMatrix_givensPairBlockMatrixCS_of_orthogonal i c s h2)

lemma isOrthogonalMatrix_givensPairMatrixCS
    {R : Type v} [Ring R]
    (i : QRTailIdx ι) (c s : R)
    (hcomm : c * s = s * c) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsOrthogonalMatrix (givensPairMatrixCS i c s) := by
  exact isOrthogonalMatrix_givensPairMatrixCS_of_orthogonal i c s
    (isOrthogonalMatrix_givens2x2CS c s hcomm hcs)

lemma givensPairMatrixCS_mul_apply_target_head
    {R : Type v} [Semiring R] [Neg R]
    (i : QRTailIdx ι) (c s : R) (A : Matrix ι ι R) :
    ((givensPairMatrixCS i c s) * A) i.1 (headElem (α := ι)) =
      -s * A (headElem (α := ι)) (headElem (α := ι)) + c * A i.1 (headElem (α := ι)) := by
  let e := givensPairEquiv i
  let Ablk := Matrix.reindex e e A
  have hmul :
      (givensPairMatrixCS i c s) * A =
        Matrix.reindex e.symm e.symm (givensPairBlockMatrixCS i c s * Ablk) := by
    simpa [givensPairMatrixCS, givensEmbeddedMatrix, givensPairBlockMatrixCS, Ablk, e] using
      (Matrix.reindexLinearEquiv_mul R R e.symm e.symm e.symm
        (givensPairBlockMatrixCS i c s) Ablk)
  have hentry := congrArg (fun M => M i.1 (headElem (α := ι))) hmul
  simpa [Ablk, e, givensPairBlockMatrixCS, givensEmbeddedBlockMatrix, givens2x2CS,
    Matrix.mul_apply, Fintype.sum_sum_type, Matrix.reindex_apply] using hentry

lemma givensPairMatrixCS_mul_apply_head_head
    {R : Type v} [Semiring R] [Neg R]
    (i : QRTailIdx ι) (c s : R) (A : Matrix ι ι R) :
    ((givensPairMatrixCS i c s) * A) (headElem (α := ι)) (headElem (α := ι)) =
      c * A (headElem (α := ι)) (headElem (α := ι)) + s * A i.1 (headElem (α := ι)) := by
  let e := givensPairEquiv i
  let Ablk := Matrix.reindex e e A
  have hmul :
      (givensPairMatrixCS i c s) * A =
        Matrix.reindex e.symm e.symm (givensPairBlockMatrixCS i c s * Ablk) := by
    simpa [givensPairMatrixCS, givensEmbeddedMatrix, givensPairBlockMatrixCS, Ablk, e] using
      (Matrix.reindexLinearEquiv_mul R R e.symm e.symm e.symm
        (givensPairBlockMatrixCS i c s) Ablk)
  have hentry := congrArg (fun M => M (headElem (α := ι)) (headElem (α := ι))) hmul
  simpa [Ablk, e, givensPairBlockMatrixCS, givensEmbeddedBlockMatrix, givens2x2CS,
    Matrix.mul_apply, Fintype.sum_sum_type, Matrix.reindex_apply] using hentry

lemma givensPairMatrixCS_mul_apply_other_head
    {R : Type v} [Semiring R] [Neg R]
    (i k : QRTailIdx ι) (c s : R) (A : Matrix ι ι R) (hk : k ≠ i) :
    ((givensPairMatrixCS i c s) * A) k.1 (headElem (α := ι)) = A k.1 (headElem (α := ι)) := by
  let e := givensPairEquiv i
  let Ablk := Matrix.reindex e e A
  let krest : GivensRestIdx i := ⟨k, hk⟩
  have hkrow : e k.1 = Sum.inr krest := by
    apply e.symm.injective
    simp [e, krest, givensPairEquiv, givensTailSplitEquiv]
  have hmul :
      (givensPairMatrixCS i c s) * A =
        Matrix.reindex e.symm e.symm (givensPairBlockMatrixCS i c s * Ablk) := by
    simpa [givensPairMatrixCS, givensEmbeddedMatrix, givensPairBlockMatrixCS, Ablk, e] using
      (Matrix.reindexLinearEquiv_mul R R e.symm e.symm e.symm
        (givensPairBlockMatrixCS i c s) Ablk)
  have hentry := congrArg (fun M => M k.1 (headElem (α := ι))) hmul
  simpa [Ablk, e, krest, hkrow, givensPairBlockMatrixCS, givensEmbeddedBlockMatrix,
    Matrix.mul_apply, Fintype.sum_sum_type, Matrix.reindex_apply, Matrix.one_apply] using hentry

lemma base_givensQR_subsingleton
    {R : Type v} [Semiring R] [Neg R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Subsingleton ι]
    (A : Matrix ι ι R) :
    HasGivensQR A := by
  refine ⟨1, A, ?_, ?_, ?_, ?_⟩
  · exact isProductOf_one IsGivensMatrix
  · exact isOrthogonalMatrix_one
  · exact isUpperTriangular_of_subsingleton A
  · simp

/-- Transport a Givens-flavored QR decomposition back across a left Givens product,
assuming the transpose-side structure has already been supplied. -/
theorem givens_transport_of_orthogonal_left_of_transpose
    {R : Type v} [CommSemiring R] [Neg R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (H A : Matrix ι ι R)
    (hH_prod_T : IsGivensProduct Hᵀ)
    (hH_orth : IsOrthogonalMatrix H)
    (hH_orth_T : IsOrthogonalMatrix Hᵀ)
    (hQR : HasGivensQR (H * A)) :
    HasGivensQR A := by
  rcases hQR with ⟨Q, R', hQ_prod, hQ_orth, hR, hEq⟩
  refine ⟨Hᵀ * Q, R', ?_, ?_, hR, ?_⟩
  · exact isProductOf_mul IsGivensMatrix hH_prod_T hQ_prod
  · exact isOrthogonalMatrix_mul hH_orth_T hQ_orth
  · calc
      A = (Hᵀ * H) * A := by
        have hHH := congrArg (fun M => M * A) hH_orth
        simpa [IsOrthogonalMatrix, Matrix.mul_assoc] using hHH.symm
      _ = Hᵀ * (H * A) := by rw [Matrix.mul_assoc]
      _ = Hᵀ * (Q * R') := by rw [hEq]
      _ = (Hᵀ * Q) * R' := by rw [Matrix.mul_assoc]

/-- Transport a Givens-flavored QR decomposition back across a left Givens product. -/
theorem givens_transport_of_orthogonal_left
    {R : Type v} [CommRing R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (H A : Matrix ι ι R)
    (hH_prod : IsGivensProduct H)
    (hH_orth : IsOrthogonalMatrix H)
    (hQR : HasGivensQR (H * A)) :
    HasGivensQR A := by
  exact givens_transport_of_orthogonal_left_of_transpose H A
    (isGivensProduct_transpose hH_prod)
    hH_orth
    (isOrthogonalMatrix_transpose hH_orth)
    hQR

lemma givensPairMatrix_eq_givensPairMatrixCS (i : QRTailIdx ι) (A : Matrix ι ι ℝ) :
    givensPairMatrix i A =
      givensPairMatrixCS i
        (givensC (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
        (givensS (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι)))) := by
  simp [givensPairMatrix, givensPairMatrixCS, givensPairBlockMatrix, givensEmbeddedMatrix,
    givensEmbeddedBlockMatrix, givensPairBlockMatrixCS, givens2x2, givens2x2CS]

lemma givensPairMatrix_isGivensMatrix (i : QRTailIdx ι) (A : Matrix ι ι ℝ) :
    IsGivensMatrix (givensPairMatrix i A) := by
  rw [givensPairMatrix_eq_givensPairMatrixCS i A]
  exact givensPairMatrixCS_isGivensMatrix i
    (givensC (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
    (givensS (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
    (givensC_sq_add_givensS_sq
      (A (headElem (α := ι)) (headElem (α := ι)))
      (A i.1 (headElem (α := ι))))

lemma givensPairMatrix_isGivensProduct (i : QRTailIdx ι) (A : Matrix ι ι ℝ) :
    IsGivensProduct (givensPairMatrix i A) := by
  rw [givensPairMatrix_eq_givensPairMatrixCS i A]
  exact givensPairMatrixCS_isGivensProduct i
    (givensC (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
    (givensS (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
    (givensC_sq_add_givensS_sq
      (A (headElem (α := ι)) (headElem (α := ι)))
      (A i.1 (headElem (α := ι))))

lemma isOrthogonalMatrix_givensPairBlockMatrix (i : QRTailIdx ι) (A : Matrix ι ι ℝ) :
    IsOrthogonalMatrix (givensPairBlockMatrix i A) := by
  simpa [givensPairBlockMatrix, givensPairBlockMatrixCS, givens2x2]
    using isOrthogonalMatrix_givensPairBlockMatrixCS i
      (givensC (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
      (givensS (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
      (mul_comm _ _)
      (givensC_sq_add_givensS_sq
        (A (headElem (α := ι)) (headElem (α := ι)))
        (A i.1 (headElem (α := ι))))

lemma isOrthogonalMatrix_givensPairMatrix (i : QRTailIdx ι) (A : Matrix ι ι ℝ) :
    IsOrthogonalMatrix (givensPairMatrix i A) := by
  rw [givensPairMatrix_eq_givensPairMatrixCS i A]
  exact isOrthogonalMatrix_givensPairMatrixCS i
    (givensC (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
    (givensS (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
    (mul_comm _ _)
    (givensC_sq_add_givensS_sq
      (A (headElem (α := ι)) (headElem (α := ι)))
      (A i.1 (headElem (α := ι))))

lemma givensPairMatrix_mul_apply_target_head (i : QRTailIdx ι) (A : Matrix ι ι ℝ) :
    ((givensPairMatrix i A) * A) i.1 (headElem (α := ι)) = 0 := by
  rw [givensPairMatrix_eq_givensPairMatrixCS i A]
  rw [givensPairMatrixCS_mul_apply_target_head]
  simpa using
    (givens_annihilate_second
      (A (headElem (α := ι)) (headElem (α := ι)))
      (A i.1 (headElem (α := ι))))

lemma givensPairMatrix_mul_apply_head_head (i : QRTailIdx ι) (A : Matrix ι ι ℝ) :
    ((givensPairMatrix i A) * A) (headElem (α := ι)) (headElem (α := ι)) =
      givensRadius (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))) := by
  rw [givensPairMatrix_eq_givensPairMatrixCS i A]
  rw [givensPairMatrixCS_mul_apply_head_head]
  simpa using
    (givens_head_value
      (A (headElem (α := ι)) (headElem (α := ι)))
      (A i.1 (headElem (α := ι))))

end MatrixStep



section Sweep

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]

@[simp] theorem givensPairEquiv_symm_apply_rest (i : QRTailIdx ι) (k : GivensRestIdx i) :
    (givensPairEquiv i).symm (Sum.inr k) = k.1.1 := by
  apply (givensPairEquiv i).injective
  simp [givensPairEquiv, givensTailSplitEquiv]

@[simp] theorem givensPairEquiv_apply_rest (i : QRTailIdx ι) (k : GivensRestIdx i) :
    givensPairEquiv i k.1.1 = Sum.inr k := by
  apply (givensPairEquiv i).symm.injective
  simp [givensPairEquiv_symm_apply_rest]

lemma givensPairMatrix_mul_apply_other_head
    (i k : QRTailIdx ι) (A : Matrix ι ι ℝ) (hk : k ≠ i) :
    ((givensPairMatrix i A) * A) k.1 (headElem (α := ι)) = A k.1 (headElem (α := ι)) := by
  rw [givensPairMatrix_eq_givensPairMatrixCS i A]
  exact givensPairMatrixCS_mul_apply_other_head i k
    (givensC (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
    (givensS (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))
    A hk

noncomputable def qrGivensTailList (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Nonempty ι] : List (QRTailIdx ι) :=
  (Finset.univ : Finset (QRTailIdx ι)).toList

noncomputable def qrGivensSweepMatrixCS
    {R : Type v} [Semiring R] [Neg R]
    (coeff : QRTailIdx ι → Matrix ι ι R → R × R) :
    List (QRTailIdx ι) → Matrix ι ι R → Matrix ι ι R
  | [], A => A
  | i :: is, A =>
      let cs := coeff i A
      qrGivensSweepMatrixCS coeff is (givensPairMatrixCS i cs.1 cs.2 * A)

lemma qrGivensSweepMatrixCS_preserves_head_of_not_mem
    {R : Type v} [Semiring R] [Neg R]
    (coeff : QRTailIdx ι → Matrix ι ι R → R × R) :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι R) {k : QRTailIdx ι},
      k ∉ l →
        qrGivensSweepMatrixCS coeff l A k.1 (headElem (α := ι)) =
          A k.1 (headElem (α := ι))
  | [], A, k, _ => by simp [qrGivensSweepMatrixCS]
  | i :: is, A, k, hk => by
      have hk_ne : k ≠ i := by
        intro h
        exact hk (by simp [h])
      have hk_tail : k ∉ is := by
        intro hmem
        exact hk (by simp [hmem])
      let cs := coeff i A
      calc
        qrGivensSweepMatrixCS coeff (i :: is) A k.1 (headElem (α := ι))
            = qrGivensSweepMatrixCS coeff is ((givensPairMatrixCS i cs.1 cs.2) * A) k.1
                (headElem (α := ι)) := by simp [qrGivensSweepMatrixCS, cs]
        _ = ((givensPairMatrixCS i cs.1 cs.2) * A) k.1 (headElem (α := ι)) :=
              qrGivensSweepMatrixCS_preserves_head_of_not_mem coeff is
                ((givensPairMatrixCS i cs.1 cs.2) * A) hk_tail
        _ = A k.1 (headElem (α := ι)) :=
              givensPairMatrixCS_mul_apply_other_head i k cs.1 cs.2 A hk_ne

lemma qrGivensSweepMatrixCS_zero_of_mem
    {R : Type v} [Semiring R] [Neg R]
    (coeff : QRTailIdx ι → Matrix ι ι R → R × R)
    (hzero : ∀ (i : QRTailIdx ι) (A : Matrix ι ι R),
      let cs := coeff i A
      ((givensPairMatrixCS i cs.1 cs.2) * A) i.1 (headElem (α := ι)) = 0) :
    ∀ {l : List (QRTailIdx ι)} (_hnd : l.Nodup) (A : Matrix ι ι R) {k : QRTailIdx ι},
      k ∈ l → qrGivensSweepMatrixCS coeff l A k.1 (headElem (α := ι)) = 0
  | [], _hnd, A, k, hk => by cases hk
  | i :: is, hnd, A, k, hk => by
      rcases List.nodup_cons.mp hnd with ⟨hi_not_mem, hnd_tail⟩
      rcases List.mem_cons.mp hk with hk_head | hk_tail
      · subst hk_head
        let cs := coeff k A
        calc
          qrGivensSweepMatrixCS coeff (k :: is) A k.1 (headElem (α := ι))
              = qrGivensSweepMatrixCS coeff is ((givensPairMatrixCS k cs.1 cs.2) * A) k.1
                  (headElem (α := ι)) := by simp [qrGivensSweepMatrixCS, cs]
          _ = ((givensPairMatrixCS k cs.1 cs.2) * A) k.1 (headElem (α := ι)) :=
                qrGivensSweepMatrixCS_preserves_head_of_not_mem coeff is
                  ((givensPairMatrixCS k cs.1 cs.2) * A) hi_not_mem
          _ = 0 := by simpa [cs] using hzero k A
      · let cs := coeff i A
        calc
          qrGivensSweepMatrixCS coeff (i :: is) A k.1 (headElem (α := ι))
              = qrGivensSweepMatrixCS coeff is ((givensPairMatrixCS i cs.1 cs.2) * A) k.1
                  (headElem (α := ι)) := by simp [qrGivensSweepMatrixCS, cs]
          _ = 0 := qrGivensSweepMatrixCS_zero_of_mem coeff hzero hnd_tail
            ((givensPairMatrixCS i cs.1 cs.2) * A) hk_tail

noncomputable def qrGivensCoeff (i : QRTailIdx ι) (A : Matrix ι ι ℝ) : ℝ × ℝ :=
  (givensC (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))),
    givensS (A (headElem (α := ι)) (headElem (α := ι))) (A i.1 (headElem (α := ι))))

lemma qrGivensCoeff_zero (i : QRTailIdx ι) (A : Matrix ι ι ℝ) :
    let cs := qrGivensCoeff i A
    ((givensPairMatrixCS i cs.1 cs.2) * A) i.1 (headElem (α := ι)) = 0 := by
  simpa [qrGivensCoeff] using givensPairMatrix_mul_apply_target_head i A

noncomputable def qrGivensSweepMatrix :
    List (QRTailIdx ι) → Matrix ι ι ℝ → Matrix ι ι ℝ :=
  qrGivensSweepMatrixCS qrGivensCoeff

noncomputable def qrGivensSweepQCS
    {R : Type v} [Semiring R] [Neg R]
    (coeff : QRTailIdx ι → Matrix ι ι R → R × R) :
    List (QRTailIdx ι) → Matrix ι ι R → Matrix ι ι R
  | [], _ => 1
  | i :: is, A =>
      let cs := coeff i A
      let G := givensPairMatrixCS i cs.1 cs.2
      let A' := G * A
      qrGivensSweepQCS coeff is A' * G

lemma qrGivensSweepQCS_mul_eq
    {R : Type v} [Semiring R] [Neg R]
    (coeff : QRTailIdx ι → Matrix ι ι R → R × R) :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι R),
      qrGivensSweepQCS coeff l A * A = qrGivensSweepMatrixCS coeff l A
  | [], A => by simp [qrGivensSweepQCS, qrGivensSweepMatrixCS]
  | i :: is, A => by
      simp [qrGivensSweepQCS, qrGivensSweepMatrixCS, qrGivensSweepQCS_mul_eq,
        Matrix.mul_assoc]

lemma qrGivensSweepQCS_isGivensProduct
    {R : Type v} [Semiring R] [Neg R]
    (coeff : QRTailIdx ι → Matrix ι ι R → R × R)
    (hcs : ∀ (i : QRTailIdx ι) (A : Matrix ι ι R),
      let cs := coeff i A
      cs.1 ^ 2 + cs.2 ^ 2 = 1) :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι R),
      IsGivensProduct (qrGivensSweepQCS coeff l A)
  | [], A => isProductOf_one IsGivensMatrix
  | i :: is, A => by
      let cs := coeff i A
      let G := givensPairMatrixCS i cs.1 cs.2
      let A' := G * A
      exact isProductOf_mul IsGivensMatrix
        (qrGivensSweepQCS_isGivensProduct coeff hcs is A')
        (givensPairMatrixCS_isGivensProduct i cs.1 cs.2 (by simpa [cs] using hcs i A))

omit [DecidableEq ι] in
lemma qrGivensCoeff_norm (i : QRTailIdx ι) (A : Matrix ι ι ℝ) :
    let cs := qrGivensCoeff i A
    cs.1 ^ 2 + cs.2 ^ 2 = 1 := by
  simpa [qrGivensCoeff] using
    givensC_sq_add_givensS_sq
      (A (headElem (α := ι)) (headElem (α := ι)))
      (A i.1 (headElem (α := ι)))

lemma qrGivensSweepQCS_isOrthogonalMatrix_of_steps
    {R : Type v} [CommSemiring R] [Neg R]
    (coeff : QRTailIdx ι → Matrix ι ι R → R × R)
    (horth : ∀ (i : QRTailIdx ι) (A : Matrix ι ι R),
      let cs := coeff i A
      IsOrthogonalMatrix (givens2x2CS cs.1 cs.2)) :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι R),
      IsOrthogonalMatrix (qrGivensSweepQCS coeff l A)
  | [], A => by
      simpa [qrGivensSweepQCS] using (isOrthogonalMatrix_one)
  | i :: is, A => by
      simp only [qrGivensSweepQCS]
      let cs := coeff i A
      let G := givensPairMatrixCS i cs.1 cs.2
      let A' := G * A
      exact isOrthogonalMatrix_mul
        (qrGivensSweepQCS_isOrthogonalMatrix_of_steps coeff horth is A')
        (isOrthogonalMatrix_givensPairMatrixCS_of_orthogonal i cs.1 cs.2
          (by simpa [cs] using horth i A))

lemma qrGivensSweepQCS_isOrthogonalMatrix
    {R : Type v} [CommRing R]
    (coeff : QRTailIdx ι → Matrix ι ι R → R × R)
    (hcs : ∀ (i : QRTailIdx ι) (A : Matrix ι ι R),
      let cs := coeff i A
      cs.1 ^ 2 + cs.2 ^ 2 = 1) :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι R),
      IsOrthogonalMatrix (qrGivensSweepQCS coeff l A) := by
  exact qrGivensSweepQCS_isOrthogonalMatrix_of_steps coeff
    (fun i A => by
      let cs := coeff i A
      exact isOrthogonalMatrix_givens2x2CS cs.1 cs.2 (mul_comm _ _)
        (by simpa [cs] using hcs i A))

noncomputable def qrGivensSweepQ :
    List (QRTailIdx ι) → Matrix ι ι ℝ → Matrix ι ι ℝ :=
  qrGivensSweepQCS qrGivensCoeff

lemma qrGivensSweepQ_mul_eq :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι ℝ),
      qrGivensSweepQ l A * A = qrGivensSweepMatrix l A := by
  intro l A
  simpa [qrGivensSweepQ, qrGivensSweepMatrix] using
    qrGivensSweepQCS_mul_eq qrGivensCoeff l A

lemma isOrthogonalMatrix_qrGivensSweepQ :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι ℝ),
      IsOrthogonalMatrix (qrGivensSweepQ l A) := by
  intro l A
  simpa [qrGivensSweepQ] using
    qrGivensSweepQCS_isOrthogonalMatrix qrGivensCoeff qrGivensCoeff_norm l A

lemma qrGivensSweepMatrix_preserves_head_of_not_mem :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι ℝ) {k : QRTailIdx ι},
      k ∉ l →
        qrGivensSweepMatrix l A k.1 (headElem (α := ι)) = A k.1 (headElem (α := ι)) := by
  intro l A k hk
  simpa [qrGivensSweepMatrix] using
    (qrGivensSweepMatrixCS_preserves_head_of_not_mem qrGivensCoeff l A hk)

lemma qrGivensSweepMatrix_zero_of_mem :
    ∀ {l : List (QRTailIdx ι)} (_hnd : l.Nodup) (A : Matrix ι ι ℝ) {k : QRTailIdx ι},
      k ∈ l → qrGivensSweepMatrix l A k.1 (headElem (α := ι)) = 0 := by
  intro l hnd A k hk
  simpa [qrGivensSweepMatrix] using
    (qrGivensSweepMatrixCS_zero_of_mem qrGivensCoeff qrGivensCoeff_zero hnd A hk)

lemma qrGivensSweepMatrix_ready (A : Matrix ι ι ℝ) :
    QRReady ι (qrGivensSweepMatrix (qrGivensTailList ι) A) := by
  ext i j
  cases j
  have hi_mem : i ∈ qrGivensTailList ι := by
    simpa [qrGivensTailList] using (show i ∈ (Finset.univ : Finset (QRTailIdx ι)) by simp)
  simpa [QRReady, Matrix.toBlocks₂₁, Matrix.reindex_apply,
    headTailEquiv_symm_apply_inl, headTailEquiv_symm_apply_inr] using
    (qrGivensSweepMatrix_zero_of_mem
      ((Finset.univ : Finset (QRTailIdx ι)).nodup_toList) A hi_mem)

lemma qrGivensSweepQ_isGivensProduct :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι ℝ),
      IsGivensProduct (qrGivensSweepQ l A) := by
  intro l A
  simpa [qrGivensSweepQ] using
    qrGivensSweepQCS_isGivensProduct qrGivensCoeff qrGivensCoeff_norm l A

lemma qrGivensSweep_ready (A : Matrix ι ι ℝ) :
    QRReady ι (qrGivensSweepQ (qrGivensTailList ι) A * A) := by
  rw [qrGivensSweepQ_mul_eq]
  exact qrGivensSweepMatrix_ready A

noncomputable def qrGivensTransformCS
    {R : Type v} [CommSemiring R] [Neg R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (coeff : QRTailIdx ι → Matrix ι ι R → R × R)
    (horth : ∀ A : Matrix ι ι R,
      IsOrthogonalMatrix (qrGivensSweepQCS coeff (qrGivensTailList ι) A))
    (horthT : ∀ A : Matrix ι ι R,
      IsOrthogonalMatrix (qrGivensSweepQCS coeff (qrGivensTailList ι) A)ᵀ)
    (hready : ∀ A : Matrix ι ι R,
      QRReady ι (qrGivensSweepQCS coeff (qrGivensTailList ι) A * A)) :
    MatDecompFormal.Abstractions.Transformation (Matrix ι ι R) where
  T := { Q : Matrix ι ι R // IsOrthogonalMatrix Q ∧ IsOrthogonalMatrix Qᵀ }
  Goal := QRReady ι
  decGoal := by infer_instance
  apply := fun Q A => Q.1 * A
  find := fun A _ => ⟨qrGivensSweepQCS coeff (qrGivensTailList ι) A, horth A, horthT A⟩
  find_spec := by
    intro A _hA
    exact hready A

noncomputable def qrGivensTransform
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    MatDecompFormal.Abstractions.Transformation (Matrix ι ι ℝ) :=
  qrGivensTransformCS ι qrGivensCoeff
    (fun A => isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A)
    (fun A => by
      exact isOrthogonalMatrix_transpose
        (isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A))
    (fun A => by simpa [qrGivensSweepQ] using qrGivensSweep_ready A)

noncomputable def qrGivensStrategyCoreCS
    {R : Type v} [CommSemiring R] [Neg R]
    (coeff :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        QRTailIdx ι → Matrix ι ι R → R × R)
    (horth :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsOrthogonalMatrix (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A))
    (horthT :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsOrthogonalMatrix (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A)ᵀ)
    (hready :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          QRReady ι (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A * A)) :
    SquareStrategyCore R where
  SliceIdx := fun {ι} fι dι oι nι => @QRTailIdx ι fι oι nι
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
      { transform := qrGivensTransformCS ι (coeff ι) (horth ι) (horthT ι) (hready ι)
        reduction := qrHeadTailSubmatrixReduction ι
        goal_is_sliceable := by
          funext A
          rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (QRTailIdx ι)
        μ_mono := ?_
        slice_progress := ?_ }
    · intro A t
      simp
    · intro A hA
      have hlt : Fintype.card (QRTailIdx ι) < Fintype.card ι := by
        simpa [QRTailIdx] using
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

noncomputable def qrGivensStrategyCore : SquareStrategyCore ℝ :=
  qrGivensStrategyCoreCS
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] =>
      qrGivensCoeff)
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A =>
      isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A)
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      exact isOrthogonalMatrix_transpose
        (isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A))
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      simpa [qrGivensSweepQ] using qrGivensSweep_ready A)

noncomputable def qr_givens_strategy_proofCS
    {R : Type v} [CommSemiring R] [Neg R]
    (coeff :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        QRTailIdx ι → Matrix ι ι R → R × R)
    (horth :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsOrthogonalMatrix (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A))
    (horthT :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsOrthogonalMatrix (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A)ᵀ)
    (hready :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          QRReady ι (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A * A)) :
    SquareStrategyProofData R QR_P (qrGivensStrategyCoreCS coeff horth horthT hready) where
  transport := by
    intro ι fι dι oι nι A B hBA hP
    rcases hBA with rfl | ⟨t, rfl⟩
    · exact hP
    · exact qr_transport_of_orthogonal_left_of_transpose t.1 A t.2.1 t.2.2 hP
  lift := by
    intro ι fι dι oι nι A hA hP
    exact qrReady_headTailSubmatrixLift A hA hP

noncomputable def qr_givens_strategy_proof :=
  qr_givens_strategy_proofCS
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] =>
      qrGivensCoeff)
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A =>
      isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A)
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      exact isOrthogonalMatrix_transpose
        (isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A))
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      simpa [qrGivensSweepQ] using qrGivensSweep_ready A)

noncomputable def qr_givens_strategy_data : SquareStrategyData ℝ QR_P :=
  mkSquareStrategyData qrGivensStrategyCore qr_givens_strategy_proof

noncomputable def qr_givens_framework_inst : SquareSubtypeInductionInstance ℝ :=
  mkSquareSubtypeInductionInstanceFromStrategy
    QR_P
    qr_base_univ
    qr_givens_strategy_data

theorem exists_qr_decomposition_givens_basic
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : HasQR A := by
  by_cases h_sub : Subsingleton ι
  · letI := h_sub
    exact base_qr_subsingleton A
  · letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp h_sub
    let x : SquareUniverse ℝ := SquareUniverse.ofMatrix A
    have hP : (qr_givens_framework_inst : SquareSubtypeInductionInstance ℝ).P x := by
      exact
        (SubtypeInductionInstance.prove
          (inst := (qr_givens_framework_inst : SquareSubtypeInductionInstance ℝ)))
          x
    change HasQR A at hP
    exact hP



section StrongVariant

lemma hasQR_of_hasGivensQR
    {R : Type v} [Semiring R] [Neg R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R} (hA : HasGivensQR A) :
    HasQR A := by
  exact hasQR_of_hasStructuredQR hA

lemma givensQRTrace_of_hasGivensQR
    {R : Type v} [Semiring R] [Neg R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R} (hA : HasGivensQR A) :
    GivensQRTrace A := by
  exact qrProductTrace_of_hasStructuredQR hA

lemma hasGivensQR_of_givensQRTrace
    {R : Type v} [Semiring R] [Neg R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R} (hA : GivensQRTrace A) :
    HasGivensQR A := by
  exact hasStructuredQR_of_qrProductTrace hA

lemma hasQR_of_givensQRTrace
    {R : Type v} [Semiring R] [Neg R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R} (hA : GivensQRTrace A) :
    HasQR A := by
  exact hasQR_of_qrProductTrace hA

lemma isGivensMatrix_reindex
    {R : Type v} [Semiring R] [Neg R]
    {α β : Type u}
    [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β)
    {Q : Matrix α α R}
    (hQ : IsGivensMatrix Q) :
    IsGivensMatrix (Matrix.reindex e e Q) := by
  rcases hQ with ⟨γ, _, _, eQ, c, s, hcs, rfl⟩
  refine ⟨γ, inferInstance, inferInstance, e.symm.trans eQ, c, s, hcs, ?_⟩
  simp [givensEmbeddedMatrix]

lemma isGivensProduct_reindex
    {R : Type v} [Semiring R] [Neg R]
    {α β : Type u}
    [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β)
    {Q : Matrix α α R}
    (hQ : IsGivensProduct Q) :
    IsGivensProduct (Matrix.reindex e e Q) := by
  exact isProductOf_map
    (fun M => IsGivensMatrix M)
    (fun M => IsGivensMatrix M)
    (f := fun M => Matrix.reindex e e M)
    (by simp)
    (by
      intro A B
      simp [Matrix.submatrix_mul_equiv])
    (by
      intro M hM
      exact isGivensMatrix_reindex (e := e) hM)
    hQ

noncomputable def givensLiftEquiv
    {β γ : Type u}
    [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (e : β ≃ (Unit ⊕ Unit) ⊕ γ) :
    Unit ⊕ₗ β ≃ (Unit ⊕ Unit) ⊕ (Unit ⊕ γ) where
  toFun
    | Sum.inl u => Sum.inr (Sum.inl u)
    | Sum.inr b =>
        match e b with
        | Sum.inl uv => Sum.inl uv
        | Sum.inr g => Sum.inr (Sum.inr g)
  invFun
    | Sum.inl uv => Sum.inr (e.symm (Sum.inl uv))
    | Sum.inr (Sum.inl u) => Sum.inl u
    | Sum.inr (Sum.inr g) => Sum.inr (e.symm (Sum.inr g))
  left_inv := by
    intro x
    rcases x with (_ | b)
    · rfl
    · cases h : e b with
      | inl uv =>
          have hs : e.symm (Sum.inl uv) = b := by
            simpa using (congrArg e.symm h).symm
          simp [h, hs]
      | inr g =>
          have hs : e.symm (Sum.inr g) = b := by
            simpa using (congrArg e.symm h).symm
          simp [h, hs]
  right_inv := by
    intro x
    rcases x with (_ | x)
    · simp
    · rcases x with (_ | g)
      · rfl
      · simp

lemma blockDiag_one_givensEmbeddedMatrix
    {R : Type v} [Semiring R] [Neg R]
    {β γ : Type u}
    [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (e : β ≃ (Unit ⊕ Unit) ⊕ γ) (c s : R) :
    (fromBlocks (1 : Matrix Unit Unit R) 0 0 (givensEmbeddedMatrix e c s) :
        Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) =
      givensEmbeddedMatrix (givensLiftEquiv e) c s := by
  ext i j <;> rcases i with (_ | i) <;> rcases j with (_ | j)
  · simp [givensEmbeddedMatrix, givensLiftEquiv, givensEmbeddedBlockMatrix, Matrix.one_apply]
  · cases h : e j with
    | inl uv =>
        simp [givensEmbeddedMatrix, givensLiftEquiv, givensEmbeddedBlockMatrix, Matrix.one_apply, h]
    | inr g =>
        simp [givensEmbeddedMatrix, givensLiftEquiv, givensEmbeddedBlockMatrix, Matrix.one_apply, h]
  · cases h : e i with
    | inl uv =>
        simp [givensEmbeddedMatrix, givensLiftEquiv, givensEmbeddedBlockMatrix, Matrix.one_apply, h]
    | inr g =>
        simp [givensEmbeddedMatrix, givensLiftEquiv, givensEmbeddedBlockMatrix, Matrix.one_apply, h]
  · cases hi : e i <;> cases hj : e j <;>
      simp [givensEmbeddedMatrix, givensLiftEquiv, givensEmbeddedBlockMatrix, Matrix.one_apply, hi, hj]

lemma isGivensMatrix_blockDiag_one
    {R : Type v} [Semiring R] [Neg R]
    {β : Type u} [Fintype β] [DecidableEq β]
    {Q : Matrix β β R} (hQ : IsGivensMatrix Q) :
    IsGivensMatrix
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 Q : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
  rcases hQ with ⟨γ, _, _, e, c, s, hcs, rfl⟩
  refine ⟨Unit ⊕ γ, inferInstance, inferInstance, givensLiftEquiv e, c, s, hcs, ?_⟩
  simpa using blockDiag_one_givensEmbeddedMatrix (e := e) c s

lemma isGivensProduct_blockDiag_one
    {R : Type v} [Semiring R] [Neg R]
    {β : Type u} [Fintype β] [DecidableEq β]
    {Q : Matrix β β R} (hQ : IsGivensProduct Q) :
    IsGivensProduct
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 Q : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
  exact isProductOf_map
    (fun M : Matrix β β R => IsGivensMatrix M)
    (fun M : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R => IsGivensMatrix M)
    (f := fun M => fromBlocks (1 : Matrix Unit Unit R) 0 0 M)
    (by simp)
    (by
      intro A B
      ext i j <;> rcases i with (_ | i) <;> rcases j with (_ | j) <;>
        simp [Matrix.mul_apply, Fintype.sum_sum_type])
    (by
      intro M hM
      exact isGivensMatrix_blockDiag_one (β := β) hM)
    hQ

section RecursiveStrong

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]

/-- Lift a Givens-flavored QR decomposition of the tail slice back across a QR-ready head-tail split. -/
theorem givensQRReady_headTailSubmatrixLift
    {R : Type v} [Semiring R] [Neg R]
    (A : Matrix ι ι R)
    (hA : QRReady ι A)
    (hP :
      HasGivensQR
        (A.submatrix
          (fun i : QRTailIdx ι => headTailEquiv.symm (Sum.inr i))
          (fun j : QRTailIdx ι => headTailEquiv.symm (Sum.inr j)))) :
    HasGivensQR A := by
  classical
  let e : ι ≃ Unit ⊕ₗ QRTailIdx ι := headTailLexEquiv (α := ι)
  let Ablk : Matrix (Unit ⊕ₗ QRTailIdx ι) (Unit ⊕ₗ QRTailIdx ι) R := Matrix.reindex e e A
  have hSlice :
      A.submatrix
          (fun i : QRTailIdx ι => headTailEquiv.symm (Sum.inr i))
          (fun j : QRTailIdx ι => headTailEquiv.symm (Sum.inr j)) =
        Ablk.toBlocks₂₂ := by
    simpa [Ablk, e] using qr_headTailSlice_eq_tailBlock A
  have hA21 : Ablk.toBlocks₂₁ = 0 := by
    simpa [QRReady, Ablk, e] using hA
  rcases (show HasGivensQR Ablk.toBlocks₂₂ by rwa [hSlice] at hP) with
    ⟨Q', R', hQprod', hQorth', hR', hEq'⟩
  let Qblk : Matrix (Unit ⊕ₗ QRTailIdx ι) (Unit ⊕ₗ QRTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 Q'
  let Rblk : Matrix (Unit ⊕ₗ QRTailIdx ι) (Unit ⊕ₗ QRTailIdx ι) R :=
    fromBlocks Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ 0 R'
  have hEqA :
      A =
        (Matrix.reindex e.symm e.symm Qblk) *
        (Matrix.reindex e.symm e.symm Rblk) := by
    simpa [Qblk, Rblk, Ablk, e] using
      (MatDecompFormal.Components.lift_two_factor_from_zero_block21
        (A := A)
        (e := e)
        (subF₁ := Q')
        (subF₂ := R')
        hA21 hEq')
  refine ⟨Matrix.reindex e.symm e.symm Qblk, Matrix.reindex e.symm e.symm Rblk, ?_, ?_, ?_, hEqA⟩
  · exact isGivensProduct_reindex (e := e.symm) (isGivensProduct_blockDiag_one hQprod')
  · exact
      (isOrthogonalMatrix_reindex
        (e := e)
        (Q := Matrix.reindex e.symm e.symm Qblk)).2
        (by simpa [Qblk] using isOrthogonalMatrix_blockDiag_one hQorth')
  · have hRblk : IsUpperTriangular Rblk := by
      rw [show Rblk = (fromBlocks Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ 0 R' :
        Matrix (Unit ⊕ₗ QRTailIdx ι) (Unit ⊕ₗ QRTailIdx ι) R) by rfl]
      have hUpper := hR'
      dsimp [IsUpperTriangular, BlockTriangular] at hUpper ⊢
      intro i j hij
      rcases i with (_ | i)
      · rcases j with (_ | j)
        · simpa using hij
        · exfalso
          exact Sum.Lex.not_inr_lt_inl hij
      · rcases j with (_ | j)
        · simp
        · exact hUpper (Sum.Lex.inr_lt_inr_iff.mp hij)
    have hRreindexed :
        IsUpperTriangular ((Matrix.reindex e e) (Matrix.reindex e.symm e.symm Rblk)) := by
      simpa using hRblk
    exact
      (isUpperTriangular_reindex
        (e := e)
        (h_mono := headTailLexEquiv_strictMono (α := ι))
        (A := Matrix.reindex e.symm e.symm Rblk)).2 hRreindexed

end RecursiveStrong

def GivensQR_P {R : Type v} [Semiring R] [Neg R] (x : SquareUniverse R) : Prop :=
  HasGivensQR x.A

def GivensQR_P_sub {R : Type v} [Semiring R] [Neg R] (x_sub : PosSquareUniverse R) : Prop :=
  HasGivensQR x_sub.1.A

@[simp] theorem givensQR_P_compat {R : Type v} [Semiring R] [Neg R] (x_sub : PosSquareUniverse R) :
    GivensQR_P_sub x_sub ↔ GivensQR_P (x_sub : SquareUniverse R) :=
  Iff.rfl

/-- Universe-level Givens QR base case used by the generic driver assembler. -/
theorem givensQR_base_univ {R : Type v} [Semiring R] [Neg R] (x : SquareUniverse R) :
    ((∀ (x_sub : PosSquareUniverse R), (x_sub : SquareUniverse R) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      GivensQR_P x := by
  intro hx
  have h_zero : Fintype.card x.ι = 0 :=
    squareSubtypeBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp h_zero
  refine ⟨1, x.A, ?_, ?_, ?_, ?_⟩
  · exact isProductOf_one (fun M => IsGivensMatrix M)
  · exact isOrthogonalMatrix_one
  · exact isUpperTriangular_of_subsingleton x.A
  · simp

noncomputable def qrGivensTransformStrongCS
    {R : Type v} [CommSemiring R] [Neg R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (coeff : QRTailIdx ι → Matrix ι ι R → R × R)
    (horth : ∀ A : Matrix ι ι R,
      IsOrthogonalMatrix (qrGivensSweepQCS coeff (qrGivensTailList ι) A))
    (hprod : ∀ A : Matrix ι ι R,
      IsGivensProduct (qrGivensSweepQCS coeff (qrGivensTailList ι) A))
    (hprodT : ∀ A : Matrix ι ι R,
      IsGivensProduct (qrGivensSweepQCS coeff (qrGivensTailList ι) A)ᵀ)
    (horthT : ∀ A : Matrix ι ι R,
      IsOrthogonalMatrix (qrGivensSweepQCS coeff (qrGivensTailList ι) A)ᵀ)
    (hready : ∀ A : Matrix ι ι R,
      QRReady ι (qrGivensSweepQCS coeff (qrGivensTailList ι) A * A)) :
    MatDecompFormal.Abstractions.Transformation (Matrix ι ι R) where
  T := { Q : Matrix ι ι R //
    IsOrthogonalMatrix Q ∧ IsGivensProduct Q ∧ IsGivensProduct Qᵀ ∧ IsOrthogonalMatrix Qᵀ }
  Goal := QRReady ι
  decGoal := by infer_instance
  apply := fun Q A => Q.1 * A
  find := fun A _ =>
    ⟨qrGivensSweepQCS coeff (qrGivensTailList ι) A,
      ⟨horth A, hprod A, hprodT A, horthT A⟩⟩
  find_spec := by
    intro A _hA
    exact hready A

noncomputable def qrGivensTransformStrong
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    MatDecompFormal.Abstractions.Transformation (Matrix ι ι ℝ) :=
  qrGivensTransformStrongCS ι qrGivensCoeff
    (fun A => isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A)
    (fun A => by simpa [qrGivensSweepQ] using
      qrGivensSweepQ_isGivensProduct (qrGivensTailList ι) A)
    (fun A => by
      simpa [qrGivensSweepQ] using
        isGivensProduct_transpose (qrGivensSweepQ_isGivensProduct (qrGivensTailList ι) A))
    (fun A => by
      exact isOrthogonalMatrix_transpose
        (isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A))
    (fun A => by simpa [qrGivensSweepQ] using qrGivensSweep_ready A)

noncomputable def qrGivensStrategyCoreStrongCS
    {R : Type v} [CommSemiring R] [Neg R]
    (coeff :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        QRTailIdx ι → Matrix ι ι R → R × R)
    (horth :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsOrthogonalMatrix (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A))
    (hprod :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsGivensProduct (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A))
    (hprodT :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsGivensProduct (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A)ᵀ)
    (horthT :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsOrthogonalMatrix (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A)ᵀ)
    (hready :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          QRReady ι (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A * A)) :
    SquareStrategyCore R where
  SliceIdx := fun {ι} fι dι oι nι => @QRTailIdx ι fι oι nι
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
      { transform := qrGivensTransformStrongCS ι (coeff ι) (horth ι) (hprod ι) (hprodT ι) (horthT ι) (hready ι)
        reduction := qrHeadTailSubmatrixReduction ι
        goal_is_sliceable := by
          funext A
          rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (QRTailIdx ι)
        μ_mono := ?_
        slice_progress := ?_ }
    · intro A t
      simp
    · intro A hA
      have hlt : Fintype.card (QRTailIdx ι) < Fintype.card ι := by
        simpa [QRTailIdx] using
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

noncomputable def qrGivensStrategyCoreStrong : SquareStrategyCore ℝ :=
  qrGivensStrategyCoreStrongCS
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] =>
      qrGivensCoeff)
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A =>
      isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A)
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      simpa [qrGivensSweepQ] using qrGivensSweepQ_isGivensProduct (qrGivensTailList ι) A)
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      simpa [qrGivensSweepQ] using
        isGivensProduct_transpose (qrGivensSweepQ_isGivensProduct (qrGivensTailList ι) A))
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      exact isOrthogonalMatrix_transpose
        (isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A))
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      simpa [qrGivensSweepQ] using qrGivensSweep_ready A)

noncomputable def qr_givens_strategy_proof_strongCS
    {R : Type v} [CommSemiring R] [Neg R]
    (coeff :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        QRTailIdx ι → Matrix ι ι R → R × R)
    (horth :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsOrthogonalMatrix (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A))
    (hprod :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsGivensProduct (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A))
    (hprodT :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsGivensProduct (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A)ᵀ)
    (horthT :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          IsOrthogonalMatrix (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A)ᵀ)
    (hready :
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        ∀ A : Matrix ι ι R,
          QRReady ι (qrGivensSweepQCS (coeff ι) (qrGivensTailList ι) A * A)) :
    SquareStrategyProofData R GivensQR_P
      (qrGivensStrategyCoreStrongCS coeff horth hprod hprodT horthT hready) where
  transport := by
    intro ι fι dι oι nι A B hBA hP
    rcases hBA with rfl | ⟨t, rfl⟩
    · exact hP
    · exact givens_transport_of_orthogonal_left_of_transpose t.1 A
        t.2.2.2.1 t.2.1 t.2.2.2.2 hP
  lift := by
    intro ι fι dι oι nι A hA hP
    exact givensQRReady_headTailSubmatrixLift A hA hP

noncomputable def qr_givens_strategy_proof_strong :=
  qr_givens_strategy_proof_strongCS
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] =>
      qrGivensCoeff)
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A =>
      isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A)
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      simpa [qrGivensSweepQ] using qrGivensSweepQ_isGivensProduct (qrGivensTailList ι) A)
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      simpa [qrGivensSweepQ] using
        isGivensProduct_transpose (qrGivensSweepQ_isGivensProduct (qrGivensTailList ι) A))
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      exact isOrthogonalMatrix_transpose
        (isOrthogonalMatrix_qrGivensSweepQ (qrGivensTailList ι) A))
    (fun (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] A => by
      simpa [qrGivensSweepQ] using qrGivensSweep_ready A)

noncomputable def qr_givens_strategy_data_strong : SquareStrategyData ℝ GivensQR_P :=
  mkSquareStrategyData
    qrGivensStrategyCoreStrong
    qr_givens_strategy_proof_strong

noncomputable def qr_givens_framework_inst_strong : SquareSubtypeInductionInstance ℝ :=
  mkSquareSubtypeInductionInstanceFromStrategy
    GivensQR_P
    givensQR_base_univ
    qr_givens_strategy_data_strong

theorem exists_qr_decomposition_givens
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : HasGivensQR A := by
  by_cases h_sub : Subsingleton ι
  · letI := h_sub
    exact base_givensQR_subsingleton A
  · letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp h_sub
    exact SquareSubtypeInductionInstance.prove_for_matrix
      (inst := qr_givens_framework_inst_strong) A

theorem exists_givens_product_qr
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : HasGivensProductQR A :=
  exists_qr_decomposition_givens A

/--
Givens QR with a final-factor product trace.

This records a product representation of the final orthogonal factor; it is not
a recursive step-by-step execution trace of the QR algorithm.
-/
theorem exists_givens_qr_with_product_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : GivensQRTrace A :=
  givensQRTrace_of_hasGivensQR
    (exists_qr_decomposition_givens A)

/--
Compatibility name for the final-factor product trace.
Prefer `exists_givens_qr_with_product_trace` in new code.
-/
theorem exists_givens_qr_with_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : GivensQRTrace A :=
  exists_givens_qr_with_product_trace A

theorem exists_qr_decomposition_givens_hasQR
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : HasQR A := by
  exact hasQR_of_hasGivensQR (exists_qr_decomposition_givens A)

end StrongVariant

end Sweep


end MatDecompFormal.Instances
