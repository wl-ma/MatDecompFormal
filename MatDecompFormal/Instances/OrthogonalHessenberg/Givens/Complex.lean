/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.OrthogonalHessenberg.Concrete
import MatDecompFormal.Instances.QR.Givens
import Mathlib.Analysis.SpecialFunctions.Sqrt

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Complex Givens Unitary Hessenberg Step

This file builds the boundary-column one-step oracle from deterministic
two-coordinate complex Givens rotations and then feeds it to the existing
boundary-column Hessenberg descent driver.
-/

noncomputable def complexGivensRadius (a b : ℂ) : ℝ :=
  Real.sqrt (Complex.normSq a + Complex.normSq b)

lemma complexGivensRadius_sq (a b : ℂ) :
    complexGivensRadius a b ^ 2 = Complex.normSq a + Complex.normSq b := by
  unfold complexGivensRadius
  exact Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg b))

lemma complexGivensRadius_eq_zero_imp (a b : ℂ)
    (h : complexGivensRadius a b = 0) :
    a = 0 ∧ b = 0 := by
  have hs : Complex.normSq a + Complex.normSq b = 0 := by
    have hsq : complexGivensRadius a b ^ 2 = 0 := by simp [h]
    rwa [complexGivensRadius_sq] at hsq
  have ha0 : Complex.normSq a = 0 := by
    nlinarith [Complex.normSq_nonneg a, Complex.normSq_nonneg b]
  have hb0 : Complex.normSq b = 0 := by
    nlinarith [Complex.normSq_nonneg a, Complex.normSq_nonneg b]
  exact ⟨Complex.normSq_eq_zero.mp ha0, Complex.normSq_eq_zero.mp hb0⟩

noncomputable def complexGivensC (a b : ℂ) : ℂ :=
  if _h : complexGivensRadius a b = 0 then 1
  else star a / (complexGivensRadius a b : ℂ)

noncomputable def complexGivensS (a b : ℂ) : ℂ :=
  if _h : complexGivensRadius a b = 0 then 0
  else star b / (complexGivensRadius a b : ℂ)

lemma complexGivens_norm (a b : ℂ) :
    star (complexGivensC a b) * complexGivensC a b +
      star (complexGivensS a b) * complexGivensS a b = 1 := by
  by_cases h : complexGivensRadius a b = 0
  · simp [complexGivensC, complexGivensS, h]
  · have hc : complexGivensC a b = star a / (complexGivensRadius a b : ℂ) := by
      simp [complexGivensC, h]
    have hs : complexGivensS a b = star b / (complexGivensRadius a b : ℂ) := by
      simp [complexGivensS, h]
    rw [hc, hs]
    have hrC : (complexGivensRadius a b : ℂ) ≠ 0 := by exact_mod_cast h
    have hsqC : (complexGivensRadius a b : ℂ) ^ 2 =
        ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) := by
      exact_mod_cast complexGivensRadius_sq a b
    calc
      star (star a / (complexGivensRadius a b : ℂ)) *
            (star a / (complexGivensRadius a b : ℂ)) +
          star (star b / (complexGivensRadius a b : ℂ)) *
            (star b / (complexGivensRadius a b : ℂ))
          = ((Complex.normSq a : ℂ) + (Complex.normSq b : ℂ)) /
              ((complexGivensRadius a b : ℂ) ^ 2) := by
            simp [Complex.conj_ofReal, Complex.normSq_eq_conj_mul_self,
              div_eq_mul_inv]
            ring
      _ = 1 := by
            rw [hsqC]
            have hden :
                (((Complex.normSq a + Complex.normSq b : ℝ) : ℂ)) ≠ 0 := by
              rw [← hsqC]
              exact pow_ne_zero 2 hrC
            field_simp [hden]
            norm_num

lemma complexGivens_annihilate_second (a b : ℂ) :
    -(star (complexGivensS a b)) * a + star (complexGivensC a b) * b = 0 := by
  by_cases h : complexGivensRadius a b = 0
  · rcases complexGivensRadius_eq_zero_imp a b h with ⟨ha, hb⟩
    simp [complexGivensC, complexGivensS, ha, hb]
  · have hc : complexGivensC a b = star a / (complexGivensRadius a b : ℂ) := by
      simp [complexGivensC, h]
    have hs : complexGivensS a b = star b / (complexGivensRadius a b : ℂ) := by
      simp [complexGivensS, h]
    rw [hc, hs]
    simp [Complex.conj_ofReal, div_eq_mul_inv]
    ring

lemma isUnitaryMatrix_conjTranspose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Matrix ι ι ℂ} (hQ : IsUnitaryMatrix Q) :
    IsUnitaryMatrix Qᴴ := by
  constructor
  · simpa using hQ.2
  · simpa using hQ.1

noncomputable def complexGivens2x2CS (c s : ℂ) :
    Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  fromBlocks
    (fun _ _ => c)
    (fun _ _ => s)
    (fun _ _ => -star s)
    (fun _ _ => star c)

lemma isUnitaryMatrix_complexGivens2x2CS (c s : ℂ)
    (hcs : star c * c + star s * s = 1) :
    IsUnitaryMatrix (complexGivens2x2CS c s) := by
  have h₁ : star c * c + s * star s = 1 := by
    calc
      star c * c + s * star s = star c * c + star s * s := by ring
      _ = 1 := hcs
  have h₂ : star s * s + c * star c = 1 := by
    calc
      star s * s + c * star c = star c * c + star s * s := by ring
      _ = 1 := hcs
  have h₃ : c * star c + s * star s = 1 := by
    calc
      c * star c + s * star s = star c * c + star s * s := by ring
      _ = 1 := hcs
  have h₄ : star s * s + star c * c = 1 := by
    calc
      star s * s + star c * c = star c * c + star s * s := by ring
      _ = 1 := hcs
  constructor
  · ext i j
    rcases i with (_ | _) <;> rcases j with (_ | _)
    · simpa [complexGivens2x2CS, Matrix.mul_apply, Fintype.sum_sum_type] using h₁
    · simp [complexGivens2x2CS, Matrix.mul_apply, Fintype.sum_sum_type]
      ring
    · simp [complexGivens2x2CS, Matrix.mul_apply, Fintype.sum_sum_type]
      ring
    · simpa [complexGivens2x2CS, Matrix.mul_apply, Fintype.sum_sum_type] using h₂
  · ext i j
    rcases i with (_ | _) <;> rcases j with (_ | _)
    · simpa [complexGivens2x2CS, Matrix.mul_apply, Fintype.sum_sum_type] using h₃
    · simp [complexGivens2x2CS, Matrix.mul_apply, Fintype.sum_sum_type]
      ring
    · simp [complexGivens2x2CS, Matrix.mul_apply, Fintype.sum_sum_type]
      ring
    · simpa [complexGivens2x2CS, Matrix.mul_apply, Fintype.sum_sum_type] using h₄

noncomputable def complexGivensEmbeddedBlockMatrix
    (γ : Type u) [Fintype γ] [DecidableEq γ] (c s : ℂ) :
    Matrix ((Unit ⊕ Unit) ⊕ γ) ((Unit ⊕ Unit) ⊕ γ) ℂ :=
  fromBlocks (complexGivens2x2CS c s) 0 0 1

noncomputable def complexGivensEmbeddedMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {γ : Type u} [Fintype γ] [DecidableEq γ]
    (e : ι ≃ (Unit ⊕ Unit) ⊕ γ) (c s : ℂ) :
    Matrix ι ι ℂ :=
  Matrix.reindex e.symm e.symm (complexGivensEmbeddedBlockMatrix γ c s)

lemma isUnitaryMatrix_complexGivensEmbeddedBlockMatrix
    {γ : Type u} [Fintype γ] [DecidableEq γ] (c s : ℂ)
    (hcs : star c * c + star s * s = 1) :
    IsUnitaryMatrix (complexGivensEmbeddedBlockMatrix γ c s) := by
  have h2 := isUnitaryMatrix_complexGivens2x2CS c s hcs
  constructor
  · change
      (fromBlocks (complexGivens2x2CS c s) 0 0
          (1 : Matrix γ γ ℂ))ᴴ *
        fromBlocks (complexGivens2x2CS c s) 0 0
          (1 : Matrix γ γ ℂ) = 1
    calc
      (fromBlocks (complexGivens2x2CS c s) 0 0
          (1 : Matrix γ γ ℂ))ᴴ *
        fromBlocks (complexGivens2x2CS c s) 0 0
          (1 : Matrix γ γ ℂ)
          = fromBlocks ((complexGivens2x2CS c s)ᴴ * complexGivens2x2CS c s)
              0 0 (1 : Matrix γ γ ℂ) := by
            simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      _ = fromBlocks (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) 0 0
              (1 : Matrix γ γ ℂ) := by rw [h2.1]
      _ = 1 := Matrix.fromBlocks_one
  · change
      fromBlocks (complexGivens2x2CS c s) 0 0
          (1 : Matrix γ γ ℂ) *
        (fromBlocks (complexGivens2x2CS c s) 0 0
          (1 : Matrix γ γ ℂ))ᴴ = 1
    calc
      fromBlocks (complexGivens2x2CS c s) 0 0
          (1 : Matrix γ γ ℂ) *
        (fromBlocks (complexGivens2x2CS c s) 0 0
          (1 : Matrix γ γ ℂ))ᴴ
          = fromBlocks (complexGivens2x2CS c s * (complexGivens2x2CS c s)ᴴ)
              0 0 (1 : Matrix γ γ ℂ) := by
            simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      _ = fromBlocks (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) 0 0
              (1 : Matrix γ γ ℂ) := by rw [h2.2]
      _ = 1 := Matrix.fromBlocks_one

lemma isUnitaryMatrix_complexGivensEmbeddedMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {γ : Type u} [Fintype γ] [DecidableEq γ]
    (e : ι ≃ (Unit ⊕ Unit) ⊕ γ) (c s : ℂ)
    (hcs : star c * c + star s * s = 1) :
    IsUnitaryMatrix (complexGivensEmbeddedMatrix e c s) := by
  simpa [complexGivensEmbeddedMatrix] using
    isUnitaryMatrix_reindex e.symm
      (isUnitaryMatrix_complexGivensEmbeddedBlockMatrix c s hcs)

noncomputable def complexGivensPairMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (i : QRTailIdx ι) (c s : ℂ) : Matrix ι ι ℂ :=
  complexGivensEmbeddedMatrix (givensPairEquiv i) c s

/--
Concrete complex Givens matrix predicate.

This records a single embedded two-coordinate complex Givens rotation with
normalized coefficients.  Products and traces should use lists of matrices
satisfying this predicate instead of a route tag on an arbitrary unitary factor.
-/
def IsComplexGivensMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (Q : Matrix ι ι ℂ) : Prop :=
  ∃ i : QRTailIdx ι, ∃ c s : ℂ,
    star c * c + star s * s = 1 ∧
      Q = complexGivensPairMatrix i c s

lemma isUnitaryMatrix_complexGivensPairMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (i : QRTailIdx ι) (c s : ℂ)
    (hcs : star c * c + star s * s = 1) :
    IsUnitaryMatrix (complexGivensPairMatrix i c s) :=
  isUnitaryMatrix_complexGivensEmbeddedMatrix (givensPairEquiv i) c s hcs

theorem complexGivensPairMatrix_isComplexGivensMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (i : QRTailIdx ι) (c s : ℂ)
    (hcs : star c * c + star s * s = 1) :
    IsComplexGivensMatrix (complexGivensPairMatrix i c s) :=
  ⟨i, c, s, hcs, rfl⟩

theorem isUnitaryMatrix_of_isComplexGivensMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {Q : Matrix ι ι ℂ} :
    IsComplexGivensMatrix Q → IsUnitaryMatrix Q := by
  intro hQ
  rcases hQ with ⟨i, c, s, hcs, rfl⟩
  exact isUnitaryMatrix_complexGivensPairMatrix i c s hcs

lemma complexGivens2x2CS_conjTranspose (c s : ℂ) :
    (complexGivens2x2CS c s)ᴴ =
      complexGivens2x2CS (star c) (-s) := by
  ext i j
  all_goals rcases i with (_ | _)
  all_goals rcases j with (_ | _)
  all_goals simp [complexGivens2x2CS]

lemma complexGivensEmbeddedBlockMatrix_conjTranspose
    {γ : Type u} [Fintype γ] [DecidableEq γ] (c s : ℂ) :
    (complexGivensEmbeddedBlockMatrix γ c s)ᴴ =
      complexGivensEmbeddedBlockMatrix γ (star c) (-s) := by
  change
    (fromBlocks (complexGivens2x2CS c s) 0 0
        (1 : Matrix γ γ ℂ))ᴴ =
      fromBlocks (complexGivens2x2CS (star c) (-s)) 0 0
        (1 : Matrix γ γ ℂ)
  rw [Matrix.fromBlocks_conjTranspose, complexGivens2x2CS_conjTranspose]
  simp

lemma complexGivensPairMatrix_conjTranspose
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (i : QRTailIdx ι) (c s : ℂ) :
    (complexGivensPairMatrix i c s)ᴴ =
      complexGivensPairMatrix i (star c) (-s) := by
  simp [complexGivensPairMatrix, complexGivensEmbeddedMatrix,
    complexGivensEmbeddedBlockMatrix_conjTranspose]

theorem isComplexGivensMatrix_conjTranspose
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {Q : Matrix ι ι ℂ} :
    IsComplexGivensMatrix Q → IsComplexGivensMatrix Qᴴ := by
  intro hQ
  rcases hQ with ⟨i, c, s, hcs, rfl⟩
  refine ⟨i, star c, -s, ?_, ?_⟩
  · calc
      star (star c) * star c + star (-s) * (-s)
          = star c * c + star s * s := by
            simp
            ring_nf
      _ = 1 := hcs
  · exact complexGivensPairMatrix_conjTranspose i c s

lemma complexGivensPairMatrix_mul_apply_target_head
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (i : QRTailIdx ι) (c s : ℂ) (A : Matrix ι ι ℂ) :
    ((complexGivensPairMatrix i c s) * A) i.1 (headElem (α := ι)) =
      -star s * A (headElem (α := ι)) (headElem (α := ι)) +
        star c * A i.1 (headElem (α := ι)) := by
  let e := givensPairEquiv i
  let Ablk := Matrix.reindex e e A
  have hmul :
      (complexGivensPairMatrix i c s) * A =
        Matrix.reindex e.symm e.symm
          (complexGivensEmbeddedBlockMatrix (GivensRestIdx i) c s * Ablk) := by
    simpa [complexGivensPairMatrix, complexGivensEmbeddedMatrix,
      Ablk, e] using
      (Matrix.reindexLinearEquiv_mul ℂ ℂ e.symm e.symm e.symm
        (complexGivensEmbeddedBlockMatrix (GivensRestIdx i) c s) Ablk)
  have hentry := congrArg (fun M => M i.1 (headElem (α := ι))) hmul
  simpa [Ablk, e, complexGivensEmbeddedBlockMatrix, complexGivens2x2CS,
    Matrix.mul_apply, Fintype.sum_sum_type, Matrix.reindex_apply] using hentry

lemma complexGivensPairMatrix_mul_apply_other_head
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (i k : QRTailIdx ι) (c s : ℂ) (A : Matrix ι ι ℂ) (hk : k ≠ i) :
    ((complexGivensPairMatrix i c s) * A) k.1 (headElem (α := ι)) =
      A k.1 (headElem (α := ι)) := by
  let e := givensPairEquiv i
  let Ablk := Matrix.reindex e e A
  let krest : GivensRestIdx i := ⟨k, hk⟩
  have hkrow : e k.1 = Sum.inr krest := by
    apply e.symm.injective
    simp [e, krest, givensPairEquiv, givensTailSplitEquiv]
  have hmul :
      (complexGivensPairMatrix i c s) * A =
        Matrix.reindex e.symm e.symm
          (complexGivensEmbeddedBlockMatrix (GivensRestIdx i) c s * Ablk) := by
    simpa [complexGivensPairMatrix, complexGivensEmbeddedMatrix,
      Ablk, e] using
      (Matrix.reindexLinearEquiv_mul ℂ ℂ e.symm e.symm e.symm
        (complexGivensEmbeddedBlockMatrix (GivensRestIdx i) c s) Ablk)
  have hentry := congrArg (fun M => M k.1 (headElem (α := ι))) hmul
  simpa [Ablk, e, krest, hkrow, complexGivensEmbeddedBlockMatrix,
    Matrix.mul_apply, Fintype.sum_sum_type, Matrix.reindex_apply, Matrix.one_apply] using hentry

noncomputable def complexGivensCoeff
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (i : QRTailIdx ι) (A : Matrix ι ι ℂ) : ℂ × ℂ :=
  (complexGivensC (A (headElem (α := ι)) (headElem (α := ι)))
      (A i.1 (headElem (α := ι))),
    complexGivensS (A (headElem (α := ι)) (headElem (α := ι)))
      (A i.1 (headElem (α := ι))))

lemma complexGivensCoeff_norm
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (i : QRTailIdx ι) (A : Matrix ι ι ℂ) :
    let cs := complexGivensCoeff i A
    star cs.1 * cs.1 + star cs.2 * cs.2 = 1 := by
  simpa [complexGivensCoeff] using
    complexGivens_norm
      (A (headElem (α := ι)) (headElem (α := ι)))
      (A i.1 (headElem (α := ι)))

lemma complexGivensCoeff_zero
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (i : QRTailIdx ι) (A : Matrix ι ι ℂ) :
    let cs := complexGivensCoeff i A
    ((complexGivensPairMatrix i cs.1 cs.2) * A) i.1 (headElem (α := ι)) = 0 := by
  dsimp [complexGivensCoeff]
  rw [complexGivensPairMatrix_mul_apply_target_head]
  exact complexGivens_annihilate_second
    (A (headElem (α := ι)) (headElem (α := ι)))
    (A i.1 (headElem (α := ι)))

lemma complexGivensCoeff_pair_isComplexGivensMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (i : QRTailIdx ι) (A : Matrix ι ι ℂ) :
    let cs := complexGivensCoeff i A
    IsComplexGivensMatrix (complexGivensPairMatrix i cs.1 cs.2) := by
  exact complexGivensPairMatrix_isComplexGivensMatrix i _ _
    (by simpa using complexGivensCoeff_norm i A)

noncomputable def complexGivensSweepMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    List (QRTailIdx ι) → Matrix ι ι ℂ → Matrix ι ι ℂ
  | [], A => A
  | i :: is, A =>
      let cs := complexGivensCoeff i A
      complexGivensSweepMatrix is ((complexGivensPairMatrix i cs.1 cs.2) * A)

noncomputable def complexGivensSweepQ
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    List (QRTailIdx ι) → Matrix ι ι ℂ → Matrix ι ι ℂ
  | [], _ => 1
  | i :: is, A =>
      let cs := complexGivensCoeff i A
      let G := complexGivensPairMatrix i cs.1 cs.2
      let A' := G * A
      complexGivensSweepQ is A' * G

lemma complexGivensSweepQ_mul_eq
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι ℂ),
      complexGivensSweepQ l A * A = complexGivensSweepMatrix l A
  | [], A => by simp [complexGivensSweepQ, complexGivensSweepMatrix]
  | i :: is, A => by
      simp [complexGivensSweepQ, complexGivensSweepMatrix,
        complexGivensSweepQ_mul_eq, Matrix.mul_assoc]

lemma complexGivensSweepQ_unitary
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι ℂ),
      IsUnitaryMatrix (complexGivensSweepQ l A)
  | [], A => by
      simpa [complexGivensSweepQ] using (isUnitaryMatrix_one : IsUnitaryMatrix (1 : Matrix ι ι ℂ))
  | i :: is, A => by
      simp only [complexGivensSweepQ]
      let cs := complexGivensCoeff i A
      let G := complexGivensPairMatrix i cs.1 cs.2
      let A' := G * A
      exact isUnitaryMatrix_mul
        (complexGivensSweepQ_unitary is A')
        (isUnitaryMatrix_complexGivensPairMatrix i cs.1 cs.2
          (by simpa [cs] using complexGivensCoeff_norm i A))

noncomputable def complexGivensSweepSteps
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    List (QRTailIdx ι) → Matrix ι ι ℂ → List (Matrix ι ι ℂ)
  | [], _ => []
  | i :: is, A =>
      let cs := complexGivensCoeff i A
      let G := complexGivensPairMatrix i cs.1 cs.2
      let A' := G * A
      complexGivensSweepSteps is A' ++ [G]

lemma complexGivensSweepSteps_all
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι ℂ),
      ∀ M ∈ complexGivensSweepSteps l A, IsComplexGivensMatrix M
  | [], _A, M, hM => by
      cases hM
  | i :: is, A, M, hM => by
      simp only [complexGivensSweepSteps, List.mem_append, List.mem_singleton]
        at hM
      let cs := complexGivensCoeff i A
      let G := complexGivensPairMatrix i cs.1 cs.2
      let A' := G * A
      rcases hM with hM | hM
      · exact complexGivensSweepSteps_all is A' M hM
      · subst M
        exact complexGivensCoeff_pair_isComplexGivensMatrix i A

lemma matrixProduct_append_singleton
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (l : List (Matrix ι ι ℂ)) (G : Matrix ι ι ℂ) :
    matrixProduct (l ++ [G]) = matrixProduct l * G := by
  rw [matrixProduct_eq_prod, List.prod_append, List.prod_singleton,
    ← matrixProduct_eq_prod]

lemma complexGivensSweepSteps_product
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι ℂ),
      matrixProduct (complexGivensSweepSteps l A) =
        complexGivensSweepQ l A
  | [], A => by
      simp [complexGivensSweepSteps, complexGivensSweepQ, matrixProduct]
  | i :: is, A => by
      let cs := complexGivensCoeff i A
      let G := complexGivensPairMatrix i cs.1 cs.2
      let A' := G * A
      calc
        matrixProduct (complexGivensSweepSteps (i :: is) A)
            = matrixProduct (complexGivensSweepSteps is A' ++ [G]) := by
              rfl
        _ = matrixProduct (complexGivensSweepSteps is A') * G :=
              matrixProduct_append_singleton _ _
        _ = complexGivensSweepQ is A' * G := by
              rw [complexGivensSweepSteps_product is A']
        _ = complexGivensSweepQ (i :: is) A := by
              simp [complexGivensSweepQ, cs, G, A']

noncomputable def complexGivensSweepAdjointSteps
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (l : List (QRTailIdx ι)) (A : Matrix ι ι ℂ) :
    List (Matrix ι ι ℂ) :=
  (complexGivensSweepSteps l A).map Matrix.conjTranspose |>.reverse

lemma complexGivensSweepAdjointSteps_all
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (l : List (QRTailIdx ι)) (A : Matrix ι ι ℂ) :
    ∀ M ∈ complexGivensSweepAdjointSteps l A, IsComplexGivensMatrix M := by
  intro M hM
  rw [complexGivensSweepAdjointSteps] at hM
  rcases List.mem_reverse.mp hM with hM
  rcases List.mem_map.mp hM with ⟨N, hN, rfl⟩
  exact isComplexGivensMatrix_conjTranspose
    (complexGivensSweepSteps_all l A N hN)

lemma matrixProduct_conjTranspose_reverse
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (l : List (Matrix ι ι ℂ)) :
    matrixProduct ((l.map Matrix.conjTranspose).reverse) =
      (matrixProduct l)ᴴ := by
  calc
    matrixProduct ((l.map Matrix.conjTranspose).reverse)
        = ((l.map Matrix.conjTranspose).reverse).prod := matrixProduct_eq_prod _
    _ = l.prodᴴ := by
        rw [← Matrix.conjTranspose_list_prod l]
    _ = (matrixProduct l)ᴴ := by
        rw [matrixProduct_eq_prod]

lemma complexGivensSweepAdjointSteps_product
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (l : List (QRTailIdx ι)) (A : Matrix ι ι ℂ) :
    matrixProduct (complexGivensSweepAdjointSteps l A) =
      (complexGivensSweepQ l A)ᴴ := by
  rw [complexGivensSweepAdjointSteps,
    matrixProduct_conjTranspose_reverse,
    complexGivensSweepSteps_product l A]

lemma complexGivensSweepMatrix_preserves_head_of_not_mem
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    ∀ (l : List (QRTailIdx ι)) (A : Matrix ι ι ℂ) {k : QRTailIdx ι},
      k ∉ l →
        complexGivensSweepMatrix l A k.1 (headElem (α := ι)) =
          A k.1 (headElem (α := ι))
  | [], A, k, _ => by simp [complexGivensSweepMatrix]
  | i :: is, A, k, hk => by
      have hk_ne : k ≠ i := by
        intro h
        exact hk (by simp [h])
      have hk_tail : k ∉ is := by
        intro hmem
        exact hk (by simp [hmem])
      let cs := complexGivensCoeff i A
      calc
        complexGivensSweepMatrix (i :: is) A k.1 (headElem (α := ι))
            = complexGivensSweepMatrix is ((complexGivensPairMatrix i cs.1 cs.2) * A)
                k.1 (headElem (α := ι)) := by simp [complexGivensSweepMatrix, cs]
        _ = ((complexGivensPairMatrix i cs.1 cs.2) * A) k.1 (headElem (α := ι)) :=
              complexGivensSweepMatrix_preserves_head_of_not_mem is
                ((complexGivensPairMatrix i cs.1 cs.2) * A) hk_tail
        _ = A k.1 (headElem (α := ι)) :=
              complexGivensPairMatrix_mul_apply_other_head i k cs.1 cs.2 A hk_ne

lemma complexGivensSweepMatrix_zero_of_mem
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    ∀ {l : List (QRTailIdx ι)} (_hnd : l.Nodup) (A : Matrix ι ι ℂ)
      {k : QRTailIdx ι},
      k ∈ l → complexGivensSweepMatrix l A k.1 (headElem (α := ι)) = 0
  | [], _hnd, A, k, hk => by cases hk
  | i :: is, hnd, A, k, hk => by
      rcases List.nodup_cons.mp hnd with ⟨hi_not_mem, hnd_tail⟩
      rcases List.mem_cons.mp hk with hk_head | hk_tail
      · subst hk_head
        let cs := complexGivensCoeff k A
        calc
          complexGivensSweepMatrix (k :: is) A k.1 (headElem (α := ι))
              = complexGivensSweepMatrix is ((complexGivensPairMatrix k cs.1 cs.2) * A)
                  k.1 (headElem (α := ι)) := by simp [complexGivensSweepMatrix, cs]
          _ = ((complexGivensPairMatrix k cs.1 cs.2) * A) k.1 (headElem (α := ι)) :=
                complexGivensSweepMatrix_preserves_head_of_not_mem is
                  ((complexGivensPairMatrix k cs.1 cs.2) * A) hi_not_mem
          _ = 0 := by simpa [cs] using complexGivensCoeff_zero k A
      · let cs := complexGivensCoeff i A
        calc
          complexGivensSweepMatrix (i :: is) A k.1 (headElem (α := ι))
              = complexGivensSweepMatrix is ((complexGivensPairMatrix i cs.1 cs.2) * A)
                  k.1 (headElem (α := ι)) := by simp [complexGivensSweepMatrix, cs]
          _ = 0 := complexGivensSweepMatrix_zero_of_mem hnd_tail
            ((complexGivensPairMatrix i cs.1 cs.2) * A) hk_tail

lemma complexGivensSweep_ready
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) :
    QRReady ι (complexGivensSweepQ (qrGivensTailList ι) A * A) := by
  rw [complexGivensSweepQ_mul_eq]
  ext i j
  cases j
  have hi_mem : i ∈ qrGivensTailList ι := by
    simp [qrGivensTailList]
  simpa [QRReady, Matrix.toBlocks₂₁, Matrix.reindex_apply,
    headTailEquiv_symm_apply_inl, headTailEquiv_symm_apply_inr] using
    (complexGivensSweepMatrix_zero_of_mem
      ((Finset.univ : Finset (QRTailIdx ι)).nodup_toList) A hi_mem)

noncomputable def givensBoundaryColumnMatrix
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    Matrix x_sub.1.ι x_sub.1.ι ℂ := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact fun i j => if j = headElem (α := x_sub.1.ι) then x_sub.1.c i () else 0

noncomputable def givensBoundarySweepH
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    Matrix x_sub.1.ι x_sub.1.ι ℂ := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact complexGivensSweepQ (qrGivensTailList x_sub.1.ι)
    (givensBoundaryColumnMatrix x_sub)

noncomputable def givensBoundaryStepQ
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    Matrix x_sub.1.ι x_sub.1.ι ℂ :=
  (givensBoundarySweepH x_sub)ᴴ

theorem givens_boundary_step_unitary
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    IsUnitaryMatrix (givensBoundaryStepQ x_sub) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact isUnitaryMatrix_conjTranspose
    (complexGivensSweepQ_unitary
      (qrGivensTailList x_sub.1.ι)
      (givensBoundaryColumnMatrix x_sub))

lemma givensBoundarySweep_column_zero
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ)
    (i : x_sub.1.ι)
    (hi : letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
      i ≠ headElem (α := x_sub.1.ι)) :
    letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
    (givensBoundarySweepH x_sub * givensBoundaryColumnMatrix x_sub)
        i (headElem (α := x_sub.1.ι)) = 0 := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  let k : QRTailIdx x_sub.1.ι := ⟨i, hi⟩
  have hready :
      QRReady x_sub.1.ι
        (givensBoundarySweepH x_sub * givensBoundaryColumnMatrix x_sub) := by
    simpa [givensBoundarySweepH] using
      complexGivensSweep_ready (givensBoundaryColumnMatrix x_sub)
  have hentry :
      (Matrix.reindex (headTailEquiv (α := x_sub.1.ι))
          (headTailEquiv (α := x_sub.1.ι))
          (givensBoundarySweepH x_sub * givensBoundaryColumnMatrix x_sub)).toBlocks₂₁
          k () = 0 := by
    simpa [QRReady] using congrFun (congrFun hready k) ()
  simpa [Matrix.toBlocks₂₁, Matrix.reindex_apply, k] using hentry

lemma givensBoundarySweep_mul_column_zero
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ)
    (i : x_sub.1.ι)
    (hi : letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
      i ≠ headElem (α := x_sub.1.ι)) :
    (givensBoundarySweepH x_sub * x_sub.1.c) i () = 0 := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  have hentry := givensBoundarySweep_column_zero x_sub i hi
  simpa [Matrix.mul_apply, givensBoundaryColumnMatrix] using hentry

theorem givens_boundary_step_ready
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    HessenbergBoundaryReady
      (unitaryHessenbergBoundarySimilarityObject
        (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
        (givensBoundaryStepQ x_sub)) := by
  classical
  intro _hne i hi
  simpa [unitaryHessenbergBoundarySimilarityObject, givensBoundaryStepQ] using
    givensBoundarySweep_mul_column_zero x_sub i hi

theorem givensBoundaryStepQ_isProductOfComplexGivensMatrix
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    IsProductOf
      (@IsComplexGivensMatrix x_sub.1.ι x_sub.1.fintype_ι
        x_sub.1.decEq_ι x_sub.1.linOrder_ι
        (posHessenbergBoundaryUniverse_nonempty x_sub))
      (givensBoundaryStepQ x_sub) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  refine
    ⟨complexGivensSweepAdjointSteps
      (qrGivensTailList x_sub.1.ι)
      (givensBoundaryColumnMatrix x_sub), ?_, ?_⟩
  · exact complexGivensSweepAdjointSteps_all
      (qrGivensTailList x_sub.1.ι)
      (givensBoundaryColumnMatrix x_sub)
  · simpa [givensBoundaryStepQ, givensBoundarySweepH] using
      complexGivensSweepAdjointSteps_product
        (qrGivensTailList x_sub.1.ι)
        (givensBoundaryColumnMatrix x_sub)

noncomputable def givensUnitaryBoundaryStepOracle :
    UnitaryHessenbergBoundaryStepOracle.{u} where
  Q := givensBoundaryStepQ
  unitary_Q := givens_boundary_step_unitary
  ready := givens_boundary_step_ready

theorem exists_unitary_hessenberg_reduction_givens
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasUnitaryHessenberg A :=
  exists_unitary_hessenberg_reduction givensUnitaryBoundaryStepOracle A

/--
Concrete step-trace data for the complex Givens Hessenberg route.

The boundary sweep is expanded into the concrete list of embedded two-coordinate
Givens rotations whose product is the boundary oracle matrix.
-/
structure ComplexGivensHessenbergStepTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) : Prop where
  decomposition : HasUnitaryHessenberg A
  boundaryStepProduct :
    ∀ x_sub : PosHessenbergBoundaryUniverse.{u} ℂ,
      IsProductOf
        (@IsComplexGivensMatrix x_sub.1.ι x_sub.1.fintype_ι
          x_sub.1.decEq_ι x_sub.1.linOrder_ι
          (posHessenbergBoundaryUniverse_nonempty x_sub))
        (givensBoundaryStepQ x_sub)

theorem hasUnitaryHessenberg_of_complexGivensHessenbergStepTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ} :
    ComplexGivensHessenbergStepTrace A → HasUnitaryHessenberg A :=
  ComplexGivensHessenbergStepTrace.decomposition

/--
Complex Givens Hessenberg route with boundary-step product data.

This records the boundary oracle products used by the framework route; it is
not a full recursive embedded-step execution trace.
-/
theorem exists_unitary_hessenberg_reduction_givens_with_boundary_step_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    ComplexGivensHessenbergStepTrace A := by
  exact
    { decomposition := exists_unitary_hessenberg_reduction_givens A
      boundaryStepProduct := fun x_sub =>
        givensBoundaryStepQ_isProductOfComplexGivensMatrix x_sub }

/--
Compatibility name for the boundary-step trace.
Prefer `exists_unitary_hessenberg_reduction_givens_with_boundary_step_trace`.
-/
theorem exists_unitary_hessenberg_reduction_givens_with_step_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    ComplexGivensHessenbergStepTrace A :=
  exists_unitary_hessenberg_reduction_givens_with_boundary_step_trace A

/--
Compatibility witness trace for the Givens boundary route.

This route-tagged witness records the final unitary Hessenberg decomposition,
not the recursive boundary-step execution sequence.
-/
theorem exists_unitary_hessenberg_reduction_givens_with_witness_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    UnitaryHessenbergTrace "complex-givens-boundary" A :=
  witnessData_of_hasUnitaryHessenberg
    "complex-givens-boundary"
    (hasUnitaryHessenberg_of_complexGivensHessenbergStepTrace
      (exists_unitary_hessenberg_reduction_givens_with_boundary_step_trace A))

/--
Compatibility name for the route-tagged final witness trace.
Prefer `exists_unitary_hessenberg_reduction_givens_with_witness_trace`.
-/
theorem exists_unitary_hessenberg_reduction_givens_with_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    UnitaryHessenbergTrace "complex-givens-boundary" A :=
  exists_unitary_hessenberg_reduction_givens_with_witness_trace A

end MatDecompFormal.Instances
