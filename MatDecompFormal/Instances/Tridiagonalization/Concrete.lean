import MatDecompFormal.Instances.Tridiagonalization.Boundary
import MatDecompFormal.Instances.OrthogonalHessenberg.Concrete
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

universe u

namespace MatDecompFormal.Instances

open Matrix
open InnerProductSpace
open MatDecompFormal.Framework

/-!
# Concrete Tridiagonalization Step

This file starts the concrete Householder/Gram-Schmidt discharge of the
boundary-aware tridiagonalization step oracle.  The one-step matrix is chosen
from a Gram-Schmidt orthonormal basis whose first input vector is the active
boundary column and whose second input vector is `A q₀`.  The triangularity
lemma for `gramSchmidtOrthonormalBasis` is the intended source of the
first-column tridiagonal readiness proof.
-/

/-- Local finite-order instances needed by mathlib's Gram-Schmidt API. -/
noncomputable abbrev tridiagonalizationLocallyFiniteOrder
    (ι : Type u) [Fintype ι] [LinearOrder ι] :
    LocallyFiniteOrder ι :=
  Fintype.toLocallyFiniteOrder

/-- Local bottom instance with the project-standard head element. -/
noncomputable abbrev tridiagonalizationOrderBot
    (ι : Type u) [Fintype ι] [LinearOrder ι] [Nonempty ι] :
    OrderBot ι where
  bot := headElem (α := ι)
  bot_le := headElem_le (α := ι)

/--
First vector used by the concrete step.

When the protected boundary column is nonzero, this is its normalized vector;
otherwise it falls back to the standard head basis vector.
-/
noncomputable def tridiagonalizationFirstVec
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (c : Matrix ι Unit ℂ) : EuclideanSpace ℂ ι := by
  classical
  exact
    if hc : c = 0 then
      EuclideanSpace.basisFun ι ℂ (headElem (α := ι))
    else
      normalizedBoundaryColumn c hc

lemma tridiagonalizationFirstVec_norm
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (c : Matrix ι Unit ℂ) :
    ‖tridiagonalizationFirstVec c‖ = 1 := by
  classical
  unfold tridiagonalizationFirstVec
  by_cases hc : c = 0
  · simp [hc]
  · simp [hc, normalizedBoundaryColumn_norm c hc]

/-- The ordered vector family fed to Gram-Schmidt for one tridiagonalization step. -/
noncomputable def tridiagonalizationGramSchmidtInput
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (c : Matrix ι Unit ℂ) :
    ι → EuclideanSpace ℂ ι := by
  classical
  exact fun i =>
    if i = headElem (α := ι) then
      tridiagonalizationFirstVec c
    else
      WithLp.toLp 2 (A *ᵥ (tridiagonalizationFirstVec c).ofLp)

/-- Gram-Schmidt orthonormal basis used by the concrete tridiagonalization step. -/
noncomputable def tridiagonalizationStepBasis
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (c : Matrix ι Unit ℂ) :
    OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι) := by
  letI : LocallyFiniteOrder ι := tridiagonalizationLocallyFiniteOrder ι
  letI : OrderBot ι := tridiagonalizationOrderBot ι
  exact
    InnerProductSpace.gramSchmidtOrthonormalBasis
      (𝕜 := ℂ) (E := EuclideanSpace ℂ ι) (ι := ι)
      (by simp)
      (tridiagonalizationGramSchmidtInput A c)

lemma tridiagonalizationStepBasis_head
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (c : Matrix ι Unit ℂ) :
    tridiagonalizationStepBasis A c (headElem (α := ι)) =
      tridiagonalizationFirstVec c := by
  classical
  unfold tridiagonalizationStepBasis
  letI : LocallyFiniteOrder ι := tridiagonalizationLocallyFiniteOrder ι
  letI : OrderBot ι := tridiagonalizationOrderBot ι
  let f : ι → EuclideanSpace ℂ ι := tridiagonalizationGramSchmidtInput A c
  have hbot : (⊥ : ι) = headElem (α := ι) := rfl
  have hf_bot : f (⊥ : ι) = tridiagonalizationFirstVec c := by
    simp [f, tridiagonalizationGramSchmidtInput, hbot]
  have hgs : InnerProductSpace.gramSchmidt ℂ f (headElem (α := ι)) =
      tridiagonalizationFirstVec c := by
    rw [← hbot]
    simpa [hf_bot] using
      (InnerProductSpace.gramSchmidt_bot (𝕜 := ℂ) (f := f))
  have hfirst_ne : tridiagonalizationFirstVec c ≠ 0 := by
    intro hzero
    have hnorm := congrArg norm hzero
    rw [tridiagonalizationFirstVec_norm c] at hnorm
    norm_num at hnorm
  have hnormed_ne :
      InnerProductSpace.gramSchmidtNormed ℂ f (headElem (α := ι)) ≠ 0 := by
    simp [InnerProductSpace.gramSchmidtNormed, hgs, hfirst_ne,
      tridiagonalizationFirstVec_norm c]
  rw [InnerProductSpace.gramSchmidtOrthonormalBasis_apply]
  · rw [InnerProductSpace.gramSchmidtNormed, hgs]
    simpa [tridiagonalizationFirstVec_norm c]
  · exact hnormed_ne

/-- Candidate concrete unitary factor for the boundary-aware tridiagonalization step. -/
noncomputable def tridiagonalizationConcreteStepQ
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    Matrix x_sub.1.ι x_sub.1.ι ℂ := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact matrixOfOrthonormalBasis
    (tridiagonalizationStepBasis x_sub.1.A x_sub.1.c)

lemma tridiagonalizationConcreteStepQ_unitary
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    IsUnitaryMatrix (tridiagonalizationConcreteStepQ x_sub) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact matrixOfOrthonormalBasis_unitary
    (tridiagonalizationStepBasis x_sub.1.A x_sub.1.c)

lemma tridiagonalizationConcreteStepQ_ready_boundary
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    ∀ i : x_sub.1.ι, 0 < finiteOrderRank x_sub.1.ι i →
      ((tridiagonalizationConcreteStepQ x_sub)ᴴ * x_sub.1.c) i () = 0 := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  intro i hi
  by_cases hc : x_sub.1.c = 0
  · simp [tridiagonalizationConcreteStepQ, hc]
  · let b : OrthonormalBasis x_sub.1.ι ℂ (EuclideanSpace ℂ x_sub.1.ι) :=
      tridiagonalizationStepBasis x_sub.1.A x_sub.1.c
    let Q : Matrix x_sub.1.ι x_sub.1.ι ℂ := matrixOfOrthonormalBasis b
    let v : EuclideanSpace ℂ x_sub.1.ι := boundaryColumnVec x_sub.1.c
    have hbhead : b (headElem (α := x_sub.1.ι)) =
        normalizedBoundaryColumn x_sub.1.c hc := by
      simpa [b, tridiagonalizationFirstVec, hc] using
        tridiagonalizationStepBasis_head x_sub.1.A x_sub.1.c
    have hneNorm : ‖v‖ ≠ 0 := by
      simpa [v] using boundaryColumnVec_ne_zero hc
    have hvec : v = (‖v‖ : ℂ) • b (headElem (α := x_sub.1.ι)) := by
      calc
        v = (‖v‖ : ℂ) • (((‖v‖ : ℂ)⁻¹) • v) := by
          rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hneNorm), one_smul]
        _ = (‖v‖ : ℂ) • b (headElem (α := x_sub.1.ι)) := by
          rw [hbhead]
          simp [normalizedBoundaryColumn, v]
    have hvec_ofLp :
        v.ofLp = (‖v‖ : ℂ) • (b (headElem (α := x_sub.1.ι))).ofLp := by
      exact congrArg WithLp.ofLp hvec
    have hmul :
        Qᴴ *ᵥ v.ofLp =
          (‖v‖ : ℂ) •
            (Pi.single (headElem (α := x_sub.1.ι)) (1 : ℂ) :
              x_sub.1.ι → ℂ) := by
      calc
        Qᴴ *ᵥ v.ofLp =
            Qᴴ *ᵥ ((‖v‖ : ℂ) • (b (headElem (α := x_sub.1.ι))).ofLp) := by
              rw [hvec_ofLp]
        _ = (‖v‖ : ℂ) •
            (Qᴴ *ᵥ (b (headElem (α := x_sub.1.ι))).ofLp) := by
              rw [mulVec_smul]
        _ = (‖v‖ : ℂ) •
            (Pi.single (headElem (α := x_sub.1.ι)) (1 : ℂ) :
              x_sub.1.ι → ℂ) := by
              simpa [Q] using
                congrArg ((‖v‖ : ℂ) • ·)
                  (conjTranspose_matrixOfOrthonormalBasis_mulVec b
                    (headElem (α := x_sub.1.ι)))
    have hne_head : i ≠ headElem (α := x_sub.1.ι) :=
      ne_headElem_of_finiteOrderRank_pos x_sub.1.ι hi
    have hentry := congrFun hmul i
    have hzero :
        (Qᴴ *ᵥ v.ofLp) i = 0 := by
      simpa [hne_head] using hentry
    simpa [tridiagonalizationConcreteStepQ, Q, v, boundaryColumnVec,
      Matrix.mulVec, Matrix.mul_apply] using hzero

lemma conjTranspose_matrixOfOrthonormalBasis_mulVec_apply
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (v : EuclideanSpace ℂ ι) (i : ι) :
    ((matrixOfOrthonormalBasis b)ᴴ *ᵥ v.ofLp) i = ⟪b i, v⟫_ℂ := by
  simp [matrixOfOrthonormalBasis, Matrix.mulVec, Matrix.conjTranspose_apply,
    Module.Basis.toMatrix_apply, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]
  rfl

lemma exists_between_head_and_tail_of_tail_rank_pos
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    [Fintype (TridiagonalTailIdx ι)]
    (i : TridiagonalTailIdx ι)
    (hi : 0 < finiteOrderRank (TridiagonalTailIdx ι) i) :
    ∃ j : ι, headElem (α := ι) < j ∧ j < (i : ι) := by
  unfold finiteOrderRank at hi
  rw [Fintype.card_pos_iff] at hi
  rcases hi with ⟨j⟩
  exact ⟨j.1.1,
    lt_of_le_of_ne (headElem_le (α := ι) j.1.1) j.1.2.symm,
    j.2⟩

lemma tridiagonalizationStepBasis_inner_A_firstVec_zero_of_tail_rank_pos
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (c : Matrix ι Unit ℂ)
    (i : TridiagonalTailIdx ι)
    (hi : 0 < finiteOrderRank (TridiagonalTailIdx ι) i) :
    ⟪tridiagonalizationStepBasis A c i,
      WithLp.toLp 2 (A *ᵥ (tridiagonalizationFirstVec c).ofLp)⟫_ℂ = 0 := by
  classical
  letI : LocallyFiniteOrder ι := tridiagonalizationLocallyFiniteOrder ι
  letI : OrderBot ι := tridiagonalizationOrderBot ι
  let f : ι → EuclideanSpace ℂ ι := tridiagonalizationGramSchmidtInput A c
  have hbetween := exists_between_head_and_tail_of_tail_rank_pos i hi
  rcases hbetween with ⟨j, hheadj, hji⟩
  have hfj :
      f j = WithLp.toLp 2 (A *ᵥ (tridiagonalizationFirstVec c).ofLp) := by
    simp [f, tridiagonalizationGramSchmidtInput,
      ne_of_gt hheadj]
  have htri :
      ⟪tridiagonalizationStepBasis A c i, f j⟫_ℂ = 0 := by
    simpa [tridiagonalizationStepBasis, f] using
      (InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular
        (𝕜 := ℂ) (E := EuclideanSpace ℂ ι)
        (h := by simp)
        (f := f)
        (i := j) (j := (i : ι)) hji)
  simpa [hfj] using htri

lemma tridiagonalizationConcreteStepQ_ready_matrix
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ)
    (_hne : Nonempty x_sub.1.ι) :
    TridiagonalizationReady x_sub.1.ι
      ((tridiagonalizationConcreteStepQ x_sub)ᴴ * x_sub.1.A *
        tridiagonalizationConcreteStepQ x_sub) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  intro i hi
  let b : OrthonormalBasis x_sub.1.ι ℂ (EuclideanSpace ℂ x_sub.1.ι) :=
    tridiagonalizationStepBasis x_sub.1.A x_sub.1.c
  let Q : Matrix x_sub.1.ι x_sub.1.ι ℂ := matrixOfOrthonormalBasis b
  have hQeq : tridiagonalizationConcreteStepQ x_sub = Q := by
    rfl
  have hhead_col :
      Q *ᵥ (Pi.single (headElem (α := x_sub.1.ι)) (1 : ℂ) :
          x_sub.1.ι → ℂ) =
        (tridiagonalizationFirstVec x_sub.1.c).ofLp := by
    rw [matrixOfOrthonormalBasis_mulVec_single]
    rw [tridiagonalizationStepBasis_head]
  have hentry :
      ((Qᴴ * x_sub.1.A * Q)
          ((headTailEquiv (α := x_sub.1.ι)).symm (Sum.inr i))
          ((headTailEquiv (α := x_sub.1.ι)).symm (Sum.inl ()))) =
        (Qᴴ *ᵥ
          (x_sub.1.A *ᵥ (tridiagonalizationFirstVec x_sub.1.c).ofLp))
          ((headTailEquiv (α := x_sub.1.ι)).symm (Sum.inr i)) := by
    have hvec := congrFun
      (Matrix.mulVec_mulVec
        (Pi.single (headElem (α := x_sub.1.ι)) (1 : ℂ) :
          x_sub.1.ι → ℂ)
        (Qᴴ * x_sub.1.A) Q) ((headTailEquiv (α := x_sub.1.ι)).symm (Sum.inr i))
    rw [hhead_col] at hvec
    simpa [Matrix.mulVec_single, Matrix.mul_assoc] using hvec.symm
  have hcoord :
      (Qᴴ *ᵥ
          (x_sub.1.A *ᵥ (tridiagonalizationFirstVec x_sub.1.c).ofLp))
          ((headTailEquiv (α := x_sub.1.ι)).symm (Sum.inr i)) = 0 := by
    have hinner :
        ⟪b i,
          WithLp.toLp 2
            (x_sub.1.A *ᵥ (tridiagonalizationFirstVec x_sub.1.c).ofLp)⟫_ℂ = 0 := by
      simpa [b] using
        tridiagonalizationStepBasis_inner_A_firstVec_zero_of_tail_rank_pos
          x_sub.1.A x_sub.1.c i hi
    rw [show
        (Qᴴ *ᵥ
            (x_sub.1.A *ᵥ (tridiagonalizationFirstVec x_sub.1.c).ofLp))
            ((headTailEquiv (α := x_sub.1.ι)).symm (Sum.inr i)) =
          ⟪b i,
            WithLp.toLp 2
              (x_sub.1.A *ᵥ (tridiagonalizationFirstVec x_sub.1.c).ofLp)⟫_ℂ by
      simpa [Q] using
        (conjTranspose_matrixOfOrthonormalBasis_mulVec_apply b
        (WithLp.toLp 2
          (x_sub.1.A *ᵥ (tridiagonalizationFirstVec x_sub.1.c).ofLp))
        i)]
    exact hinner
  simpa [TridiagonalizationReady, tridiagonalHeadTailMatrix, Matrix.toBlocks₂₁,
    Matrix.reindex_apply, hQeq] using hentry.trans hcoord

/-- Concrete nonconstructive boundary step oracle for tridiagonalization. -/
noncomputable def tridiagonalizationBoundaryStepOracle :
    TridiagonalizationBoundaryStepOracle.{u} where
  Q := tridiagonalizationConcreteStepQ
  unitary_Q := tridiagonalizationConcreteStepQ_unitary
  ready_matrix := tridiagonalizationConcreteStepQ_ready_matrix
  ready_boundary := tridiagonalizationConcreteStepQ_ready_boundary

end MatDecompFormal.Instances
