import MatDecompFormal.Framework.DecompositionDriver
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.IsDiag

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Normal Matrix Decomposition Details

This file contains the target predicate and small algebraic facts for the
normal-matrix spectral decomposition development. The recursive framework route
is assembled in later files.
-/

variable {ι : Type*}

/-- Matrix-level unitary predicate used by the normal spectral target. -/
def IsUnitaryMatrix [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) : Prop :=
  Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-- Matrix-level normality predicate. -/
def IsNormalMatrix [Fintype ι] (A : Matrix ι ι ℂ) : Prop :=
  Aᴴ * A = A * Aᴴ

/-- Spectral decomposition target for a concrete finite square matrix. -/
def HasNormalSpectral [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Prop :=
  ∃ U D : Matrix ι ι ℂ,
    IsUnitaryMatrix U ∧ D.IsDiag ∧ A = U * D * Uᴴ

/-- Hermitian real part of a complex square matrix. -/
noncomputable def normalHermitianPart [Fintype ι] (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (2 : ℂ)⁻¹ • (A + Aᴴ)

lemma normalHermitianPart_isHermitian [Fintype ι] (A : Matrix ι ι ℂ) :
    (normalHermitianPart A).IsHermitian := by
  rw [Matrix.IsHermitian, normalHermitianPart]
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, add_comm]

/-- Hermitian imaginary part of a complex square matrix. -/
noncomputable def normalImagHermitianPart [Fintype ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (-(Complex.I) * (2 : ℂ)⁻¹) • (A - Aᴴ)

lemma normalImagHermitianPart_isHermitian [Fintype ι] (A : Matrix ι ι ℂ) :
    (normalImagHermitianPart A).IsHermitian := by
  rw [Matrix.IsHermitian, normalImagHermitianPart]
  ext i j
  simp [sub_eq_add_neg, Complex.conj_I]
  ring_nf

lemma normalHermitian_imag_recombine [Fintype ι] (A : Matrix ι ι ℂ) :
    A = normalHermitianPart A + Complex.I • normalImagHermitianPart A := by
  rw [normalHermitianPart, normalImagHermitianPart]
  ext i j
  simp [sub_eq_add_neg, ← mul_assoc, Complex.I_mul_I]
  ring_nf

lemma normalHermitian_imag_raw_commute [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    (A + Aᴴ) * (A - Aᴴ) = (A - Aᴴ) * (A + Aᴴ) := by
  calc
    (A + Aᴴ) * (A - Aᴴ) =
        A * A - A * Aᴴ + (Aᴴ * A - Aᴴ * Aᴴ) := by
      noncomm_ring
    _ = A * A - Aᴴ * Aᴴ := by
      rw [hA]
      noncomm_ring
    _ = A * A - Aᴴ * A + (A * Aᴴ - Aᴴ * Aᴴ) := by
      rw [hA]
      noncomm_ring
    _ = (A - Aᴴ) * (A + Aᴴ) := by
      noncomm_ring

lemma normalHermitian_imag_commute [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    normalHermitianPart A * normalImagHermitianPart A =
      normalImagHermitianPart A * normalHermitianPart A := by
  rw [normalHermitianPart, normalImagHermitianPart]
  calc
    ((2 : ℂ)⁻¹ • (A + Aᴴ)) * ((-Complex.I * (2 : ℂ)⁻¹) • (A - Aᴴ))
        = (((2 : ℂ)⁻¹ * (-Complex.I * (2 : ℂ)⁻¹)) • ((A + Aᴴ) * (A - Aᴴ))) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.smul_apply]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      simp [smul_eq_mul]
      ring_nf
    _ = (((-Complex.I * (2 : ℂ)⁻¹) * (2 : ℂ)⁻¹) • ((A - Aᴴ) * (A + Aᴴ))) := by
      rw [normalHermitian_imag_raw_commute A hA]
      congr 1
      ring
    _ = ((-Complex.I * (2 : ℂ)⁻¹) • (A - Aᴴ)) * ((2 : ℂ)⁻¹ • (A + Aᴴ)) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.smul_apply]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      simp [smul_eq_mul]
      ring_nf

lemma normalHermitianPart_isSymmetric [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (normalHermitianPart A).toEuclideanLin.IsSymmetric :=
  Matrix.isHermitian_iff_isSymmetric.mp (normalHermitianPart_isHermitian A)

lemma normalImagHermitianPart_isSymmetric [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (normalImagHermitianPart A).toEuclideanLin.IsSymmetric :=
  Matrix.isHermitian_iff_isSymmetric.mp (normalImagHermitianPart_isHermitian A)

lemma toEuclideanLin_mul [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℂ) :
    Matrix.toEuclideanLin (M * N) =
      (Matrix.toEuclideanLin M).comp (Matrix.toEuclideanLin N) := by
  ext v i
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

lemma normalHermitian_imag_toEuclideanLin_commute [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    Commute (Matrix.toEuclideanLin (normalHermitianPart A))
      (Matrix.toEuclideanLin (normalImagHermitianPart A)) := by
  rw [Commute, SemiconjBy]
  simp only [Module.End.mul_eq_comp]
  rw [← toEuclideanLin_mul, ← toEuclideanLin_mul, normalHermitian_imag_commute A hA]

lemma normalHermitianPart_joint_eigenspaces_internal [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    DirectSum.IsInternal
      (fun p : ℂ × ℂ =>
        (Module.End.eigenspace (Matrix.toEuclideanLin (normalHermitianPart A)) p.2 ⊓
          Module.End.eigenspace (Matrix.toEuclideanLin (normalImagHermitianPart A)) p.1)) := by
  exact LinearMap.IsSymmetric.directSum_isInternal_of_commute
    (normalHermitianPart_isSymmetric A)
    (normalImagHermitianPart_isSymmetric A)
    (normalHermitian_imag_toEuclideanLin_commute A hA)

/-- Universe-level predicate used by the square-subtype induction framework. -/
def NormalSpectral_P (x : SquareUniverse ℂ) : Prop :=
  IsNormalMatrix x.A → HasNormalSpectral x.A

def NormalSpectral_P_sub (x_sub : PosSquareUniverse ℂ) : Prop :=
  NormalSpectral_P (x_sub : SquareUniverse ℂ)

@[simp] theorem normalSpectral_P_compat (x_sub : PosSquareUniverse ℂ) :
    NormalSpectral_P_sub x_sub ↔ NormalSpectral_P (x_sub : SquareUniverse ℂ) :=
  Iff.rfl

lemma isUnitaryMatrix_one [Fintype ι] [DecidableEq ι] :
    IsUnitaryMatrix (1 : Matrix ι ι ℂ) := by
  simp [IsUnitaryMatrix]

lemma isUnitaryMatrix_mul [Fintype ι] [DecidableEq ι]
    {U V : Matrix ι ι ℂ}
    (hU : IsUnitaryMatrix U) (hV : IsUnitaryMatrix V) :
    IsUnitaryMatrix (U * V) := by
  constructor
  · calc
      (U * V)ᴴ * (U * V) = (Vᴴ * Uᴴ) * (U * V) := by
        rw [Matrix.conjTranspose_mul]
      _ = Vᴴ * (Uᴴ * U) * V := by
        simp [Matrix.mul_assoc]
      _ = 1 := by
        simp [hU.1, hV.1]
  · calc
      (U * V) * (U * V)ᴴ = (U * V) * (Vᴴ * Uᴴ) := by
        rw [Matrix.conjTranspose_mul]
      _ = U * (V * Vᴴ) * Uᴴ := by
        simp [Matrix.mul_assoc]
      _ = 1 := by
        simp [hU.2, hV.2]

lemma isUnitaryMatrix_reindex
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {U : Matrix α α ℂ} (hU : IsUnitaryMatrix U) :
    IsUnitaryMatrix (Matrix.reindex e e U) := by
  constructor
  · have h := congrArg (Matrix.reindex e e) hU.1
    simpa [IsUnitaryMatrix, Matrix.conjTranspose_reindex, Matrix.submatrix_mul_equiv] using h
  · have h := congrArg (Matrix.reindex e e) hU.2
    simpa [IsUnitaryMatrix, Matrix.conjTranspose_reindex, Matrix.submatrix_mul_equiv] using h

lemma isDiag_reindex
    {α β R : Type*} [DecidableEq α] [DecidableEq β] [Zero R]
    (e : α ≃ β) {D : Matrix α α R} (hD : D.IsDiag) :
    (Matrix.reindex e e D).IsDiag := by
  intro i j hij
  apply hD
  intro hEq
  exact hij (e.symm.injective hEq)

theorem normalSpectral_reindex
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {A : Matrix α α ℂ} (hA : HasNormalSpectral A) :
    HasNormalSpectral (Matrix.reindex e e A) := by
  rcases hA with ⟨U, D, hU, hD, hEq⟩
  refine ⟨Matrix.reindex e e U, Matrix.reindex e e D, ?_, ?_, ?_⟩
  · exact isUnitaryMatrix_reindex e hU
  · exact isDiag_reindex e hD
  · have hEq' := congrArg (Matrix.reindex e e) hEq
    simpa [Matrix.conjTranspose_reindex, Matrix.submatrix_mul_equiv, Matrix.mul_assoc] using hEq'

lemma isNormalMatrix_reindex
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) {A : Matrix α α ℂ} (hA : IsNormalMatrix A) :
    IsNormalMatrix (Matrix.reindex e e A) := by
  have h := congrArg (Matrix.reindex e e) hA
  simpa [IsNormalMatrix, Matrix.conjTranspose_reindex, Matrix.submatrix_mul_equiv] using h

lemma isNormalMatrix_unitarySimilarity [Fintype ι] [DecidableEq ι]
    {Q A : Matrix ι ι ℂ}
    (hQ : IsUnitaryMatrix Q) (hA : IsNormalMatrix A) :
    IsNormalMatrix (Qᴴ * A * Q) := by
  calc
    (Qᴴ * A * Q)ᴴ * (Qᴴ * A * Q)
        = Qᴴ * (Aᴴ * A) * Q := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qᴴ (A * Q), hQ.2]
      simp
    _ = Qᴴ * (A * Aᴴ) * Q := by
      rw [hA]
    _ = (Qᴴ * A * Q) * (Qᴴ * A * Q)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qᴴ (Aᴴ * Q), hQ.2]
      simp

lemma isDiag_of_subsingleton [Fintype ι] [Subsingleton ι]
    (A : Matrix ι ι ℂ) :
    A.IsDiag := by
  intro i j hij
  exact False.elim (hij (Subsingleton.elim i j))

/-- Trivial spectral witness for subsingleton square matrices. -/
theorem base_normalSpectral_subsingleton
    [Fintype ι] [DecidableEq ι] [Subsingleton ι]
    (A : Matrix ι ι ℂ) :
    HasNormalSpectral A := by
  refine ⟨1, A, isUnitaryMatrix_one, isDiag_of_subsingleton A, ?_⟩
  simp

/--
Transport a spectral decomposition across a unitary similarity.

This is one of the reusable algebraic facts needed by the framework transport
hook. The unconditional normal spectral theorem will eventually use this with
the unitary matrix produced by the eigenvector/head-basis step.
-/
theorem normalSpectral_transport_unitarySimilarity
    [Fintype ι] [DecidableEq ι]
    (Q A B : Matrix ι ι ℂ)
    (hQ : IsUnitaryMatrix Q)
    (hB : B = Qᴴ * A * Q)
    (hSpec : HasNormalSpectral B) :
    HasNormalSpectral A := by
  rcases hSpec with ⟨U, D, hU, hD, hEq⟩
  refine ⟨Q * U, D, isUnitaryMatrix_mul hQ hU, hD, ?_⟩
  calc
    A = (Q * Qᴴ) * A * (Q * Qᴴ) := by
      simp [hQ.2]
    _ = Q * (Qᴴ * A * Q) * Qᴴ := by
      simp [Matrix.mul_assoc]
    _ = Q * B * Qᴴ := by
      rw [← hB]
    _ = Q * (U * D * Uᴴ) * Qᴴ := by
      rw [hEq]
    _ = (Q * U) * D * (Q * U)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp [Matrix.mul_assoc]


section BlockLift

variable {β : Type*} [Fintype β] [DecidableEq β]

lemma isUnitaryMatrix_blockDiag_one
    {U : Matrix β β ℂ} (hU : IsUnitaryMatrix U) :
    IsUnitaryMatrix
      (fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U :
        Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ) := by
  constructor
  · calc
      (fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U :
          Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ)ᴴ *
          (fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U :
            Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ)
          = fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 (Uᴴ * U) := by
        simp [Matrix.fromBlocks_conjTranspose, fromBlocks_multiply]
      _ = 1 := by
        rw [hU.1]
        exact Matrix.fromBlocks_one
  · calc
      (fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U :
          Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ) *
          (fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U :
            Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ)ᴴ
          = fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 (U * Uᴴ) := by
        simp [Matrix.fromBlocks_conjTranspose, fromBlocks_multiply]
      _ = 1 := by
        rw [hU.2]
        exact Matrix.fromBlocks_one

omit [Fintype β] [DecidableEq β] in
lemma isDiag_blockDiag_unit
    (lam : ℂ) {D : Matrix β β ℂ} (hD : D.IsDiag) :
    (fromBlocks (fun _ _ : Unit => lam) 0 0 D :
      Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ).IsDiag := by
  have hHead : (show Matrix Unit Unit ℂ from fun _ _ => lam).IsDiag :=
    isDiag_of_subsingleton _
  simpa using Matrix.IsDiag.fromBlocks hHead hD

lemma normalSpectral_blockDiag_unit
    (lam : ℂ) {A : Matrix β β ℂ} (hA : HasNormalSpectral A) :
    HasNormalSpectral
      (fromBlocks (fun _ _ : Unit => lam) 0 0 A :
        Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ) := by
  rcases hA with ⟨U, D, hU, hD, hEq⟩
  let Ublk : Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ :=
    fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U
  let Dblk : Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ :=
    fromBlocks (fun _ _ : Unit => lam) 0 0 D
  refine ⟨Ublk, Dblk, ?_, ?_, ?_⟩
  · exact isUnitaryMatrix_blockDiag_one hU
  · exact isDiag_blockDiag_unit lam hD
  · calc
      (fromBlocks (fun _ _ : Unit => lam) 0 0 A :
          Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ)
          = fromBlocks (fun _ _ : Unit => lam) 0 0 (U * D * Uᴴ) := by
        rw [hEq]
      _ = Ublk * Dblk * Ublkᴴ := by
        simp [Ublk, Dblk, Matrix.fromBlocks_conjTranspose, fromBlocks_multiply,
          Matrix.mul_assoc]

lemma normalSpectral_fromBlocks_zero_offdiag
    (A₁₁ : Matrix Unit Unit ℂ) {A₂₂ : Matrix β β ℂ}
    (hA₂₂ : HasNormalSpectral A₂₂) :
    HasNormalSpectral
      (fromBlocks A₁₁ 0 0 A₂₂ :
        Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ) := by
  have hA₁₁ : A₁₁ = fun _ _ : Unit => A₁₁ () () := by
    ext i j
    simp
  rw [hA₁₁]
  exact normalSpectral_blockDiag_unit (A₁₁ () ()) hA₂₂

lemma normalSpectral_of_blockReady_reindex
    (A : Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ)
    (h₁₂ : A.toBlocks₁₂ = 0) (h₂₁ : A.toBlocks₂₁ = 0)
    (hTail : HasNormalSpectral A.toBlocks₂₂) :
    HasNormalSpectral A := by
  have hA :
      A =
        fromBlocks A.toBlocks₁₁ 0 0 A.toBlocks₂₂ := by
    exact (Matrix.ext_iff_blocks).2 ⟨rfl, h₁₂, h₂₁, rfl⟩
  rw [hA]
  exact normalSpectral_fromBlocks_zero_offdiag A.toBlocks₁₁ hTail

omit [DecidableEq β] in
lemma isNormalMatrix_tail_of_zero_offdiag
    (A : Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ)
    (hNormal : IsNormalMatrix A)
    (h₁₂ : A.toBlocks₁₂ = 0) (h₂₁ : A.toBlocks₂₁ = 0) :
    IsNormalMatrix A.toBlocks₂₂ := by
  have hA :
      A =
        fromBlocks A.toBlocks₁₁ 0 0 A.toBlocks₂₂ := by
    exact (Matrix.ext_iff_blocks).2 ⟨rfl, h₁₂, h₂₁, rfl⟩
  rw [hA] at hNormal
  have h := congrArg Matrix.toBlocks₂₂ hNormal
  simpa [IsNormalMatrix, Matrix.fromBlocks_conjTranspose, fromBlocks_multiply] using h

end BlockLift

end MatDecompFormal.Instances
