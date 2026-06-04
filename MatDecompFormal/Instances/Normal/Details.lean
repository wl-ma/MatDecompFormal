import MatDecompFormal.Framework.DecompositionDriver
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
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

lemma isDiag_blockDiag_unit
    (λ : ℂ) {D : Matrix β β ℂ} (hD : D.IsDiag) :
    (fromBlocks (fun _ _ : Unit => λ) 0 0 D :
      Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ).IsDiag := by
  have hHead : (fun _ _ : Unit => λ : Matrix Unit Unit ℂ).IsDiag :=
    isDiag_of_subsingleton _
  simpa using Matrix.IsDiag.fromBlocks hHead hD

lemma normalSpectral_blockDiag_unit
    (λ : ℂ) {A : Matrix β β ℂ} (hA : HasNormalSpectral A) :
    HasNormalSpectral
      (fromBlocks (fun _ _ : Unit => λ) 0 0 A :
        Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ) := by
  rcases hA with ⟨U, D, hU, hD, hEq⟩
  let Ublk : Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ :=
    fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U
  let Dblk : Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ :=
    fromBlocks (fun _ _ : Unit => λ) 0 0 D
  refine ⟨Ublk, Dblk, ?_, ?_, ?_⟩
  · exact isUnitaryMatrix_blockDiag_one hU
  · exact isDiag_blockDiag_unit λ hD
  · calc
      (fromBlocks (fun _ _ : Unit => λ) 0 0 A :
          Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ)
          = fromBlocks (fun _ _ : Unit => λ) 0 0 (U * D * Uᴴ) := by
        rw [hEq]
      _ = Ublk * Dblk * Ublkᴴ := by
        simp [Ublk, Dblk, Matrix.fromBlocks_conjTranspose, fromBlocks_multiply,
          Matrix.mul_assoc]

end BlockLift

end MatDecompFormal.Instances
