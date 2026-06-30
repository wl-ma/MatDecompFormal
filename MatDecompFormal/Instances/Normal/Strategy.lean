/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Normal.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Framework

/-!
# Normal Matrix Strategy Core

This file implements the strategy-side skeleton for normal spectral
decomposition. The hard spectral step is isolated in `NormalSimilarityOracle`:
given a matrix, it supplies a unitary similarity that puts the matrix into a
head-tail block-ready form.

The oracle is not an unsupported placeholder. It is an explicit parameter to the conditional
framework theorem, and the remaining project work is to construct it from the
complex spectral/eigenvector lemmas.
-/

/-- Tail index obtained by removing the distinguished head element. -/
abbrev NormalTailIdx (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { a : ι // a ≠ headElem (α := ι) }

/--
The block-ready state for the normal-matrix descent step: after reindexing by
the head-tail equivalence, both off-diagonal blocks vanish.
-/
def NormalBlockReady
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) : Prop :=
  let A' := Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A
  A'.toBlocks₁₂ = 0 ∧ A'.toBlocks₂₁ = 0

lemma normalBlockReady_of_isDiag
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} (hDiag : A.IsDiag) :
    NormalBlockReady ι A := by
  let e := headTailEquiv (α := ι)
  have hDiag' : (Matrix.reindex e e A).IsDiag :=
    isDiag_reindex e hDiag
  dsimp [NormalBlockReady]
  constructor
  · ext i j
    exact hDiag' (by simp)
  · ext i j
    exact hDiag' (by simp)

/--
The slicability predicate used by the framework.

The universe-level target is an implication `IsNormalMatrix A → HasNormalSpectral A`,
so the recursive driver must also be able to make progress on non-normal matrices.
Those branches are harmless: the lift hook later receives a normality assumption
and closes the non-normal case by contradiction.
-/
def NormalDescentReady
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) : Prop :=
  ¬ IsNormalMatrix A ∨ NormalBlockReady ι A

noncomputable instance normalBlockReadyDecidable
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    DecidablePred (fun A : Matrix ι ι ℂ => NormalDescentReady ι A) := by
  classical
  intro A
  exact inferInstance

/--
The high-level spectral step required by the strategy: every matrix can be
unitarily transformed into a block-ready matrix.

This is the main mathematical hook left by the first implementation pass.
-/
structure NormalSimilarityOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  Q : Matrix ι ι ℂ → Matrix ι ι ℂ
  unitary_Q : ∀ A, IsUnitaryMatrix (Q A)
  descentReady : ∀ A, NormalDescentReady ι ((Q A)ᴴ * A * (Q A))

/--
Mathematical oracle still needed for the normal case: given a normal matrix,
produce a unitary similarity putting it in head-tail block-ready form.

This isolates the real spectral/eigenvector work from the framework bookkeeping.
-/
structure NormalBlockReadyOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  Q : (A : Matrix ι ι ℂ) → IsNormalMatrix A → Matrix ι ι ℂ
  unitary_Q : ∀ A hA, IsUnitaryMatrix (Q A hA)
  blockReady : ∀ A hA, NormalBlockReady ι ((Q A hA)ᴴ * A * (Q A hA))

/--
Standard spectral-theorem-shaped oracle: for every normal matrix, provide a
unitary diagonalizing basis.

This is stronger than `NormalBlockReadyOracle`, but it matches the usual
normal-matrix spectral theorem statement and can be converted into the descent
oracle below.
-/
structure NormalDiagonalizationOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  Q : (A : Matrix ι ι ℂ) → IsNormalMatrix A → Matrix ι ι ℂ
  unitary_Q : ∀ A hA, IsUnitaryMatrix (Q A hA)
  diagonalizes : ∀ A hA, ((Q A hA)ᴴ * A * (Q A hA)).IsDiag

/--
Joint-Hermitian-pair oracle: split each normal matrix into two parts, provide a
unitary that diagonalizes both, and prove they recombine to the original matrix.
This is tailored to mathlib's commuting self-adjoint joint eigenspace results.
-/
structure NormalHermitianPairDiagonalizationOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  Hpart : Matrix ι ι ℂ → Matrix ι ι ℂ
  Ipart : Matrix ι ι ℂ → Matrix ι ι ℂ
  Q : (A : Matrix ι ι ℂ) → IsNormalMatrix A → Matrix ι ι ℂ
  unitary_Q : ∀ A hA, IsUnitaryMatrix (Q A hA)
  recombine : ∀ A (_hA : IsNormalMatrix A), A = Hpart A + Complex.I • Ipart A
  diag_H : ∀ A (hA : IsNormalMatrix A), ((Q A hA)ᴴ * Hpart A * (Q A hA)).IsDiag
  diag_I : ∀ A (hA : IsNormalMatrix A), ((Q A hA)ᴴ * Ipart A * (Q A hA)).IsDiag

/--
Concrete remaining diagonalization oracle for the canonical Hermitian
real/imaginary split of a normal matrix.
-/
structure NormalHermitianPartSimultaneousDiagonalizationOracle
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  Q : (A : Matrix ι ι ℂ) → IsNormalMatrix A → Matrix ι ι ℂ
  unitary_Q : ∀ A hA, IsUnitaryMatrix (Q A hA)
  diag_H : ∀ A (hA : IsNormalMatrix A),
    ((Q A hA)ᴴ * normalHermitianPart A * (Q A hA)).IsDiag
  diag_I : ∀ A (hA : IsNormalMatrix A),
    ((Q A hA)ᴴ * normalImagHermitianPart A * (Q A hA)).IsDiag

/-- Matrix whose columns are an orthonormal basis of `EuclideanSpace ℂ ι`. -/
noncomputable def matrixOfOrthonormalBasis
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) :
    Matrix ι ι ℂ :=
  (EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b.toBasis

lemma matrixOfOrthonormalBasis_unitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) :
    IsUnitaryMatrix (matrixOfOrthonormalBasis b) := by
  constructor
  · exact (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_conjTranspose_mul_self b
  · exact (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_self_mul_conjTranspose b

@[simp] lemma matrixOfOrthonormalBasis_col
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (j : ι) :
    Matrix.col (matrixOfOrthonormalBasis b) j = ⇑(b j) := rfl

lemma matrixOfOrthonormalBasis_mulVec_single
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (j : ι) :
    (matrixOfOrthonormalBasis b) *ᵥ (Pi.single j (1 : ℂ) : ι → ℂ) = ⇑(b j) := by
  simp_rw [mulVec_single_one, matrixOfOrthonormalBasis_col]

lemma matrix_one_mulVec_single
    {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) :
    (1 : Matrix ι ι ℂ) *ᵥ (Pi.single j (1 : ℂ) : ι → ℂ) =
      (Pi.single j (1 : ℂ) : ι → ℂ) := by
  rw [one_mulVec]

lemma conjTranspose_matrixOfOrthonormalBasis_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (j : ι) :
    (matrixOfOrthonormalBasis b)ᴴ *ᵥ ⇑(b j) =
      (Pi.single j (1 : ℂ) : ι → ℂ) := by
  calc
    (matrixOfOrthonormalBasis b)ᴴ *ᵥ ⇑(b j)
        = (matrixOfOrthonormalBasis b)ᴴ *ᵥ
            ((matrixOfOrthonormalBasis b) *ᵥ (Pi.single j (1 : ℂ) : ι → ℂ)) := by
      rw [matrixOfOrthonormalBasis_mulVec_single]
    _ = ((matrixOfOrthonormalBasis b)ᴴ * (matrixOfOrthonormalBasis b)) *ᵥ
          (Pi.single j (1 : ℂ) : ι → ℂ) := by
      rw [Matrix.mulVec_mulVec]
    _ = (Pi.single j (1 : ℂ) : ι → ℂ) := by
      rw [(matrixOfOrthonormalBasis_unitary b).1, matrix_one_mulVec_single]

lemma conjugated_mulVec_single_of_eigenbasis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (lam : ι → ℂ)
    (heig : ∀ j, M *ᵥ ⇑(b j) = (lam j : ℂ) • ⇑(b j)) (j : ι) :
    ((matrixOfOrthonormalBasis b)ᴴ * M * (matrixOfOrthonormalBasis b)) *ᵥ
        (Pi.single j (1 : ℂ) : ι → ℂ) =
      (lam j : ℂ) • (Pi.single j (1 : ℂ) : ι → ℂ) := by
  calc
    ((matrixOfOrthonormalBasis b)ᴴ * M * (matrixOfOrthonormalBasis b)) *ᵥ
        (Pi.single j (1 : ℂ) : ι → ℂ)
        = ((matrixOfOrthonormalBasis b)ᴴ * M) *ᵥ
            ((matrixOfOrthonormalBasis b) *ᵥ (Pi.single j (1 : ℂ) : ι → ℂ)) := by
      exact
        (Matrix.mulVec_mulVec
          (Pi.single j (1 : ℂ) : ι → ℂ)
          ((matrixOfOrthonormalBasis b)ᴴ * M)
          (matrixOfOrthonormalBasis b)).symm
    _ = (matrixOfOrthonormalBasis b)ᴴ *ᵥ
          (M *ᵥ ((matrixOfOrthonormalBasis b) *ᵥ (Pi.single j (1 : ℂ) : ι → ℂ))) := by
      exact
        (Matrix.mulVec_mulVec
          ((matrixOfOrthonormalBasis b) *ᵥ (Pi.single j (1 : ℂ) : ι → ℂ))
          (matrixOfOrthonormalBasis b)ᴴ M).symm
    _ = (matrixOfOrthonormalBasis b)ᴴ *ᵥ (M *ᵥ ⇑(b j)) := by
      rw [matrixOfOrthonormalBasis_mulVec_single]
    _ = (matrixOfOrthonormalBasis b)ᴴ *ᵥ ((lam j : ℂ) • ⇑(b j)) := by
      rw [heig j]
    _ = (lam j : ℂ) • ((matrixOfOrthonormalBasis b)ᴴ *ᵥ ⇑(b j)) := by
      rw [mulVec_smul]
    _ = (lam j : ℂ) • (Pi.single j (1 : ℂ) : ι → ℂ) := by
      rw [conjTranspose_matrixOfOrthonormalBasis_mulVec]

lemma isDiag_conjugated_of_eigenbasis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (lam : ι → ℂ)
    (heig : ∀ j, M *ᵥ ⇑(b j) = (lam j : ℂ) • ⇑(b j)) :
    ((matrixOfOrthonormalBasis b)ᴴ * M * (matrixOfOrthonormalBasis b)).IsDiag := by
  intro i j hij
  have hvec := conjugated_mulVec_single_of_eigenbasis M b lam heig j
  have hentry := congrFun hvec i
  simpa [Matrix.mulVec_single, Pi.single_apply, hij] using hentry

/--
Data form of the remaining simultaneous-eigenbasis theorem for the canonical
Hermitian parts.
-/
structure NormalHermitianPartJointEigenbasis
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  basis : (A : Matrix ι ι ℂ) → IsNormalMatrix A → OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)
  H_eigenvalue : (A : Matrix ι ι ℂ) → IsNormalMatrix A → ι → ℂ
  I_eigenvalue : (A : Matrix ι ι ℂ) → IsNormalMatrix A → ι → ℂ
  H_eigen :
    ∀ A (hA : IsNormalMatrix A) j,
      normalHermitianPart A *ᵥ ⇑(basis A hA j) =
        H_eigenvalue A hA j • ⇑(basis A hA j)
  I_eigen :
    ∀ A (hA : IsNormalMatrix A) j,
      normalImagHermitianPart A *ᵥ ⇑(basis A hA j) =
        I_eigenvalue A hA j • ⇑(basis A hA j)

structure NormalHermitianPartJointEigenbasisSubordinate
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  basis : (A : Matrix ι ι ℂ) → IsNormalMatrix A → OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)
  eigenPair : (A : Matrix ι ι ℂ) → IsNormalMatrix A → ι → ℂ × ℂ
  mem_joint :
    ∀ A (hA : IsNormalMatrix A) j,
      basis A hA j ∈
        (Module.End.eigenspace (Matrix.toEuclideanLin (normalHermitianPart A))
            (eigenPair A hA j).2 ⊓
          Module.End.eigenspace (Matrix.toEuclideanLin (normalImagHermitianPart A))
            (eigenPair A hA j).1)

abbrev NormalCardFin (ι : Type*) [Fintype ι] := Fin (Fintype.card ι)

structure NormalHermitianPartJointEigenbasisSubordinateFin
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  basis :
    (A : Matrix ι ι ℂ) → IsNormalMatrix A →
      OrthonormalBasis (NormalCardFin ι) ℂ (EuclideanSpace ℂ ι)
  eigenPair : (A : Matrix ι ι ℂ) → IsNormalMatrix A → NormalCardFin ι → ℂ × ℂ
  mem_joint :
    ∀ A (hA : IsNormalMatrix A) j,
      basis A hA j ∈
        (Module.End.eigenspace (Matrix.toEuclideanLin (normalHermitianPart A))
            (eigenPair A hA j).2 ⊓
          Module.End.eigenspace (Matrix.toEuclideanLin (normalImagHermitianPart A))
            (eigenPair A hA j).1)

noncomputable def normalHermitianPartSubordinateOfFin
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (subFin : NormalHermitianPartJointEigenbasisSubordinateFin ι) :
    NormalHermitianPartJointEigenbasisSubordinate ι where
  basis := fun A hA =>
    (subFin.basis A hA).reindex (Fintype.equivOfCardEq (Fintype.card_fin _))
  eigenPair := fun A hA i =>
    subFin.eigenPair A hA ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
  mem_joint := by
    intro A hA i
    rw [OrthonormalBasis.reindex_apply]
    exact subFin.mem_joint A hA ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)

structure NormalHermitianPartFiniteJointSubordinate
    (ι γ : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Fintype γ] [DecidableEq γ] where
  eigenPair : (A : Matrix ι ι ℂ) → IsNormalMatrix A → γ → ℂ × ℂ
  space : (A : Matrix ι ι ℂ) → IsNormalMatrix A → γ → Submodule ℂ (EuclideanSpace ℂ ι)
  space_eq :
    ∀ A hA g,
      space A hA g =
        (Module.End.eigenspace (Matrix.toEuclideanLin (normalHermitianPart A))
            (eigenPair A hA g).2 ⊓
          Module.End.eigenspace (Matrix.toEuclideanLin (normalImagHermitianPart A))
            (eigenPair A hA g).1)
  basis :
    (A : Matrix ι ι ℂ) → IsNormalMatrix A →
      OrthonormalBasis (NormalCardFin ι) ℂ (EuclideanSpace ℂ ι)
  basisIndex : (A : Matrix ι ι ℂ) → IsNormalMatrix A → NormalCardFin ι → γ
  basis_mem : ∀ A (hA : IsNormalMatrix A) i, basis A hA i ∈ space A hA (basisIndex A hA i)

noncomputable def normalHermitianPartSubordinateFinOfFiniteJoint
    (ι γ : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Fintype γ] [DecidableEq γ]
    (finite : NormalHermitianPartFiniteJointSubordinate ι γ) :
    NormalHermitianPartJointEigenbasisSubordinateFin ι where
  basis := finite.basis
  eigenPair := fun A hA i => finite.eigenPair A hA (finite.basisIndex A hA i)
  mem_joint := by
    intro A hA i
    have hmem := finite.basis_mem A hA i
    rw [finite.space_eq A hA (finite.basisIndex A hA i)] at hmem
    exact hmem

structure NormalHermitianPartJointEigenbasisSubordinateSigma
    (ι γ : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Fintype γ] [DecidableEq γ] where
  idx : γ → Type*
  fintype_sigma : Fintype (Σ g : γ, idx g)
  basis :
    (A : Matrix ι ι ℂ) → IsNormalMatrix A →
      @OrthonormalBasis (Σ g : γ, idx g) ℂ _ (EuclideanSpace ℂ ι) _ _ fintype_sigma
  eigenPair : (A : Matrix ι ι ℂ) → IsNormalMatrix A → γ → ℂ × ℂ
  reindexEquiv :
    (A : Matrix ι ι ℂ) → IsNormalMatrix A → (Σ g : γ, idx g) ≃ NormalCardFin ι
  mem_joint :
    ∀ A (hA : IsNormalMatrix A) (a : Σ g : γ, idx g),
      basis A hA a ∈
        (Module.End.eigenspace (Matrix.toEuclideanLin (normalHermitianPart A))
            (eigenPair A hA a.1).2 ⊓
          Module.End.eigenspace (Matrix.toEuclideanLin (normalImagHermitianPart A))
            (eigenPair A hA a.1).1)

structure NormalHermitianPartJointEigenbasisSubordinateGeneralSigma
    (ι γ : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  idx : γ → Type*
  fintype_sigma : Fintype (Σ g : γ, idx g)
  decEq_sigma : DecidableEq (Σ g : γ, idx g)
  basis :
    (A : Matrix ι ι ℂ) → IsNormalMatrix A →
      @OrthonormalBasis (Σ g : γ, idx g) ℂ _ (EuclideanSpace ℂ ι) _ _ fintype_sigma
  eigenPair : (A : Matrix ι ι ℂ) → IsNormalMatrix A → γ → ℂ × ℂ
  reindexEquiv :
    (A : Matrix ι ι ℂ) → IsNormalMatrix A → (Σ g : γ, idx g) ≃ NormalCardFin ι
  mem_joint :
    ∀ A (hA : IsNormalMatrix A) (a : Σ g : γ, idx g),
      basis A hA a ∈
        (Module.End.eigenspace (Matrix.toEuclideanLin (normalHermitianPart A))
            (eigenPair A hA a.1).2 ⊓
          Module.End.eigenspace (Matrix.toEuclideanLin (normalImagHermitianPart A))
            (eigenPair A hA a.1).1)

structure NormalHermitianPartJointEigenbasisSubordinateDependentSigma
    (ι γ : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  idx : (A : Matrix ι ι ℂ) → IsNormalMatrix A → γ → Type*
  fintype_sigma : ∀ A hA, Fintype (Σ g : γ, idx A hA g)
  basis :
    (A : Matrix ι ι ℂ) → (hA : IsNormalMatrix A) →
      @OrthonormalBasis (Σ g : γ, idx A hA g) ℂ _ (EuclideanSpace ℂ ι) _ _
        (fintype_sigma A hA)
  eigenPair : (A : Matrix ι ι ℂ) → IsNormalMatrix A → γ → ℂ × ℂ
  reindexEquiv :
    (A : Matrix ι ι ℂ) → (hA : IsNormalMatrix A) →
      (Σ g : γ, idx A hA g) ≃ NormalCardFin ι
  mem_joint :
    ∀ A (hA : IsNormalMatrix A) (a : Σ g : γ, idx A hA g),
      basis A hA a ∈
        (Module.End.eigenspace (Matrix.toEuclideanLin (normalHermitianPart A))
            (eigenPair A hA a.1).2 ⊓
          Module.End.eigenspace (Matrix.toEuclideanLin (normalImagHermitianPart A))
            (eigenPair A hA a.1).1)

structure NormalHermitianPartJointEigenbasisSubordinateMatrixSigma
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  label : (A : Matrix ι ι ℂ) → IsNormalMatrix A → Type*
  label_fintype : ∀ A hA, Fintype (label A hA)
  idx : (A : Matrix ι ι ℂ) → (hA : IsNormalMatrix A) → label A hA → Type*
  fintype_sigma : ∀ A hA, Fintype (Σ g : label A hA, idx A hA g)
  basis :
    (A : Matrix ι ι ℂ) → (hA : IsNormalMatrix A) →
      @OrthonormalBasis (Σ g : label A hA, idx A hA g) ℂ _ (EuclideanSpace ℂ ι) _ _
        (fintype_sigma A hA)
  eigenPair :
    (A : Matrix ι ι ℂ) → (hA : IsNormalMatrix A) → label A hA → ℂ × ℂ
  reindexEquiv :
    (A : Matrix ι ι ℂ) → (hA : IsNormalMatrix A) →
      (Σ g : label A hA, idx A hA g) ≃ NormalCardFin ι
  mem_joint :
    ∀ A (hA : IsNormalMatrix A) (a : Σ g : label A hA, idx A hA g),
      basis A hA a ∈
        (Module.End.eigenspace (Matrix.toEuclideanLin (normalHermitianPart A))
            (eigenPair A hA a.1).2 ⊓
          Module.End.eigenspace (Matrix.toEuclideanLin (normalImagHermitianPart A))
            (eigenPair A hA a.1).1)

noncomputable def normalHermitianPartSubordinateFinOfSigma
    (ι γ : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Fintype γ] [DecidableEq γ]
    (subSigma : NormalHermitianPartJointEigenbasisSubordinateSigma ι γ) :
    NormalHermitianPartJointEigenbasisSubordinateFin ι := by
  letI := subSigma.fintype_sigma
  refine
    { basis := fun A hA =>
        (subSigma.basis A hA).reindex (subSigma.reindexEquiv A hA)
      eigenPair := fun A hA i =>
        subSigma.eigenPair A hA ((subSigma.reindexEquiv A hA).symm i).1
      mem_joint := ?_ }
  intro A hA i
  rw [OrthonormalBasis.reindex_apply]
  exact subSigma.mem_joint A hA ((subSigma.reindexEquiv A hA).symm i)

noncomputable def normalHermitianPartSubordinateFinOfGeneralSigma
    (ι γ : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (subSigma : NormalHermitianPartJointEigenbasisSubordinateGeneralSigma ι γ) :
    NormalHermitianPartJointEigenbasisSubordinateFin ι := by
  letI := subSigma.fintype_sigma
  refine
    { basis := fun A hA =>
        (subSigma.basis A hA).reindex (subSigma.reindexEquiv A hA)
      eigenPair := fun A hA i =>
        subSigma.eigenPair A hA ((subSigma.reindexEquiv A hA).symm i).1
      mem_joint := ?_ }
  intro A hA i
  rw [OrthonormalBasis.reindex_apply]
  exact subSigma.mem_joint A hA ((subSigma.reindexEquiv A hA).symm i)

noncomputable def normalHermitianPartSubordinateFinOfDependentSigma
    (ι γ : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (subSigma : NormalHermitianPartJointEigenbasisSubordinateDependentSigma ι γ) :
    NormalHermitianPartJointEigenbasisSubordinateFin ι := by
  refine
    { basis := fun A hA =>
        letI := subSigma.fintype_sigma A hA
        (subSigma.basis A hA).reindex (subSigma.reindexEquiv A hA)
      eigenPair := fun A hA i =>
        subSigma.eigenPair A hA ((subSigma.reindexEquiv A hA).symm i).1
      mem_joint := ?_ }
  intro A hA i
  letI := subSigma.fintype_sigma A hA
  rw [OrthonormalBasis.reindex_apply]
  exact subSigma.mem_joint A hA ((subSigma.reindexEquiv A hA).symm i)

noncomputable def normalHermitianPartSubordinateFinOfMatrixSigma
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (subSigma : NormalHermitianPartJointEigenbasisSubordinateMatrixSigma ι) :
    NormalHermitianPartJointEigenbasisSubordinateFin ι := by
  refine
    { basis := fun A hA =>
        letI := subSigma.fintype_sigma A hA
        (subSigma.basis A hA).reindex (subSigma.reindexEquiv A hA)
      eigenPair := fun A hA i =>
        subSigma.eigenPair A hA ((subSigma.reindexEquiv A hA).symm i).1
      mem_joint := ?_ }
  intro A hA i
  letI := subSigma.fintype_sigma A hA
  rw [OrthonormalBasis.reindex_apply]
  exact subSigma.mem_joint A hA ((subSigma.reindexEquiv A hA).symm i)

noncomputable abbrev normalHOp
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Module.End ℂ (EuclideanSpace ℂ ι) :=
  Matrix.toEuclideanLin (normalHermitianPart A)

noncomputable abbrev normalIOp
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Module.End ℂ (EuclideanSpace ℂ ι) :=
  Matrix.toEuclideanLin (normalImagHermitianPart A)

noncomputable abbrev normalHermitianPartEigenLabel
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :=
  Prod (normalHOp A).Eigenvalues (normalIOp A).Eigenvalues

noncomputable abbrev normalHermitianPartEigenPair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (p : normalHermitianPartEigenLabel A) : ℂ × ℂ :=
  ((p.2 : ℂ), (p.1 : ℂ))

noncomputable abbrev normalHermitianPartEigenJointSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (p : normalHermitianPartEigenLabel A) :
    Submodule ℂ (EuclideanSpace ℂ ι) :=
  Module.End.eigenspace (normalHOp A) (p.1 : ℂ) ⊓
    Module.End.eigenspace (normalIOp A) (p.2 : ℂ)

lemma normalHermitianPartEigenPair_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    Function.Injective (fun p : normalHermitianPartEigenLabel A =>
      normalHermitianPartEigenPair A p) := by
  intro p q h
  rcases p with ⟨pH, pI⟩
  rcases q with ⟨qH, qI⟩
  have hI : pI = qI := Subtype.ext (Prod.ext_iff.mp h).1
  have hH : pH = qH := Subtype.ext (Prod.ext_iff.mp h).2
  simp [hH, hI]

lemma normalHermitianPartEigenJointSpace_orthogonalFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    OrthogonalFamily ℂ
      (fun p : normalHermitianPartEigenLabel A =>
        ↥(normalHermitianPartEigenJointSpace A p))
      (fun p => (normalHermitianPartEigenJointSpace A p).subtypeₗᵢ) := by
  simpa [normalHermitianPartEigenJointSpace, normalHermitianPartEigenPair,
    normalHOp, normalIOp] using
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace
      (normalHermitianPart_isSymmetric A) (normalImagHermitianPart_isSymmetric A)).comp
      (normalHermitianPartEigenPair_injective A)

lemma iSup_inf_right_normalIOp_eigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (V : Submodule ℂ (EuclideanSpace ℂ ι)) :
    (⨆ γ : (normalIOp A).Eigenvalues,
        V ⊓ Module.End.eigenspace (normalIOp A) (γ : ℂ)) =
      (⨆ γ : ℂ, V ⊓ Module.End.eigenspace (normalIOp A) γ) := by
  apply le_antisymm
  · refine iSup_le ?_
    intro γ
    exact le_iSup_of_le (γ : ℂ) le_rfl
  · refine iSup_le ?_
    intro γ
    by_cases hγ : Module.End.eigenspace (normalIOp A) γ = ⊥
    · simp [hγ]
    · exact le_iSup_of_le (⟨γ, hγ⟩ : (normalIOp A).Eigenvalues) le_rfl

lemma normalHermitianPartEigenJointSpace_iSup
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (⨆ p : normalHermitianPartEigenLabel A,
        normalHermitianPartEigenJointSpace A p) =
      (⨆ α : ℂ, ⨆ γ : ℂ,
        Module.End.eigenspace (normalHOp A) α ⊓
          Module.End.eigenspace (normalIOp A) γ) := by
  rw [iSup_prod]
  calc
    (⨆ α : (normalHOp A).Eigenvalues,
        ⨆ γ : (normalIOp A).Eigenvalues,
          Module.End.eigenspace (normalHOp A) (α : ℂ) ⊓
            Module.End.eigenspace (normalIOp A) (γ : ℂ))
        =
      (⨆ α : (normalHOp A).Eigenvalues,
        ⨆ γ : ℂ,
          Module.End.eigenspace (normalHOp A) (α : ℂ) ⊓
            Module.End.eigenspace (normalIOp A) γ) := by
      simp_rw [iSup_inf_right_normalIOp_eigenvalues A]
    _ =
      (⨆ α : ℂ, ⨆ γ : ℂ,
        Module.End.eigenspace (normalHOp A) α ⊓
          Module.End.eigenspace (normalIOp A) γ) := by
      apply le_antisymm
      · refine iSup_le ?_
        intro α
        exact le_iSup_of_le (α : ℂ) le_rfl
      · refine iSup_le ?_
        intro α
        by_cases hα : Module.End.eigenspace (normalHOp A) α = ⊥
        · simp [hα]
        · exact le_iSup_of_le (⟨α, hα⟩ : (normalHOp A).Eigenvalues) le_rfl

lemma normalHermitianPartEigenJointSpace_iSup_top
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    (⨆ p : normalHermitianPartEigenLabel A,
        normalHermitianPartEigenJointSpace A p) = ⊤ := by
  rw [normalHermitianPartEigenJointSpace_iSup A]
  exact LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
    (normalHermitianPart_isSymmetric A) (normalImagHermitianPart_isSymmetric A)
    (normalHermitian_imag_toEuclideanLin_commute A hA)

lemma normalHermitianPartEigenJointSpace_internal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    DirectSum.IsInternal (fun p : normalHermitianPartEigenLabel A =>
      normalHermitianPartEigenJointSpace A p) := by
  classical
  refine (OrthogonalFamily.isInternal_iff ?orth).mpr ?_
  · exact normalHermitianPartEigenJointSpace_orthogonalFamily A
  · rw [Submodule.orthogonal_eq_bot_iff]
    exact normalHermitianPartEigenJointSpace_iSup_top A hA

noncomputable def normalHermitianPartEigenCollectedBasis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    OrthonormalBasis
      (Σ p : normalHermitianPartEigenLabel A,
        Fin (Module.finrank ℂ (normalHermitianPartEigenJointSpace A p))) ℂ
      (EuclideanSpace ℂ ι) := by
  classical
  refine
    (normalHermitianPartEigenJointSpace_internal A hA).collectedOrthonormalBasis
      ?orth ?basis
  · exact normalHermitianPartEigenJointSpace_orthogonalFamily A
  · exact fun p => stdOrthonormalBasis ℂ (normalHermitianPartEigenJointSpace A p)

noncomputable def normalHermitianPartEigenCollectedEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    (Σ p : normalHermitianPartEigenLabel A,
      Fin (Module.finrank ℂ (normalHermitianPartEigenJointSpace A p))) ≃
      NormalCardFin ι := by
  classical
  let b := normalHermitianPartEigenCollectedBasis A hA
  exact Fintype.equivFinOfCardEq <| by
    rw [← Module.finrank_eq_card_basis b.toBasis]
    exact finrank_euclideanSpace

lemma normalHermitianPartEigenCollectedBasis_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A)
    (a : Σ p : normalHermitianPartEigenLabel A,
      Fin (Module.finrank ℂ (normalHermitianPartEigenJointSpace A p))) :
    normalHermitianPartEigenCollectedBasis A hA a ∈
      (Module.End.eigenspace (normalHOp A)
          (normalHermitianPartEigenPair A a.1).2 ⊓
        Module.End.eigenspace (normalIOp A)
          (normalHermitianPartEigenPair A a.1).1) := by
  exact
    (normalHermitianPartEigenJointSpace_internal A hA).collectedOrthonormalBasis_mem
      (normalHermitianPartEigenJointSpace_orthogonalFamily A)
      (fun p => stdOrthonormalBasis ℂ (normalHermitianPartEigenJointSpace A p)) a

set_option maxHeartbeats 800000 in
-- The structure fields contain dependent sigma indices, so elaboration needs a
-- larger heartbeat budget for the final field unification.
/-- Construct the finite joint-eigenbasis data from the canonical Hermitian parts. -/
noncomputable def normalHermitianPartMatrixSigma
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    NormalHermitianPartJointEigenbasisSubordinateMatrixSigma ι where
  label := fun A _hA => normalHermitianPartEigenLabel A
  label_fintype := by
    intro A hA
    classical
    infer_instance
  idx := fun A _hA p =>
    Fin (Module.finrank ℂ (normalHermitianPartEigenJointSpace A p))
  fintype_sigma := by
    intro A hA
    classical
    infer_instance
  basis := fun A hA => normalHermitianPartEigenCollectedBasis A hA
  eigenPair := fun A _hA p => normalHermitianPartEigenPair A p
  reindexEquiv := fun A hA => normalHermitianPartEigenCollectedEquiv A hA
  mem_joint := by
    intro A hA a
    exact normalHermitianPartEigenCollectedBasis_mem A hA a

lemma mulVec_of_toEuclideanLin_eigen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (lam : ℂ)
    (h : Matrix.toEuclideanLin M v = lam • v) :
    M *ᵥ ⇑v = lam • ⇑v := by
  have h' := congrArg (fun x : EuclideanSpace ℂ ι => (x : ι → ℂ)) h
  simpa [Matrix.toEuclideanLin_apply] using h'

noncomputable def normalHermitianPartJointEigenbasisOfSubordinate
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (sub : NormalHermitianPartJointEigenbasisSubordinate ι) :
    NormalHermitianPartJointEigenbasis ι where
  basis := sub.basis
  H_eigenvalue := fun A hA j => (sub.eigenPair A hA j).2
  I_eigenvalue := fun A hA j => (sub.eigenPair A hA j).1
  H_eigen := by
    intro A hA j
    exact mulVec_of_toEuclideanLin_eigen (normalHermitianPart A) (sub.basis A hA j)
      (sub.eigenPair A hA j).2 (Module.End.mem_eigenspace_iff.mp (sub.mem_joint A hA j).1)
  I_eigen := by
    intro A hA j
    exact mulVec_of_toEuclideanLin_eigen (normalImagHermitianPart A) (sub.basis A hA j)
      (sub.eigenPair A hA j).1 (Module.End.mem_eigenspace_iff.mp (sub.mem_joint A hA j).2)

noncomputable def normalHermitianPartOracleOfJointEigenbasis
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (joint : NormalHermitianPartJointEigenbasis ι) :
    NormalHermitianPartSimultaneousDiagonalizationOracle ι where
  Q := fun A hA => matrixOfOrthonormalBasis (joint.basis A hA)
  unitary_Q := fun A hA => matrixOfOrthonormalBasis_unitary (joint.basis A hA)
  diag_H := by
    intro A hA
    exact isDiag_conjugated_of_eigenbasis
      (normalHermitianPart A) (joint.basis A hA) (joint.H_eigenvalue A hA)
      (joint.H_eigen A hA)
  diag_I := by
    intro A hA
    exact isDiag_conjugated_of_eigenbasis
      (normalImagHermitianPart A) (joint.basis A hA) (joint.I_eigenvalue A hA)
      (joint.I_eigen A hA)

noncomputable def normalHermitianPairOracleOfParts
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (partsOracle : NormalHermitianPartSimultaneousDiagonalizationOracle ι) :
    NormalHermitianPairDiagonalizationOracle ι where
  Hpart := normalHermitianPart
  Ipart := normalImagHermitianPart
  Q := partsOracle.Q
  unitary_Q := partsOracle.unitary_Q
  recombine := by
    intro A _hA
    exact normalHermitian_imag_recombine A
  diag_H := partsOracle.diag_H
  diag_I := partsOracle.diag_I

noncomputable def normalDiagonalizationOracleOfHermitianPair
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (pairOracle : NormalHermitianPairDiagonalizationOracle ι) :
    NormalDiagonalizationOracle ι where
  Q := pairOracle.Q
  unitary_Q := pairOracle.unitary_Q
  diagonalizes := by
    intro A hA
    let Q := pairOracle.Q A hA
    have hEq :
        Qᴴ * A * Q =
          Qᴴ * pairOracle.Hpart A * Q + Complex.I • (Qᴴ * pairOracle.Ipart A * Q) := by
      calc
        Qᴴ * A * Q =
            Qᴴ * (pairOracle.Hpart A + Complex.I • pairOracle.Ipart A) * Q := by
          conv_lhs => rw [pairOracle.recombine A hA]
        _ = Qᴴ * pairOracle.Hpart A * Q + Complex.I • (Qᴴ * pairOracle.Ipart A * Q) := by
          simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [hEq]
    exact (pairOracle.diag_H A hA).add ((pairOracle.diag_I A hA).smul Complex.I)

noncomputable def normalBlockReadyOracleOfDiagonalization
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (diagOracle : NormalDiagonalizationOracle ι) :
    NormalBlockReadyOracle ι where
  Q := diagOracle.Q
  unitary_Q := diagOracle.unitary_Q
  blockReady := by
    intro A hA
    exact normalBlockReady_of_isDiag ι (diagOracle.diagonalizes A hA)

set_option linter.unnecessarySimpa false in
noncomputable def normalSimilarityOracleOfBlockReady
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (blockOracle : NormalBlockReadyOracle ι) :
    NormalSimilarityOracle ι := by
  classical
  refine
    { Q := fun A =>
        if hA : IsNormalMatrix A then blockOracle.Q A hA else 1
      unitary_Q := ?_
      descentReady := ?_ }
  · intro A
    by_cases hA : IsNormalMatrix A
    · simpa [hA] using blockOracle.unitary_Q A hA
    · simpa [hA] using (isUnitaryMatrix_one : IsUnitaryMatrix (1 : Matrix ι ι ℂ))
  · intro A
    by_cases hA : IsNormalMatrix A
    · exact Or.inr (by simpa [hA] using blockOracle.blockReady A hA)
    · left
      intro hNormalSimilar
      exact hA (by simpa [hA] using hNormalSimilar)

/-- Unitary similarity transformation driven by a `NormalSimilarityOracle`. -/
noncomputable def normalUnitarySimilarityTransform
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (oracle : NormalSimilarityOracle ι) :
    Transformation (Matrix ι ι ℂ) where
  T := { Q : Matrix ι ι ℂ // IsUnitaryMatrix Q }
  Goal := NormalDescentReady ι
  apply := fun Q A => Q.1ᴴ * A * Q.1
  find := fun A _h => ⟨oracle.Q A, oracle.unitary_Q A⟩
  find_spec := by
    intro A _h
    exact oracle.descentReady A

/-- Head-tail lower-right-block reduction for a block-ready normal matrix. -/
noncomputable def normalHeadTailReduction
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :
    ReductionMethod ι ι (NormalTailIdx ι) (NormalTailIdx ι) ℂ :=
  SubmatrixMethod
    (headTailEquiv (α := ι))
    (headTailEquiv (α := ι))
    (NormalDescentReady ι)

/--
Normal spectral strategy core parameterized by a family of unitary-similarity
oracles, one for each nonempty finite linearly ordered index type.
-/
noncomputable def normal_strategy_core
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι) :
    SquareStrategyCore ℂ where
  SliceIdx := fun {ι} fι dι oι nι => @NormalTailIdx ι fι oι nι
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
      { transform := normalUnitarySimilarityTransform ι (oracle (ι := ι))
        reduction := normalHeadTailReduction ι
        goal_is_sliceable := rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (NormalTailIdx ι)
        μ_mono := by
          intro A t
          simp
        slice_progress := by
          intro A hA
          have hlt : Fintype.card (NormalTailIdx ι) < Fintype.card ι := by
            simpa [NormalTailIdx] using
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
