import MatDecompFormal.Instances.Tridiagonalization.Existence
import MatDecompFormal.Instances.Tridiagonalization.Concrete
import MatDecompFormal.Instances.Normal.Existence

universe u

namespace MatDecompFormal.Instances

open Matrix

/-!
# Spectral Fallback for Tridiagonalization

This file keeps the normal spectral theorem as a stronger fallback.  The public
tridiagonalization theorem below is routed through the concrete boundary-aware
descent oracle from `Concrete.lean`.
-/

variable {ι : Type*}

lemma isNormalMatrix_of_isHermitian
    [Fintype ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    IsNormalMatrix A := by
  rw [IsNormalMatrix, hA.eq]

lemma isTridiagonal_of_isDiag
    [Fintype ι] [LinearOrder ι]
    {D : Matrix ι ι ℂ} (hD : D.IsDiag) :
    IsTridiagonal D := by
  intro i j hij
  apply hD
  intro hEq
  subst j
  rcases hij with hij | hij
  · have hlt : finiteOrderRank ι i < finiteOrderRank ι i :=
      lt_trans (Nat.lt_succ_self _) hij
    exact Nat.lt_irrefl _ hlt
  · have hlt : finiteOrderRank ι i < finiteOrderRank ι i :=
      lt_trans (Nat.lt_succ_self _) hij
    exact Nat.lt_irrefl _ hlt

theorem hasUnitaryTridiagonalization_of_hasNormalSpectral
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ}
    (hHerm : A.IsHermitian) (hSpec : HasNormalSpectral A) :
    HasUnitaryTridiagonalization A := by
  rcases hSpec with ⟨U, D, hU, hD, hEq⟩
  have hD_eq : D = Uᴴ * A * U :=
    unitary_similarity_target_eq hU hEq
  have hDHerm : D.IsHermitian := by
    rw [hD_eq]
    exact isHermitian_unitarySimilarity hHerm
  exact ⟨U, D, hU, isTridiagonal_of_isDiag hD, hDHerm, hEq⟩

theorem exists_unitary_tridiagonalization_spectral
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A :=
  hasUnitaryTridiagonalization_of_hasNormalSpectral hA
    (exists_normal_spectral_decomposition A (isNormalMatrix_of_isHermitian hA))

/--
Spectral fallback step oracle.

The chosen transform is identity; lift-readiness is discharged by the stronger
normal spectral theorem for Hermitian matrices.  This keeps the public theorem
on the strict descent-framework route while the algorithmic Householder/Givens
oracle remains future work.
-/
noncomputable def tridiagonalizationSpectralStepOracle
    (ι : Type u) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    TridiagonalizationStepOracle ι where
  Q := fun _ => 1
  unitary_Q := fun _ => isUnitaryMatrix_one
  liftReady := by
    intro _A _hTail hHerm
    exact exists_unitary_tridiagonalization_spectral _ hHerm

/--
Unconditional Hermitian unitary tridiagonalization, routed through the strict
tridiagonalization descent framework.
-/
theorem exists_unitary_tridiagonalization
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A := by
  exact exists_unitary_tridiagonalization_boundary_framework_oracle
    tridiagonalizationBoundaryStepOracle A hA

end MatDecompFormal.Instances
