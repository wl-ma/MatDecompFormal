/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Tridiagonalization.Existence
import MatDecompFormal.Instances.Tridiagonalization.Concrete
import MatDecompFormal.Instances.Normal.Existence
import MatDecompFormal.Instances.OrthogonalHessenberg.Givens.Complex
import MatDecompFormal.Instances.OrthogonalHessenberg.Householder.Complex

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

/--
Public boundary-framework theorem for Hermitian unitary tridiagonalization.

This is the framework-routed theorem used for implementation claims: the
concrete `tridiagonalizationBoundaryStepOracle` supplies the boundary step,
and the boundary descent driver assembles the final decomposition.
-/
theorem exists_unitary_tridiagonalization_boundary_framework
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A :=
  exists_unitary_tridiagonalization_boundary_framework_oracle
    tridiagonalizationBoundaryStepOracle A hA

/--
Hermitian unitary tridiagonalization obtained through the complex Householder
unitary Hessenberg boundary route.
-/
theorem exists_unitary_tridiagonalization_householder_boundary
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A :=
  exists_unitary_tridiagonalization_of_unitaryHessenbergOracle
    householderUnitaryBoundaryStepOracle A hA

/--
Hermitian unitary tridiagonalization obtained through the complex Givens
unitary Hessenberg boundary route.
-/
theorem exists_unitary_tridiagonalization_givens_boundary
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A :=
  exists_unitary_tridiagonalization_of_unitaryHessenbergOracle
    givensUnitaryBoundaryStepOracle A hA

/--
Concrete Householder step trace target for tridiagonalization.

Unlike `HouseholderTridiagonalizationTrace`, this predicate uses the concrete
complex Householder matrix predicate from the boundary-step construction instead
of the route-tagged unitary predicate.
-/
abbrev ComplexHouseholderTridiagonalizationTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) : Prop :=
  TridiagonalizationTrace
    (@IsComplexHouseholderMatrix ι ‹Fintype ι› ‹DecidableEq ι› ‹LinearOrder ι›
      ‹Nonempty ι›) A

/--
Concrete Givens step trace target for tridiagonalization.

This records products of embedded two-coordinate complex Givens rotations rather
than arbitrary unitary matrices carrying a Givens route tag.
-/
abbrev ComplexGivensTridiagonalizationTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) : Prop :=
  TridiagonalizationTrace
    (@IsComplexGivensMatrix ι ‹Fintype ι› ‹DecidableEq ι› ‹LinearOrder ι›
      ‹Nonempty ι›) A

theorem hasUnitaryTridiagonalization_of_complexHouseholderTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} :
    ComplexHouseholderTridiagonalizationTrace A →
      HasUnitaryTridiagonalization A :=
  hasUnitaryTridiagonalization_of_product

theorem hasUnitaryTridiagonalization_of_complexGivensTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} :
    ComplexGivensTridiagonalizationTrace A →
      HasUnitaryTridiagonalization A :=
  hasUnitaryTridiagonalization_of_product

/--
Boundary-step trace data for the Householder tridiagonalization route.

This is the first concrete trace layer: it records that the boundary oracle used
by the route supplies an actual product of complex Householder matrices at each
positive boundary subproblem.  The full recursive embedded-step trace still
requires a separate block-embedding closure theorem.
-/
structure ComplexHouseholderTridiagonalizationStepTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) : Prop where
  decomposition : HasUnitaryTridiagonalization A
  boundaryStepProduct :
    ∀ x_sub : PosHessenbergBoundaryUniverse.{u} ℂ,
      IsProductOf
        (@IsComplexHouseholderMatrix x_sub.1.ι x_sub.1.fintype_ι
          x_sub.1.decEq_ι x_sub.1.linOrder_ι
          (posHessenbergBoundaryUniverse_nonempty x_sub))
        (householderBoundaryStepQ x_sub)

/--
Boundary-step trace data for the Givens tridiagonalization route.

The Givens boundary sweep is expanded into the concrete list of embedded
two-coordinate Givens rotations whose product is the oracle step.
-/
structure ComplexGivensTridiagonalizationStepTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) : Prop where
  decomposition : HasUnitaryTridiagonalization A
  boundaryStepProduct :
    ∀ x_sub : PosHessenbergBoundaryUniverse.{u} ℂ,
      IsProductOf
        (@IsComplexGivensMatrix x_sub.1.ι x_sub.1.fintype_ι
          x_sub.1.decEq_ι x_sub.1.linOrder_ι
          (posHessenbergBoundaryUniverse_nonempty x_sub))
        (givensBoundaryStepQ x_sub)

theorem hasUnitaryTridiagonalization_of_complexHouseholderStepTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ} :
    ComplexHouseholderTridiagonalizationStepTrace A →
      HasUnitaryTridiagonalization A :=
  ComplexHouseholderTridiagonalizationStepTrace.decomposition

theorem hasUnitaryTridiagonalization_of_complexGivensStepTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ} :
    ComplexGivensTridiagonalizationStepTrace A →
      HasUnitaryTridiagonalization A :=
  ComplexGivensTridiagonalizationStepTrace.decomposition

/--
Householder tridiagonalization with boundary-step product data.

The witness records the boundary oracle product layer plus the final framework
decomposition; it is not a complete recursive embedded-step trace.
-/
theorem exists_householder_tridiagonalization_with_boundary_step_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ComplexHouseholderTridiagonalizationStepTrace A := by
  exact
    { decomposition := exists_unitary_tridiagonalization_householder_boundary A hA
      boundaryStepProduct := fun x_sub =>
        householderBoundaryStepQ_isProductOfComplexHouseholderMatrix x_sub }

/--
Givens tridiagonalization with boundary-step product data.

The witness records the boundary oracle product layer plus the final framework
decomposition; it is not a complete recursive embedded-step trace.
-/
theorem exists_givens_tridiagonalization_with_boundary_step_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ComplexGivensTridiagonalizationStepTrace A := by
  exact
    { decomposition := exists_unitary_tridiagonalization_givens_boundary A hA
      boundaryStepProduct := fun x_sub =>
        givensBoundaryStepQ_isProductOfComplexGivensMatrix x_sub }

/--
Compatibility name for the Householder boundary-step trace.
Prefer `exists_householder_tridiagonalization_with_boundary_step_trace`.
-/
theorem exists_householder_tridiagonalization_with_step_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ComplexHouseholderTridiagonalizationStepTrace A :=
  exists_householder_tridiagonalization_with_boundary_step_trace A hA

/--
Compatibility name for the Givens boundary-step trace.
Prefer `exists_givens_tridiagonalization_with_boundary_step_trace`.
-/
theorem exists_givens_tridiagonalization_with_step_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ComplexGivensTridiagonalizationStepTrace A :=
  exists_givens_tridiagonalization_with_boundary_step_trace A hA

theorem exists_householder_product_tridiagonalization
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasHouseholderProductTridiagonalization A :=
  hasHouseholderProductTridiagonalization_of_hasUnitary
    (hasUnitaryTridiagonalization_of_complexHouseholderStepTrace
      (exists_householder_tridiagonalization_with_boundary_step_trace A hA))

theorem exists_givens_product_tridiagonalization
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasGivensProductTridiagonalization A :=
  hasGivensProductTridiagonalization_of_hasUnitary
    (hasUnitaryTridiagonalization_of_complexGivensStepTrace
      (exists_givens_tridiagonalization_with_boundary_step_trace A hA))

/--
Householder tridiagonalization with a final-factor product trace.

This is a product witness for the final unitary factor, projected from the
boundary-step route; it is not a full recursive execution trace.
-/
theorem exists_householder_tridiagonalization_with_product_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HouseholderTridiagonalizationTrace A :=
  hasHouseholderProductTridiagonalization_of_hasUnitary
    (hasUnitaryTridiagonalization_of_complexHouseholderStepTrace
      (exists_householder_tridiagonalization_with_boundary_step_trace A hA))

/--
Givens tridiagonalization with a final-factor product trace.

This is a product witness for the final unitary factor, projected from the
boundary-step route; it is not a full recursive execution trace.
-/
theorem exists_givens_tridiagonalization_with_product_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    GivensTridiagonalizationTrace A :=
  hasGivensProductTridiagonalization_of_hasUnitary
    (hasUnitaryTridiagonalization_of_complexGivensStepTrace
      (exists_givens_tridiagonalization_with_boundary_step_trace A hA))

/--
Compatibility name for the Householder final-factor product trace.
Prefer `exists_householder_tridiagonalization_with_product_trace`.
-/
theorem exists_householder_tridiagonalization_with_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HouseholderTridiagonalizationTrace A :=
  exists_householder_tridiagonalization_with_product_trace A hA

/--
Compatibility name for the Givens final-factor product trace.
Prefer `exists_givens_tridiagonalization_with_product_trace`.
-/
theorem exists_givens_tridiagonalization_with_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    GivensTridiagonalizationTrace A :=
  exists_givens_tridiagonalization_with_product_trace A hA

end MatDecompFormal.Instances
