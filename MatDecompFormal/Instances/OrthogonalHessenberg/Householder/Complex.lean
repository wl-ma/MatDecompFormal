import MatDecompFormal.Instances.OrthogonalHessenberg.Concrete
import MatDecompFormal.Instances.QR.Details
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

universe u

namespace MatDecompFormal.Instances

open Matrix
open InnerProductSpace
open MatDecompFormal.Framework

/-!
# Complex Householder Unitary Hessenberg Step

This file instantiates the unitary boundary-column Hessenberg descent with a
phase-adjusted complex Householder reflection.  The one-step matrix is the
standard-basis matrix of the reflection in `(ℂ ∙ (x - w))ᗮ`, where `w` is the
phase-adjusted multiple of the head standard basis vector.
-/

/-- Phase used by the complex Householder target vector. -/
noncomputable def complexHouseholderPhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / (‖z‖ : ℂ)

lemma complexHouseholderPhase_norm (z : ℂ) :
    ‖complexHouseholderPhase z‖ = 1 := by
  by_cases h : z = 0
  · simp [complexHouseholderPhase, h]
  · have hnR : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h
    simp [complexHouseholderPhase, h, hnR]

lemma complexHouseholderPhase_mul_star (z : ℂ) :
    complexHouseholderPhase z * star z = (‖z‖ : ℂ) := by
  by_cases h : z = 0
  · simp [complexHouseholderPhase, h]
  · have hnR : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hnC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hnR
    calc
      complexHouseholderPhase z * star z =
          (z / (‖z‖ : ℂ)) * star z := by
        simp [complexHouseholderPhase, h]
      _ = (z * star z) / (‖z‖ : ℂ) := by ring
      _ = ((‖z‖ : ℂ) ^ 2) / (‖z‖ : ℂ) := by
        rw [show z * star z = (‖z‖ : ℂ) ^ 2 by
          simpa [Complex.star_def] using Complex.mul_conj' z]
      _ = (‖z‖ : ℂ) := by field_simp [hnC]

lemma star_complexHouseholderPhase_mul (z : ℂ) :
    star (complexHouseholderPhase z) * z = (‖z‖ : ℂ) := by
  have h := congrArg star (complexHouseholderPhase_mul_star z)
  simpa using h

lemma complexHouseholderPhase_norm_sq (z : ℂ) :
    star (complexHouseholderPhase z) * complexHouseholderPhase z = 1 := by
  have hnorm := complexHouseholderPhase_norm z
  have h := Complex.conj_mul' (complexHouseholderPhase z)
  simpa [Complex.star_def, hnorm] using h

/-- Phase-adjusted head-axis target for the active boundary vector. -/
noncomputable def complexHouseholderTarget
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (x : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (complexHouseholderPhase (x (headElem (α := ι))) * (‖x‖ : ℂ)) •
    EuclideanSpace.basisFun ι ℂ (headElem (α := ι))

lemma complexHouseholder_inner_add_sub_zero
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (x : EuclideanSpace ℂ ι) :
    ⟪x + complexHouseholderTarget x, x - complexHouseholderTarget x⟫_ℂ = 0 := by
  let e : EuclideanSpace ℂ ι := EuclideanSpace.basisFun ι ℂ (headElem (α := ι))
  let a : ℂ := x (headElem (α := ι))
  let n : ℂ := (‖x‖ : ℂ)
  let p : ℂ := complexHouseholderPhase a
  have htarget : complexHouseholderTarget x = (p * n) • e := by
    simp [complexHouseholderTarget, e, a, n, p]
  have he_left : ⟪e, x⟫_ℂ = a := by
    simpa [e, a] using
      EuclideanSpace.basisFun_inner ι ℂ x (headElem (α := ι))
  have he_right : ⟪x, e⟫_ℂ = star a := by
    have h0 : star ⟪x, e⟫_ℂ = a := by
      exact (inner_conj_symm (𝕜 := ℂ) e x).trans he_left
    have h1 := congrArg star h0
    simpa using h1
  have hpe : p * star a = (‖a‖ : ℂ) := by
    simpa [p, a] using complexHouseholderPhase_mul_star a
  have hsp : star p * a = (‖a‖ : ℂ) := by
    simpa [p, a] using star_complexHouseholderPhase_mul a
  have hpp : star p * p = 1 := by
    simpa [p, a] using complexHouseholderPhase_norm_sq a
  have hen : ‖e‖ = 1 := by simp [e]
  have hnstar : star n = n := by simp [n]
  rw [htarget]
  simp [he_left, he_right, hen, hnstar]
  calc
    n ^ 2 + a * (star p * n) - p * n * (star a + star p * n)
        = n ^ 2 + n * (star p * a) - n * (p * star a) -
            (star p * p) * n ^ 2 := by ring
    _ = 0 := by rw [hsp, hpe, hpp]; ring

lemma complexHouseholder_reflection_apply
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (x : EuclideanSpace ℂ ι) :
    Submodule.reflection (ℂ ∙ (x - complexHouseholderTarget x))ᗮ x =
      complexHouseholderTarget x := by
  set R : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
    Submodule.reflection (ℂ ∙ (x - complexHouseholderTarget x))ᗮ
  suffices R x + R x = complexHouseholderTarget x + complexHouseholderTarget x by
    apply smul_right_injective (EuclideanSpace ℂ ι) (show (2 : ℂ) ≠ 0 by norm_num)
    simpa [two_smul] using this
  have hdiff : R (x - complexHouseholderTarget x) =
      -(x - complexHouseholderTarget x) := by
    simpa [R] using
      (Submodule.reflection_orthogonalComplement_singleton_eq_neg
        (𝕜 := ℂ) (x - complexHouseholderTarget x))
  have hsum : R (x + complexHouseholderTarget x) =
      x + complexHouseholderTarget x := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact complexHouseholder_inner_add_sub_zero x
  convert congr_arg₂ (· + ·) hsum hdiff using 1
  · simp
  · abel

/-- The complex Householder reflection sending the active vector to head-axis form. -/
noncomputable def complexHouseholderReflection
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (x : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  Submodule.reflection (ℂ ∙ (x - complexHouseholderTarget x))ᗮ

/-- Orthonormal basis obtained by applying the Householder reflection to the standard basis. -/
noncomputable def complexHouseholderBasis
    {ι : Type u} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (x : EuclideanSpace ℂ ι) :
    OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι) :=
  (EuclideanSpace.basisFun ι ℂ).map (complexHouseholderReflection x)

/--
Concrete complex Householder matrix predicate.

This records that the matrix is obtained from the phase-adjusted complex
Householder reflection used by the boundary oracle, rather than merely being an
arbitrary unitary matrix tagged as Householder.
-/
def IsComplexHouseholderMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (Q : Matrix ι ι ℂ) : Prop :=
  ∃ x : EuclideanSpace ℂ ι,
    Q = matrixOfOrthonormalBasis (complexHouseholderBasis x)

theorem isUnitaryMatrix_of_isComplexHouseholderMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {Q : Matrix ι ι ℂ} :
    IsComplexHouseholderMatrix Q → IsUnitaryMatrix Q := by
  intro hQ
  rcases hQ with ⟨x, rfl⟩
  exact matrixOfOrthonormalBasis_unitary (complexHouseholderBasis x)

lemma conjTranspose_matrixOfOrthonormalBasis_mulVec_apply'
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (v : EuclideanSpace ℂ ι) (i : ι) :
    ((matrixOfOrthonormalBasis b)ᴴ *ᵥ v.ofLp) i = ⟪b i, v⟫_ℂ := by
  simp [matrixOfOrthonormalBasis, Matrix.mulVec, Matrix.conjTranspose_apply,
    Module.Basis.toMatrix_apply, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]
  rfl

lemma complexHouseholderBasis_conjTranspose_mulVec
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (x : EuclideanSpace ℂ ι) :
    (matrixOfOrthonormalBasis (complexHouseholderBasis x))ᴴ *ᵥ x.ofLp =
      (complexHouseholderTarget x).ofLp := by
  ext i
  rw [conjTranspose_matrixOfOrthonormalBasis_mulVec_apply'
    (complexHouseholderBasis x) x i]
  calc
    ⟪complexHouseholderBasis x i, x⟫_ℂ =
        ⟪EuclideanSpace.basisFun ι ℂ i, complexHouseholderReflection x x⟫_ℂ := by
      simpa [complexHouseholderBasis] using
        (LinearIsometryEquiv.inner_map_eq_flip (complexHouseholderReflection x)
          (EuclideanSpace.basisFun ι ℂ i) x)
    _ = ⟪EuclideanSpace.basisFun ι ℂ i, complexHouseholderTarget x⟫_ℂ := by
      rw [complexHouseholderReflection, complexHouseholder_reflection_apply]
    _ = (complexHouseholderTarget x).ofLp i := by
      rw [EuclideanSpace.basisFun_inner]

/-- Complex Householder boundary-step factor. -/
noncomputable def householderBoundaryStepQ
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    Matrix x_sub.1.ι x_sub.1.ι ℂ := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact matrixOfOrthonormalBasis
    (complexHouseholderBasis (boundaryColumnVec x_sub.1.c))

theorem householder_boundary_step_unitary
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    IsUnitaryMatrix (householderBoundaryStepQ x_sub) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact matrixOfOrthonormalBasis_unitary
    (complexHouseholderBasis (boundaryColumnVec x_sub.1.c))

theorem householderBoundaryStepQ_isComplexHouseholderMatrix
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    @IsComplexHouseholderMatrix x_sub.1.ι x_sub.1.fintype_ι
      x_sub.1.decEq_ι x_sub.1.linOrder_ι
      (posHessenbergBoundaryUniverse_nonempty x_sub)
      (householderBoundaryStepQ x_sub) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact ⟨boundaryColumnVec x_sub.1.c, rfl⟩

theorem householderBoundaryStepQ_isProductOfComplexHouseholderMatrix
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    IsProductOf
      (@IsComplexHouseholderMatrix x_sub.1.ι x_sub.1.fintype_ι
        x_sub.1.decEq_ι x_sub.1.linOrder_ι
        (posHessenbergBoundaryUniverse_nonempty x_sub))
      (householderBoundaryStepQ x_sub) := by
  refine ⟨[householderBoundaryStepQ x_sub], ?_, ?_⟩
  · intro M hM
    have hM' : M = householderBoundaryStepQ x_sub := by
      simpa using hM
    subst M
    exact householderBoundaryStepQ_isComplexHouseholderMatrix x_sub
  · simp [matrixProduct]

theorem householder_boundary_step_ready
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    HessenbergBoundaryReady
      (unitaryHessenbergBoundarySimilarityObject
        (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
        (householderBoundaryStepQ x_sub)) := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  intro _hne i hi
  let x : EuclideanSpace ℂ x_sub.1.ι := boundaryColumnVec x_sub.1.c
  have hmul := congrFun (complexHouseholderBasis_conjTranspose_mulVec x) i
  have hzero : (complexHouseholderTarget x).ofLp i = 0 := by
    simp [complexHouseholderTarget, hi]
  have hentry : ((householderBoundaryStepQ x_sub)ᴴ *ᵥ x.ofLp) i = 0 :=
    hmul.trans hzero
  simpa [unitaryHessenbergBoundarySimilarityObject, householderBoundaryStepQ, x,
    boundaryColumnVec, Matrix.mulVec, Matrix.mul_apply] using hentry

/-- Complex unitary Householder boundary-step oracle. -/
noncomputable def householderUnitaryBoundaryStepOracle :
    UnitaryHessenbergBoundaryStepOracle.{u} where
  Q := householderBoundaryStepQ
  unitary_Q := householder_boundary_step_unitary
  ready := householder_boundary_step_ready

/-- Complex unitary Hessenberg reduction via the Householder boundary oracle. -/
theorem exists_unitary_hessenberg_reduction_householder
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasUnitaryHessenberg A :=
  exists_unitary_hessenberg_reduction householderUnitaryBoundaryStepOracle A

/--
Concrete step-trace data for the complex Householder Hessenberg route.

This records the actual Householder product supplied by every positive
boundary step, together with the final framework decomposition.  It is a
stronger route-specific API than the legacy route-tagged final witness trace.
-/
structure ComplexHouseholderHessenbergStepTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) : Prop where
  decomposition : HasUnitaryHessenberg A
  boundaryStepProduct :
    ∀ x_sub : PosHessenbergBoundaryUniverse.{u} ℂ,
      IsProductOf
        (@IsComplexHouseholderMatrix x_sub.1.ι x_sub.1.fintype_ι
          x_sub.1.decEq_ι x_sub.1.linOrder_ι
          (posHessenbergBoundaryUniverse_nonempty x_sub))
        (householderBoundaryStepQ x_sub)

theorem hasUnitaryHessenberg_of_complexHouseholderHessenbergStepTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ} :
    ComplexHouseholderHessenbergStepTrace A → HasUnitaryHessenberg A :=
  ComplexHouseholderHessenbergStepTrace.decomposition

/--
Complex Householder Hessenberg route with boundary-step product data.

This records the boundary oracle products used by the framework route; it is
not a full recursive embedded-step execution trace.
-/
theorem exists_unitary_hessenberg_reduction_householder_with_boundary_step_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    ComplexHouseholderHessenbergStepTrace A := by
  exact
    { decomposition := exists_unitary_hessenberg_reduction_householder A
      boundaryStepProduct := fun x_sub =>
        householderBoundaryStepQ_isProductOfComplexHouseholderMatrix x_sub }

/--
Compatibility name for the boundary-step trace.
Prefer `exists_unitary_hessenberg_reduction_householder_with_boundary_step_trace`.
-/
theorem exists_unitary_hessenberg_reduction_householder_with_step_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    ComplexHouseholderHessenbergStepTrace A :=
  exists_unitary_hessenberg_reduction_householder_with_boundary_step_trace A

/--
Compatibility witness trace for the Householder boundary route.

This route-tagged witness records the final unitary Hessenberg decomposition,
not the recursive boundary-step execution sequence.
-/
theorem exists_unitary_hessenberg_reduction_householder_with_witness_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    UnitaryHessenbergTrace "complex-householder-boundary" A :=
  witnessData_of_hasUnitaryHessenberg
    "complex-householder-boundary"
    (hasUnitaryHessenberg_of_complexHouseholderHessenbergStepTrace
      (exists_unitary_hessenberg_reduction_householder_with_boundary_step_trace A))

/--
Compatibility name for the route-tagged final witness trace.
Prefer `exists_unitary_hessenberg_reduction_householder_with_witness_trace`.
-/
theorem exists_unitary_hessenberg_reduction_householder_with_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    UnitaryHessenbergTrace "complex-householder-boundary" A :=
  exists_unitary_hessenberg_reduction_householder_with_witness_trace A

end MatDecompFormal.Instances
