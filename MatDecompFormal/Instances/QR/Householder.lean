import MatDecompFormal.Instances.QR.Driver
import MatDecompFormal.Instances.QR.Strategy
import MatDecompFormal.Components.Properties.Triangular
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Components.Properties

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable abbrev qrHouseholderTransform
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :=
  qrDirectOrthogonalTransform ι

noncomputable abbrev qr_householder_framework_inst := qr_framework_inst


noncomputable def householderMatrix
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (u : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  ((EuclideanSpace.basisFun ι ℝ).toBasis.toMatrix
    ((EuclideanSpace.basisFun ι ℝ).map ((ℝ ∙ u)ᗮ).reflection))ᵀ

def IsHouseholderMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) : Prop :=
  ∃ u : EuclideanSpace ℝ ι, Q = householderMatrix ι u

def IsHouseholderProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) : Prop :=
  IsProductOf IsHouseholderMatrix Q

abbrev HasHouseholderQR [LinearOrder ι] (A : Matrix ι ι ℝ) : Prop :=
  HasStructuredQR IsHouseholderProduct A

lemma hasQR_of_hasHouseholderQR
    [LinearOrder ι]
    {A : Matrix ι ι ℝ} (hA : HasHouseholderQR A) :
    HasQR A := by
  exact hasQR_of_hasStructuredQR hA

lemma qrHeadOrthogonalStep_isHouseholderMatrix
    [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ¬ QRReady ι A) :
    IsHouseholderMatrix (qrHeadOrthogonalStep ι A hA) := by
  refine ⟨qrHeadAxisVec ι - qrHeadUnitVec ι A hA, ?_⟩
  simp [IsHouseholderMatrix, householderMatrix, qrHeadOrthogonalStep, qrHeadBasis,
    qrHeadReflector, qrHeadAxisVec]

lemma qrHeadOrthogonalStep_isHouseholderProduct
    [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ¬ QRReady ι A) :
    IsHouseholderProduct (qrHeadOrthogonalStep ι A hA) := by
  refine ⟨[qrHeadOrthogonalStep ι A hA], ?_, ?_⟩
  · intro M hM
    simp at hM
    rcases hM with rfl
    exact qrHeadOrthogonalStep_isHouseholderMatrix A hA
  · simp [matrixProduct]

lemma householderMatrix_transpose_eq_reflectionToMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : EuclideanSpace ℝ ι) :
    (householderMatrix ι u)ᵀ =
      LinearMap.toMatrix
        (EuclideanSpace.basisFun ι ℝ).toBasis
        (EuclideanSpace.basisFun ι ℝ).toBasis
        (((ℝ ∙ u)ᗮ).reflection.toLinearMap) := by
  ext i j
  simp [householderMatrix, LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply]

lemma reflectionToMatrix_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : EuclideanSpace ℝ ι) :
    (LinearMap.toMatrix
      (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis
      (((ℝ ∙ u)ᗮ).reflection.toLinearMap))ᵀ =
    LinearMap.toMatrix
      (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis
      (((ℝ ∙ u)ᗮ).reflection.toLinearMap) := by
  let f : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := ((ℝ ∙ u)ᗮ).reflection.toLinearMap
  have hs : f.IsSymmetric := by
    intro x y
    simpa [f, Submodule.reflection_symm] using (((ℝ ∙ u)ᗮ).reflection.inner_map_eq_flip x y)
  have hmat :=
    LinearMap.toMatrix_adjoint
      (v₁ := EuclideanSpace.basisFun ι ℝ)
      (v₂ := EuclideanSpace.basisFun ι ℝ)
      f
  rw [hs.adjoint_eq] at hmat
  simpa [f] using hmat.symm

lemma householderMatrix_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : EuclideanSpace ℝ ι) :
    (householderMatrix ι u)ᵀ = householderMatrix ι u := by
  have h1 := householderMatrix_transpose_eq_reflectionToMatrix u
  have h2 := reflectionToMatrix_transpose u
  have h3 :
      householderMatrix ι u =
        (LinearMap.toMatrix
          (EuclideanSpace.basisFun ι ℝ).toBasis
          (EuclideanSpace.basisFun ι ℝ).toBasis
          (((ℝ ∙ u)ᗮ).reflection.toLinearMap))ᵀ := by
    simpa using congrArg Matrix.transpose h1
  calc
    (householderMatrix ι u)ᵀ =
        LinearMap.toMatrix
          (EuclideanSpace.basisFun ι ℝ).toBasis
          (EuclideanSpace.basisFun ι ℝ).toBasis
          (((ℝ ∙ u)ᗮ).reflection.toLinearMap) := h1
    _ =
        (LinearMap.toMatrix
          (EuclideanSpace.basisFun ι ℝ).toBasis
          (EuclideanSpace.basisFun ι ℝ).toBasis
          (((ℝ ∙ u)ᗮ).reflection.toLinearMap))ᵀ := by
            symm
            exact reflectionToMatrix_transpose u
    _ = householderMatrix ι u := by simpa using h3.symm

lemma isHouseholderMatrix_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : IsHouseholderMatrix Q) :
    IsHouseholderMatrix Qᵀ := by
  rcases hQ with ⟨u, rfl⟩
  refine ⟨u, ?_⟩
  exact householderMatrix_transpose u

lemma isHouseholderProduct_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : IsHouseholderProduct Q) :
    IsHouseholderProduct Qᵀ := by
  exact isProductOf_transpose
    IsHouseholderMatrix
    (h_mem := fun M hM => isHouseholderMatrix_transpose hM)
    hQ

/-- Transport a Householder-flavored QR decomposition back across a left Householder product,
assuming transpose-side structure has already been supplied. -/
theorem householder_transport_of_orthogonal_left_of_transpose
    [LinearOrder ι]
    (H A : Matrix ι ι ℝ)
    (hH_prod_T : IsHouseholderProduct Hᵀ)
    (hH_orth : IsOrthogonalMatrix H)
    (hH_orth_T : IsOrthogonalMatrix Hᵀ)
    (hQR : HasHouseholderQR (H * A)) :
    HasHouseholderQR A := by
  rcases hQR with ⟨Q, R', hQ_prod, hQ_orth, hR, hEq⟩
  refine ⟨Hᵀ * Q, R', ?_, ?_, hR, ?_⟩
  · exact isProductOf_mul
      IsHouseholderMatrix
      hH_prod_T
      hQ_prod
  · exact isOrthogonalMatrix_mul hH_orth_T hQ_orth
  · calc
      A = (Hᵀ * H) * A := by
        have hHH := congrArg (fun M => M * A) hH_orth
        simpa [IsOrthogonalMatrix, Matrix.mul_assoc] using hHH.symm
      _ = Hᵀ * (H * A) := by rw [Matrix.mul_assoc]
      _ = Hᵀ * (Q * R') := by rw [hEq]
      _ = (Hᵀ * Q) * R' := by rw [Matrix.mul_assoc]

/-- Transport a Householder-flavored QR decomposition back across a left Householder product. -/
theorem householder_transport_of_orthogonal_left
    [LinearOrder ι]
    (H A : Matrix ι ι ℝ)
    (hH_prod : IsHouseholderProduct H)
    (hH_orth : IsOrthogonalMatrix H)
    (hQR : HasHouseholderQR (H * A)) :
    HasHouseholderQR A := by
  exact householder_transport_of_orthogonal_left_of_transpose H A
    (isHouseholderProduct_transpose hH_prod)
    hH_orth
    (isOrthogonalMatrix_transpose hH_orth)
    hQR

noncomputable def householderStdMatrix
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (φ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  LinearMap.toMatrix
    (EuclideanSpace.basisFun ι ℝ).toBasis
    (EuclideanSpace.basisFun ι ℝ).toBasis
    φ.toLinearMap

@[simp] lemma householderStdMatrix_reflection
    (u : EuclideanSpace ℝ ι) :
    householderStdMatrix ι (((ℝ ∙ u)ᗮ).reflection) = householderMatrix ι u := by
  calc
    householderStdMatrix ι (((ℝ ∙ u)ᗮ).reflection) = (householderMatrix ι u)ᵀ := by
      symm
      exact householderMatrix_transpose_eq_reflectionToMatrix u
    _ = householderMatrix ι u := householderMatrix_transpose u

@[simp] lemma householderStdMatrix_mul
    (φ ψ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    householderStdMatrix ι (φ * ψ) =
      householderStdMatrix ι φ * householderStdMatrix ι ψ := by
  simpa [householderStdMatrix, LinearIsometryEquiv.mul_def] using
    (LinearMap.toMatrix_comp
      ((EuclideanSpace.basisFun ι ℝ).toBasis)
      ((EuclideanSpace.basisFun ι ℝ).toBasis)
      ((EuclideanSpace.basisFun ι ℝ).toBasis)
      φ.toLinearMap ψ.toLinearMap)

lemma householderStdMatrix_prod
    (l : List (EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)) :
    householderStdMatrix ι l.prod = ((l.map (householderStdMatrix ι)).prod) := by
  induction l with
  | nil =>
      ext i j
      simp [householderStdMatrix, LinearMap.toMatrix_apply, Matrix.one_apply]
  | cons φ l ih =>
      simp [householderStdMatrix_mul, ih]

lemma isHouseholderProduct_of_isOrthogonalMatrix
    (Q : Matrix ι ι ℝ)
    (hQ : IsOrthogonalMatrix Q) :
    IsHouseholderProduct Q := by
  let L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := Matrix.toEuclideanLin Q
  have hcomp : L.adjoint.comp L = 1 := by
    ext x i
    have hAdj : L.adjoint = Matrix.toEuclideanLin Qᵀ := by
      symm
      simpa [L] using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := Q))
    have hQvec : (Qᵀ * Q) *ᵥ x.ofLp = x.ofLp := by
      simpa [IsOrthogonalMatrix] using congrArg (fun M => M *ᵥ x.ofLp) hQ
    calc
      ((L.adjoint.comp L) x) i = (((Qᵀ * Q) *ᵥ x.ofLp) i) := by
        simp [LinearMap.comp_apply, hAdj, L, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
      _ = x.ofLp i := by simpa using congrArg (fun v => v i) hQvec
      _ = x i := by rfl
  have hinner : ∀ x y : EuclideanSpace ℝ ι, inner ℝ (L x) (L y) = inner ℝ x y := by
    intro x y
    calc
      inner ℝ (L x) (L y) = inner ℝ x (L.adjoint (L y)) := by
        simpa using (LinearMap.adjoint_inner_right L x (L y)).symm
      _ = inner ℝ x ((L.adjoint.comp L) y) := by rfl
      _ = inner ℝ x y := by simpa [hcomp]
  let li : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ ι := L.isometryOfInner hinner
  let φ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι := li.toLinearIsometryEquiv rfl
  have hφL : φ.toLinearMap = L := by
    ext x
    rfl
  have hφQ : householderStdMatrix ι φ = Q := by
    calc
      householderStdMatrix ι φ =
          LinearMap.toMatrix
            (EuclideanSpace.basisFun ι ℝ).toBasis
            (EuclideanSpace.basisFun ι ℝ).toBasis
            L := by
              simp [householderStdMatrix, hφL]
      _ = Q := by
            simpa [L, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
              (LinearMap.toMatrix_toLin
                (v₁ := (EuclideanSpace.basisFun ι ℝ).toBasis)
                (v₂ := (EuclideanSpace.basisFun ι ℝ).toBasis)
                Q)
  rcases LinearIsometryEquiv.reflections_generate_dim φ with ⟨l, _, hfac⟩
  refine ⟨l.map (fun u => householderMatrix ι u), ?_, ?_⟩
  · intro M hM
    rcases List.mem_map.mp hM with ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  · rw [← hφQ, hfac, householderStdMatrix_prod]
    simpa [List.map_map, Function.comp_def, matrixProduct_eq_prod] using
      congrArg List.prod (List.map_congr rfl (fun u _ => householderStdMatrix_reflection u))



theorem base_householderQR_subsingleton
    [LinearOrder ι] [Subsingleton ι] (A : Matrix ι ι ℝ) :
    HasHouseholderQR A := by
  refine ⟨1, A, ?_, ?_, ?_, ?_⟩
  · exact isProductOf_one IsHouseholderMatrix
  · exact isOrthogonalMatrix_one
  · exact isUpperTriangular_of_subsingleton A
  · simp

def HouseholderQR_P (x : SquareUniverse ℝ) : Prop :=
  HasHouseholderQR x.A

noncomputable def qrHouseholderTransformStrong
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    MatDecompFormal.Abstractions.Transformation (Matrix ι ι ℝ) where
  T := { Q : Matrix ι ι ℝ //
    IsOrthogonalMatrix Q ∧ IsHouseholderProduct Q ∧
      IsHouseholderProduct Qᵀ ∧ IsOrthogonalMatrix Qᵀ }
  Goal := QRReady ι
  decGoal := by infer_instance
  apply := fun Q A => Q.1 * A
  find := fun A hA =>
    ⟨qrHeadOrthogonalStep ι A hA,
      ⟨qrHeadOrthogonalStep_isOrthogonal ι A hA,
        (show IsHouseholderProduct (qrHeadOrthogonalStep ι A hA) from
          qrHeadOrthogonalStep_isHouseholderProduct A hA),
        isHouseholderProduct_transpose
          (show IsHouseholderProduct (qrHeadOrthogonalStep ι A hA) from
            qrHeadOrthogonalStep_isHouseholderProduct A hA),
        isOrthogonalMatrix_transpose (qrHeadOrthogonalStep_isOrthogonal ι A hA)⟩⟩
  find_spec := by
    intro A hA
    simpa using qrHeadOrthogonalStep_spec ι A hA

noncomputable def qrHouseholderStrategyCoreStrong : SquareStrategyCore ℝ where
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
      { transform := qrHouseholderTransformStrong ι
        reduction := qrHeadTailSubmatrixReduction ι
        goal_is_sliceable := by
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

theorem householderQRReady_headTailSubmatrixLift
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ)
    (hA : QRReady ι A)
    (hP :
      HasHouseholderQR
        (A.submatrix
          (fun i : QRTailIdx ι => (headTailEquiv (α := ι)).symm (Sum.inr i))
          (fun j : QRTailIdx ι => (headTailEquiv (α := ι)).symm (Sum.inr j)))) :
    HasHouseholderQR A := by
  have hPqr :
      HasQR
        (A.submatrix
          (fun i : QRTailIdx ι => (headTailEquiv (α := ι)).symm (Sum.inr i))
          (fun j : QRTailIdx ι => (headTailEquiv (α := ι)).symm (Sum.inr j))) :=
    hasQR_of_hasHouseholderQR hP
  rcases qrReady_headTailSubmatrixLift A hA hPqr with ⟨⟨Q, R'⟩, hprop, hEq⟩
  rcases hprop with ⟨hQorth, hRtri⟩
  exact ⟨Q, R', isHouseholderProduct_of_isOrthogonalMatrix Q hQorth, hQorth, hRtri, hEq⟩

theorem householderQR_base_univ (x : SquareUniverse ℝ) :
    ((∀ (x_sub : PosSquareUniverse ℝ), (x_sub : SquareUniverse ℝ) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      HouseholderQR_P x := by
  intro hx
  have h_zero : Fintype.card x.ι = 0 :=
    squareSubtypeBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp h_zero
  exact base_householderQR_subsingleton x.A

noncomputable def qr_householder_strategy_proof_strong :
    SquareStrategyProofData ℝ HouseholderQR_P qrHouseholderStrategyCoreStrong where
  transport := by
    intro ι fι dι oι nι A B hBA hP
    rcases hBA with rfl | ⟨t, rfl⟩
    · exact hP
    · rcases t with ⟨H, hH⟩
      exact householder_transport_of_orthogonal_left_of_transpose H A
        hH.2.2.1 hH.1 hH.2.2.2 hP
  lift := by
    intro ι fι dι oι nι A hA hP
    simpa [qrHeadTailSubmatrixReduction, MatDecompFormal.Components.Reductions.SubmatrixMethod] using
      (householderQRReady_headTailSubmatrixLift A hA hP)

noncomputable def qr_householder_strategy_data_strong : SquareStrategyData ℝ HouseholderQR_P :=
  mkSquareStrategyData
    qrHouseholderStrategyCoreStrong
    qr_householder_strategy_proof_strong

noncomputable def qr_householder_framework_inst_strong : SquareSubtypeInductionInstance ℝ :=
  mkSquareSubtypeInductionInstanceFromStrategy
    HouseholderQR_P
    householderQR_base_univ
    qr_householder_strategy_data_strong

/-- Householder-flavored QR existence theorem routed through
a dedicated stronger framework instance.
-/
theorem exists_qr_decomposition_householder [LinearOrder ι] (A : Matrix ι ι ℝ) :
    HasHouseholderQR A := by
  by_cases h_sub : Subsingleton ι
  · exact base_householderQR_subsingleton A
  · exact SquareSubtypeInductionInstance.prove_for_matrix qr_householder_framework_inst_strong A

theorem exists_qr_decomposition_householder_hasQR [LinearOrder ι] (A : Matrix ι ι ℝ) : HasQR A :=
  hasQR_of_hasHouseholderQR (exists_qr_decomposition_householder A)

end MatDecompFormal.Instances
