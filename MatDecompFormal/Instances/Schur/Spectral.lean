import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Basis
import MatDecompFormal.Instances.Normal.Strategy
import MatDecompFormal.Instances.Schur.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open InnerProductSpace
open MatDecompFormal.Framework

/-!
# Algebraic Schur Spectral Step

This file discharges the algebraic one-step Schur oracle.  The first layer is
the field-theoretic eigenvector existence statement over an algebraically closed
field. The remaining layer is arbitrary basis completion with the eigenvector
placed at the distinguished head index, not orthonormal basis completion.
-/

/--
Matrix-level eigenvector data for the Schur head step.

The vector is nonzero and satisfies `A *ᵥ v = eigenvalue • v`.
-/
structure SchurEigenvectorData
    (K ι : Type*) [Field K] [Fintype ι]
    (A : Matrix ι ι K) where
  eigenvalue : K
  vector : ι → K
  vector_ne_zero : vector ≠ 0
  eigen_eq : A *ᵥ vector = eigenvalue • vector

/--
Every square matrix on a nonempty finite index type over an algebraically closed
field has a nonzero eigenvector.
-/
noncomputable def schurEigenvectorData
    {K ι : Type*} [Field K] [IsAlgClosed K]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι K) :
    SchurEigenvectorData K ι A := by
  classical
  haveI : FiniteDimensional K (ι → K) := inferInstance
  haveI : Inhabited ι := Classical.inhabited_of_nonempty inferInstance
  haveI : Nontrivial (ι → K) := Pi.nontrivial
  let hμ_exists :
      ∃ μ : K, Module.End.HasEigenvalue (Matrix.toLin' A) μ :=
    Module.End.exists_eigenvalue
      (V := ι → K)
      (Matrix.toLin' A)
  let μ : K := Classical.choose hμ_exists
  have hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ :=
    Classical.choose_spec hμ_exists
  let hv_exists := hμ.exists_hasEigenvector
  let v : ι → K := Classical.choose hv_exists
  have hv : Module.End.HasEigenvector (Matrix.toLin' A) μ v :=
    Classical.choose_spec hv_exists
  exact
    { eigenvalue := μ
      vector := v
      vector_ne_zero := hv.2
      eigen_eq := by
        simpa [Matrix.toLin'_apply] using hv.apply_eq_smul }

/--
Matrix-level head-column data sufficient for the Schur one-step oracle.

`P A` is an invertible change-of-basis matrix whose head column is an
eigenvector of `A`.
-/
structure SchurHeadColumnData
    (K ι : Type*) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  P : Matrix ι ι K → Matrix ι ι K
  eigenvalue : Matrix ι ι K → K
  invertible_P : ∀ A, InvertibleMatrix (P A)
  head_col_eigen :
    ∀ A,
      A *ᵥ ((P A) *ᵥ (Pi.single (headElem (α := ι)) (1 : K))) =
        eigenvalue A • ((P A) *ᵥ (Pi.single (headElem (α := ι)) (1 : K)))

/--
Extend a nonzero vector to a basis indexed by the original matrix index type,
with that vector placed at the distinguished head index.
-/
noncomputable def schurBasisWithHeadVector
    {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (v : ι → K) (hv : v ≠ 0) :
    { b : Module.Basis ι K (ι → K) // b (headElem (α := ι)) = v } := by
  classical
  let s : Set (ι → K) := {v}
  have hs : LinearIndepOn K id s := by
    simpa [s] using (LinearIndepOn.singleton (R := K) (v := id) hv)
  let b0 : Module.Basis (hs.extend (Set.subset_univ s)) K (ι → K) :=
    Module.Basis.extend hs
  have hv_mem : v ∈ hs.extend (Set.subset_univ s) := by
    exact hs.subset_extend (Set.subset_univ s) (by simp [s])
  let idxV : hs.extend (Set.subset_univ s) := ⟨v, hv_mem⟩
  haveI : Fintype (hs.extend (Set.subset_univ s)) :=
    Module.Basis.fintypeIndexOfRankLtAleph0 b0
      (Module.rank_lt_aleph0 K (ι → K))
  have hcard :
      Fintype.card ι = Fintype.card (hs.extend (Set.subset_univ s)) := by
    rw [← Module.finrank_eq_card_basis b0]
    simp
  let e0 : ι ≃ hs.extend (Set.subset_univ s) := Fintype.equivOfCardEq hcard
  let e : ι ≃ hs.extend (Set.subset_univ s) :=
    e0.trans (Equiv.swap (e0 (headElem (α := ι))) idxV)
  refine ⟨b0.reindex e.symm, ?_⟩
  simp [e, idxV, b0]

/-- Matrix whose columns are a basis, expressed in the standard `Pi.basisFun`. -/
noncomputable def schurBasisMatrix
    {K ι : Type*} [Field K] [Fintype ι]
    (b : Module.Basis ι K (ι → K)) :
    Matrix ι ι K :=
  (Pi.basisFun K ι).toMatrix b

lemma schurBasisMatrix_invertible
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K (ι → K)) :
    InvertibleMatrix (schurBasisMatrix b) := by
  classical
  change IsUnit ((Pi.basisFun K ι).toMatrix b)
  haveI : Invertible ((Pi.basisFun K ι).toMatrix b) :=
    Module.Basis.invertibleToMatrix (Pi.basisFun K ι) b
  exact isUnit_of_invertible _

lemma schurBasisMatrix_mulVec_single
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K (ι → K)) (j : ι) :
    schurBasisMatrix b *ᵥ Pi.single j (1 : K) = b j := by
  classical
  ext i
  simp [schurBasisMatrix, Module.Basis.toMatrix_apply]

/--
Concrete head-column data over an algebraically closed field. The head column is
obtained by extending a nonzero eigenvector to a basis.
-/
noncomputable def schurHeadColumnData
    (K ι : Type u) [Field K] [IsAlgClosed K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    SchurHeadColumnData K ι where
  P := fun A =>
    schurBasisMatrix
      (schurBasisWithHeadVector
        (schurEigenvectorData (K := K) (ι := ι) A).vector
        (schurEigenvectorData (K := K) (ι := ι) A).vector_ne_zero).1
  eigenvalue := fun A => (schurEigenvectorData (K := K) (ι := ι) A).eigenvalue
  invertible_P := fun A =>
    schurBasisMatrix_invertible
      (schurBasisWithHeadVector
        (schurEigenvectorData (K := K) (ι := ι) A).vector
        (schurEigenvectorData (K := K) (ι := ι) A).vector_ne_zero).1
  head_col_eigen := fun A => by
    classical
    let data := schurEigenvectorData (K := K) (ι := ι) A
    let bdata := schurBasisWithHeadVector data.vector data.vector_ne_zero
    have hhead :
        (schurBasisMatrix bdata.1) *ᵥ
            Pi.single (headElem (α := ι)) (1 : K) =
          data.vector := by
      rw [schurBasisMatrix_mulVec_single]
      exact bdata.2
    change
      A *ᵥ
          ((schurBasisMatrix bdata.1) *ᵥ
            Pi.single (headElem (α := ι)) (1 : K)) =
        data.eigenvalue •
          ((schurBasisMatrix bdata.1) *ᵥ
            Pi.single (headElem (α := ι)) (1 : K))
    rw [hhead]
    exact data.eigen_eq

/--
If an invertible change-of-basis matrix has an eigenvector as its head column,
then the corresponding similarity is Schur-ready: the lower-left head-tail block
vanishes.
-/
lemma schurDescentReady_of_head_col_eigen
    {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A P : Matrix ι ι K} {μ : K}
    (hP : InvertibleMatrix P)
    (hEig :
      A *ᵥ (P *ᵥ (Pi.single (headElem (α := ι)) (1 : K))) =
        μ • (P *ᵥ (Pi.single (headElem (α := ι)) (1 : K)))) :
    SchurDescentReady K ι (P⁻¹ * A * P) := by
  classical
  haveI : Invertible P := hP.invertible
  let ehead : ι → K := Pi.single (headElem (α := ι)) (1 : K)
  have hvec : (P⁻¹ * A * P) *ᵥ ehead = μ • ehead := by
    calc
      (P⁻¹ * A * P) *ᵥ ehead = P⁻¹ *ᵥ (A *ᵥ (P *ᵥ ehead)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = P⁻¹ *ᵥ (μ • (P *ᵥ ehead)) := by
        rw [hEig]
      _ = μ • (P⁻¹ *ᵥ (P *ᵥ ehead)) := by
        rw [Matrix.mulVec_smul]
      _ = μ • ((P⁻¹ * P) *ᵥ ehead) := by
        rw [Matrix.mulVec_mulVec]
      _ = μ • ehead := by
        simp [Matrix.inv_mul_of_invertible]
  dsimp [SchurDescentReady]
  ext i j
  cases j
  have hi : (i : ι) ≠ headElem (α := ι) := i.property
  have hentry := congrFun hvec (i : ι)
  simpa [ehead, Matrix.mulVec_single_one, Pi.single_eq_of_ne hi] using hentry

/--
Convert head-column eigenvector data into the exact one-step oracle expected by
the square descent strategy.
-/
noncomputable def schurStepOracleOfHeadColumnData
    {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (data : SchurHeadColumnData K ι) :
    SchurStepOracle K ι where
  P := data.P
  invertible_P := data.invertible_P
  ready := fun A =>
    schurDescentReady_of_head_col_eigen
      (data.invertible_P A)
      (data.head_col_eigen A)

/-- One-step Schur oracle obtained from eigenvectors over an algebraically closed field. -/
noncomputable def schur_step_oracle_of_isAlgClosed
    (K : Type u) [Field K] [IsAlgClosed K] :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      SchurStepOracle K ι :=
  fun {ι} _ _ _ _ =>
    schurStepOracleOfHeadColumnData (schurHeadColumnData K ι)

/-!
## Concrete unitary Schur step

For the complex unitary Schur theorem, the same head-column argument is driven
by an orthonormal basis: choose a nonzero complex eigenvector, normalize it,
extend it to an orthonormal basis with the normalized eigenvector at the head
index, and use the basis matrix as the unitary one-step similarity.
-/

/-- A Schur eigenvector as a vector in complex Euclidean space. -/
noncomputable def unitarySchurEigenvectorVec
    {ι : Type u} [Fintype ι] {A : Matrix ι ι ℂ}
    (data : SchurEigenvectorData ℂ ι A) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 data.vector

lemma unitarySchurEigenvectorVec_ne_zero
    {ι : Type u} [Fintype ι] {A : Matrix ι ι ℂ}
    (data : SchurEigenvectorData ℂ ι A) :
    unitarySchurEigenvectorVec data ≠ 0 := by
  intro hvec
  apply data.vector_ne_zero
  exact (WithLp.toLp_eq_zero 2).mp hvec

/-- Normalized eigenvector used as the head column of the unitary Schur step. -/
noncomputable def normalizedUnitarySchurEigenvector
    {ι : Type u} [Fintype ι] {A : Matrix ι ι ℂ}
    (data : SchurEigenvectorData ℂ ι A) :
    EuclideanSpace ℂ ι :=
  ((‖unitarySchurEigenvectorVec data‖ : ℂ)⁻¹) •
    unitarySchurEigenvectorVec data

lemma normalizedUnitarySchurEigenvector_norm
    {ι : Type u} [Fintype ι] {A : Matrix ι ι ℂ}
    (data : SchurEigenvectorData ℂ ι A) :
    ‖normalizedUnitarySchurEigenvector data‖ = 1 := by
  simpa [normalizedUnitarySchurEigenvector] using
    (norm_smul_inv_norm (unitarySchurEigenvectorVec_ne_zero data))

lemma normalizedUnitarySchurEigenvector_eigen
    {ι : Type u} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (data : SchurEigenvectorData ℂ ι A) :
    A *ᵥ ⇑(normalizedUnitarySchurEigenvector data) =
      data.eigenvalue • ⇑(normalizedUnitarySchurEigenvector data) := by
  classical
  let c : ℂ := ((‖unitarySchurEigenvectorVec data‖ : ℂ)⁻¹)
  have hcoe :
      ⇑(normalizedUnitarySchurEigenvector data) = c • data.vector := by
    ext i
    simp [normalizedUnitarySchurEigenvector, unitarySchurEigenvectorVec, c]
  calc
    A *ᵥ ⇑(normalizedUnitarySchurEigenvector data) =
        A *ᵥ (c • data.vector) := by
          rw [hcoe]
    _ = c • (A *ᵥ data.vector) := by
          rw [Matrix.mulVec_smul]
    _ = c • (data.eigenvalue • data.vector) := by
          rw [data.eigen_eq]
    _ = data.eigenvalue • (c • data.vector) := by
          ext i
          simp [mul_comm, mul_assoc]
    _ = data.eigenvalue • ⇑(normalizedUnitarySchurEigenvector data) := by
          rw [hcoe]

lemma schur_orthonormal_singleton_head_const
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    Orthonormal ℂ
      (({headElem (α := ι)} : Set ι).restrict (fun _ : ι => v)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hi : i.1 = headElem (α := ι) := Set.mem_singleton_iff.mp i.2
  have hj : j.1 = headElem (α := ι) := Set.mem_singleton_iff.mp j.2
  have hij : i = j := by
    apply Subtype.ext
    rw [hi, hj]
  subst hij
  simp [inner_self_eq_norm_sq_to_K, hv]

/--
Extend the normalized Schur eigenvector to an orthonormal basis indexed by the
original matrix index type, with that vector placed at the distinguished head.
-/
noncomputable def unitarySchurBasisWithHeadEigenvector
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} (data : SchurEigenvectorData ℂ ι A) :
    OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι) :=
  Classical.choose
    (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℂ) (E := EuclideanSpace ℂ ι) (ι := ι)
      (card_ι := by simp)
      (s := {headElem (α := ι)})
      (v := fun _ : ι => normalizedUnitarySchurEigenvector data)
      (schur_orthonormal_singleton_head_const
        (normalizedUnitarySchurEigenvector data)
        (normalizedUnitarySchurEigenvector_norm data)))

lemma unitarySchurBasisWithHeadEigenvector_head
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} (data : SchurEigenvectorData ℂ ι A) :
    unitarySchurBasisWithHeadEigenvector data (headElem (α := ι)) =
      normalizedUnitarySchurEigenvector data := by
  classical
  unfold unitarySchurBasisWithHeadEigenvector
  simpa using
    Classical.choose_spec
      (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℂ) (E := EuclideanSpace ℂ ι) (ι := ι)
        (card_ι := by simp)
        (s := {headElem (α := ι)})
        (v := fun _ : ι => normalizedUnitarySchurEigenvector data)
        (schur_orthonormal_singleton_head_const
          (normalizedUnitarySchurEigenvector data)
          (normalizedUnitarySchurEigenvector_norm data)))
      (headElem (α := ι)) (by simp)

/-- Unitary matrix for the concrete one-step Schur similarity. -/
noncomputable def unitarySchurStepQ
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  matrixOfOrthonormalBasis
    (unitarySchurBasisWithHeadEigenvector
      (schurEigenvectorData (K := ℂ) (ι := ι) A))

lemma unitarySchurStepQ_unitary
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) :
    IsUnitaryMatrix (unitarySchurStepQ A) := by
  exact
    matrixOfOrthonormalBasis_unitary
      (unitarySchurBasisWithHeadEigenvector
        (schurEigenvectorData (K := ℂ) (ι := ι) A))

lemma unitarySchurStepQ_head_col_eigen
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) :
    A *ᵥ
        ((unitarySchurStepQ A) *ᵥ
          (Pi.single (headElem (α := ι)) (1 : ℂ))) =
      (schurEigenvectorData (K := ℂ) (ι := ι) A).eigenvalue •
        ((unitarySchurStepQ A) *ᵥ
          (Pi.single (headElem (α := ι)) (1 : ℂ))) := by
  classical
  let data := schurEigenvectorData (K := ℂ) (ι := ι) A
  let b := unitarySchurBasisWithHeadEigenvector data
  have hhead :
      (matrixOfOrthonormalBasis b) *ᵥ
          (Pi.single (headElem (α := ι)) (1 : ℂ)) =
        ⇑(normalizedUnitarySchurEigenvector data) := by
    rw [matrixOfOrthonormalBasis_mulVec_single]
    exact congrArg (fun v : EuclideanSpace ℂ ι => ⇑v)
      (unitarySchurBasisWithHeadEigenvector_head data)
  change
    A *ᵥ
        ((matrixOfOrthonormalBasis b) *ᵥ
          (Pi.single (headElem (α := ι)) (1 : ℂ))) =
      data.eigenvalue •
        ((matrixOfOrthonormalBasis b) *ᵥ
          (Pi.single (headElem (α := ι)) (1 : ℂ)))
  rw [hhead]
  exact normalizedUnitarySchurEigenvector_eigen data

lemma unitarySchurStepQ_ready
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) :
    SchurDescentReady ℂ ι ((unitarySchurStepQ A)ᴴ * A * (unitarySchurStepQ A)) := by
  classical
  let Q := unitarySchurStepQ A
  have hQ : IsUnitaryMatrix Q := unitarySchurStepQ_unitary A
  have hready :
      SchurDescentReady ℂ ι (Q⁻¹ * A * Q) :=
    schurDescentReady_of_head_col_eigen
      (invertibleMatrix_of_isUnitaryMatrix hQ)
      (by
        simpa [Q] using unitarySchurStepQ_head_col_eigen A)
  have hQinv : Q⁻¹ = Qᴴ := by
    apply Matrix.inv_eq_right_inv
    exact hQ.2
  simpa [Q, hQinv] using hready

/-- Concrete one-step unitary Schur oracle over complex matrices. -/
noncomputable def unitarySchurStepOracle :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      UnitarySchurStepOracle ι :=
  fun {_ι} _ _ _ _ =>
    { Q := fun A => unitarySchurStepQ A
      unitary_Q := fun A => unitarySchurStepQ_unitary A
      ready := fun A => unitarySchurStepQ_ready A }

end MatDecompFormal.Instances
