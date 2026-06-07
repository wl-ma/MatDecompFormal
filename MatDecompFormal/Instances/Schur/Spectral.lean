import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Basis
import MatDecompFormal.Instances.Schur.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Schur Spectral Step

This file starts discharging the one-step Schur oracle. The first layer is the
field-theoretic eigenvector existence statement over an algebraically closed
field. The remaining layer is basis completion with the eigenvector placed at
the distinguished head index.
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

end MatDecompFormal.Instances
