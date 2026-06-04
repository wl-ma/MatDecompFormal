import Mathlib.Analysis.Matrix.PosDef
import MatDecompFormal.Instances.Normal.Strategy
import MatDecompFormal.Instances.SVD.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open scoped ComplexOrder

/-!
# SVD Spectral Step

This file starts the concrete spectral construction behind the SVD
`SVDBlockReadyOracle`. The right singular data is extracted from the Hermitian
positive semidefinite matrix `Aᴴ * A`.
-/

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype n] in
/-- The right Gram matrix used in the standard SVD construction. -/
noncomputable def svdRightGram (A : Matrix m n ℂ) : Matrix n n ℂ :=
  Aᴴ * A

omit [Fintype n] in
lemma svdRightGram_isHermitian (A : Matrix m n ℂ) :
    (svdRightGram A).IsHermitian := by
  simpa [svdRightGram] using Matrix.isHermitian_conjTranspose_mul_self A

lemma svdRightGram_posSemidef (A : Matrix m n ℂ) :
    (svdRightGram A).PosSemidef := by
  simpa [svdRightGram] using Matrix.posSemidef_conjTranspose_mul_self A

/-- Eigenvalues of `Aᴴ * A`, indexed by the column type. -/
noncomputable def svdRightEigenvalue [DecidableEq n] (A : Matrix m n ℂ) (j : n) : ℝ :=
  (svdRightGram_isHermitian A).eigenvalues j

lemma svdRightEigenvalue_nonneg [DecidableEq n] (A : Matrix m n ℂ) (j : n) :
    0 ≤ svdRightEigenvalue A j := by
  simpa [svdRightEigenvalue] using (svdRightGram_posSemidef A).eigenvalues_nonneg j

/-- Singular values from the right Gram matrix. -/
noncomputable def svdSingularValue [DecidableEq n] (A : Matrix m n ℂ) (j : n) : ℝ :=
  Real.sqrt (svdRightEigenvalue A j)

lemma svdSingularValue_nonneg [DecidableEq n] (A : Matrix m n ℂ) (j : n) :
    0 ≤ svdSingularValue A j := by
  exact Real.sqrt_nonneg _

/-- The right eigenbasis of `Aᴴ * A`. -/
noncomputable def svdRightBasis [DecidableEq n] (A : Matrix m n ℂ) :
    OrthonormalBasis n ℂ (EuclideanSpace ℂ n) :=
  (svdRightGram_isHermitian A).eigenvectorBasis

/-- The right unitary matrix whose columns are the right singular vectors. -/
noncomputable def svdRightUnitary [DecidableEq n] (A : Matrix m n ℂ) :
    Matrix n n ℂ :=
  (svdRightGram_isHermitian A).eigenvectorUnitary

lemma svdRightUnitary_unitary [DecidableEq n] (A : Matrix m n ℂ) :
    IsUnitaryMatrix (svdRightUnitary A) := by
  constructor
  · simpa [svdRightUnitary] using
      (show ((svdRightGram_isHermitian A).eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          ((svdRightGram_isHermitian A).eigenvectorUnitary : Matrix n n ℂ) = 1 by
        exact Unitary.coe_star_mul_self _)
  · simpa [svdRightUnitary] using
      (show ((svdRightGram_isHermitian A).eigenvectorUnitary : Matrix n n ℂ) *
          ((svdRightGram_isHermitian A).eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 by
        exact Unitary.coe_mul_star_self _)

lemma svdRightGram_mulVec_rightBasis [DecidableEq n] (A : Matrix m n ℂ) (j : n) :
    (svdRightGram A) *ᵥ ⇑(svdRightBasis A j) =
      (svdRightEigenvalue A j : ℂ) • ⇑(svdRightBasis A j) := by
  simpa [svdRightBasis, svdRightEigenvalue] using
    (svdRightGram_isHermitian A).mulVec_eigenvectorBasis j

lemma image_star_dotProduct_image_eq_gram
    (A : Matrix m n ℂ) (v w : n → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (A *ᵥ w) =
      star v ⬝ᵥ ((svdRightGram A) *ᵥ w) := by
  calc
    star (A *ᵥ v) ⬝ᵥ (A *ᵥ w)
        = (star (A *ᵥ v) ᵥ* A) ⬝ᵥ w := by
      rw [Matrix.dotProduct_mulVec]
    _ = ((star v ᵥ* Aᴴ) ᵥ* A) ⬝ᵥ w := by
      have h : star (A *ᵥ v) = star v ᵥ* Aᴴ := by
        simpa using (Matrix.vecMul_conjTranspose A (star v)).symm
      rw [h]
    _ = (star v ᵥ* (Aᴴ * A)) ⬝ᵥ w := by
      rw [Matrix.vecMul_vecMul]
    _ = star v ⬝ᵥ ((svdRightGram A) *ᵥ w) := by
      rw [Matrix.dotProduct_mulVec]
      simp [svdRightGram]

lemma svdRightBasis_image_star_dotProduct_image [DecidableEq n]
    (A : Matrix m n ℂ) (i j : n) :
    star (A *ᵥ ⇑(svdRightBasis A i)) ⬝ᵥ
        (A *ᵥ ⇑(svdRightBasis A j)) =
      (svdRightEigenvalue A j : ℂ) *
        (star ⇑(svdRightBasis A i) ⬝ᵥ ⇑(svdRightBasis A j)) := by
  rw [image_star_dotProduct_image_eq_gram]
  rw [svdRightGram_mulVec_rightBasis]
  simp [dotProduct_smul]

lemma star_dotProduct_orthonormalBasis_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (i j : ι) :
    star ⇑(b i) ⬝ᵥ ⇑(b j) = if i = j then 1 else 0 := by
  rw [← OrthonormalBasis.inner_eq_ite b i j]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  exact (dotProduct_comm _ _).symm

lemma svdRightBasis_star_dotProduct [DecidableEq n]
    (A : Matrix m n ℂ) (i j : n) :
    star ⇑(svdRightBasis A i) ⬝ᵥ ⇑(svdRightBasis A j) =
      if i = j then 1 else 0 := by
  exact star_dotProduct_orthonormalBasis_apply (svdRightBasis A) i j

lemma svdRightBasis_image_star_dotProduct_image_of_ne [DecidableEq n]
    (A : Matrix m n ℂ) {i j : n} (hij : i ≠ j) :
    star (A *ᵥ ⇑(svdRightBasis A i)) ⬝ᵥ
        (A *ᵥ ⇑(svdRightBasis A j)) = 0 := by
  rw [svdRightBasis_image_star_dotProduct_image]
  simp [svdRightBasis_star_dotProduct, hij]

lemma svdRightBasis_image_star_dotProduct_image_self [DecidableEq n]
    (A : Matrix m n ℂ) (j : n) :
    star (A *ᵥ ⇑(svdRightBasis A j)) ⬝ᵥ
        (A *ᵥ ⇑(svdRightBasis A j)) =
      (svdRightEigenvalue A j : ℂ) := by
  rw [svdRightBasis_image_star_dotProduct_image]
  simp [svdRightBasis_star_dotProduct]

lemma svdSingularValue_sq [DecidableEq n] (A : Matrix m n ℂ) (j : n) :
    (svdSingularValue A j) ^ 2 = svdRightEigenvalue A j := by
  exact Real.sq_sqrt (svdRightEigenvalue_nonneg A j)

lemma svdSingularValue_mul_self_complex [DecidableEq n] (A : Matrix m n ℂ) (j : n) :
    (svdSingularValue A j : ℂ) * (svdSingularValue A j : ℂ) =
      (svdRightEigenvalue A j : ℂ) := by
  rw [← Complex.ofReal_mul, ← sq]
  exact congrArg (fun x : ℝ => (x : ℂ)) (svdSingularValue_sq A j)

lemma svdRightBasis_image_ne_zero_of_pos_eigenvalue [DecidableEq n]
    (A : Matrix m n ℂ) (j : n) (hpos : 0 < svdRightEigenvalue A j) :
    A *ᵥ ⇑(svdRightBasis A j) ≠ 0 := by
  intro hzero
  have hdot :
      star (A *ᵥ ⇑(svdRightBasis A j)) ⬝ᵥ
          (A *ᵥ ⇑(svdRightBasis A j)) = 0 := by
    simp [hzero]
  have hzero_eigen : (svdRightEigenvalue A j : ℂ) = 0 := by
    rw [← svdRightBasis_image_star_dotProduct_image_self A j]
    exact hdot
  exact hpos.ne' (Complex.ofReal_inj.mp hzero_eigen)

noncomputable def svdLeftHeadVectorOfPositive [DecidableEq n]
    (A : Matrix m n ℂ) (j : n) : EuclideanSpace ℂ m :=
  WithLp.toLp 2 (((svdSingularValue A j : ℂ)⁻¹) •
    (A *ᵥ ⇑(svdRightBasis A j)))

lemma svdLeftHeadVectorOfPositive_apply [DecidableEq n]
    (A : Matrix m n ℂ) (j : n) :
    ⇑(svdLeftHeadVectorOfPositive A j) =
      ((svdSingularValue A j : ℂ)⁻¹) •
        (A *ᵥ ⇑(svdRightBasis A j)) := by
  rfl

lemma svdLeftHeadVectorOfPositive_star_dotProduct_self [DecidableEq n]
    (A : Matrix m n ℂ) (j : n) (hpos : 0 < svdRightEigenvalue A j) :
    star ⇑(svdLeftHeadVectorOfPositive A j) ⬝ᵥ
        ⇑(svdLeftHeadVectorOfPositive A j) = 1 := by
  let σ : ℝ := svdSingularValue A j
  let σc : ℂ := (σ : ℂ)
  let x : m → ℂ := A *ᵥ ⇑(svdRightBasis A j)
  have hσpos : 0 < σ := by
    dsimp [σ, svdSingularValue]
    exact Real.sqrt_pos.2 hpos
  have hσc_ne : σc ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hσpos.ne'
  have hx : star x ⬝ᵥ x = σc * σc := by
    dsimp [x, σc, σ]
    rw [svdRightBasis_image_star_dotProduct_image_self]
    exact (svdSingularValue_mul_self_complex A j).symm
  have hstar : star (σc⁻¹ • x) = σc⁻¹ • star x := by
    ext i
    simp [σc]
  calc
    star ⇑(svdLeftHeadVectorOfPositive A j) ⬝ᵥ
        ⇑(svdLeftHeadVectorOfPositive A j)
        = star (σc⁻¹ • x) ⬝ᵥ (σc⁻¹ • x) := by
      rfl
    _ = σc⁻¹ * (σc⁻¹ * (star x ⬝ᵥ x)) := by
      rw [hstar]
      simp [smul_eq_mul]
    _ = 1 := by
      rw [hx]
      field_simp [hσc_ne]

lemma svdRightBasis_image_eq_singularValue_smul_leftHead [DecidableEq n]
    (A : Matrix m n ℂ) (j : n) (hpos : 0 < svdRightEigenvalue A j) :
    A *ᵥ ⇑(svdRightBasis A j) =
      (svdSingularValue A j : ℂ) • ⇑(svdLeftHeadVectorOfPositive A j) := by
  let σ : ℝ := svdSingularValue A j
  let σc : ℂ := (σ : ℂ)
  let x : m → ℂ := A *ᵥ ⇑(svdRightBasis A j)
  have hσpos : 0 < σ := by
    dsimp [σ, svdSingularValue]
    exact Real.sqrt_pos.2 hpos
  have hσc_ne : σc ≠ 0 := Complex.ofReal_ne_zero.mpr hσpos.ne'
  calc
    A *ᵥ ⇑(svdRightBasis A j) = x := rfl
    _ = σc • (σc⁻¹ • x) := by
      ext i
      simp [σc, hσc_ne, smul_eq_mul]
    _ = (svdSingularValue A j : ℂ) • ⇑(svdLeftHeadVectorOfPositive A j) := by
      rfl

lemma svdLeftHeadVectorOfPositive_head_row_zero [DecidableEq n]
    (A : Matrix m n ℂ) (i j : n) (hij : i ≠ j) :
    star ⇑(svdLeftHeadVectorOfPositive A i) ⬝ᵥ
        (A *ᵥ ⇑(svdRightBasis A j)) = 0 := by
  let σ : ℝ := svdSingularValue A i
  let σc : ℂ := (σ : ℂ)
  let xi : m → ℂ := A *ᵥ ⇑(svdRightBasis A i)
  have hstar : star ⇑(svdLeftHeadVectorOfPositive A i) = σc⁻¹ • star xi := by
    ext k
    simp [svdLeftHeadVectorOfPositive, xi, σc, σ]
  calc
    star ⇑(svdLeftHeadVectorOfPositive A i) ⬝ᵥ
        (A *ᵥ ⇑(svdRightBasis A j))
        = σc⁻¹ * (star xi ⬝ᵥ (A *ᵥ ⇑(svdRightBasis A j))) := by
      rw [hstar]
      simp [smul_eq_mul]
    _ = 0 := by
      rw [svdRightBasis_image_star_dotProduct_image_of_ne A hij]
      simp

lemma svdLeftHeadVectorOfPositive_head_entry [DecidableEq n]
    (A : Matrix m n ℂ) (j : n) (hpos : 0 < svdRightEigenvalue A j) :
    star ⇑(svdLeftHeadVectorOfPositive A j) ⬝ᵥ
        (A *ᵥ ⇑(svdRightBasis A j)) =
      (svdSingularValue A j : ℂ) := by
  rw [svdRightBasis_image_eq_singularValue_smul_leftHead A j hpos]
  rw [dotProduct_smul]
  rw [svdLeftHeadVectorOfPositive_star_dotProduct_self A j hpos]
  simp

lemma star_dotProduct_mulVec_eq_entry
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (u : m → ℂ) (v : n → ℂ) :
    star u ⬝ᵥ (A *ᵥ v) = ∑ x, (star u x) * ∑ y, A x y * v y := by
  rfl

/--
Basis-level one-step SVD data. It is intentionally phrased in vector terms:
the first right basis vector is sent by `A` to `σ` times the first left basis
vector, all other right basis vectors have zero component along the first left
basis vector, and all other left basis vectors have zero component along the
first image vector.
-/
structure SVDHeadBasisData
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  leftBasis : (A : Matrix m n ℂ) → OrthonormalBasis m ℂ (EuclideanSpace ℂ m)
  rightBasis : (A : Matrix m n ℂ) → OrthonormalBasis n ℂ (EuclideanSpace ℂ n)
  sigma : Matrix m n ℂ → ℝ
  sigma_nonneg : ∀ A, 0 ≤ sigma A
  head_image :
    ∀ A,
      A *ᵥ ⇑(rightBasis A (headElem (α := n))) =
        (sigma A : ℂ) • ⇑(leftBasis A (headElem (α := m)))
  head_entry :
    ∀ A,
      star ⇑(leftBasis A (headElem (α := m))) ⬝ᵥ
        (A *ᵥ ⇑(rightBasis A (headElem (α := n)))) = (sigma A : ℂ)
  head_row_zero :
    ∀ A (j : n), j ≠ headElem (α := n) →
      star ⇑(leftBasis A (headElem (α := m))) ⬝ᵥ
        (A *ᵥ ⇑(rightBasis A j)) = 0
  head_col_zero :
    ∀ A (i : m), i ≠ headElem (α := m) →
      star ⇑(leftBasis A i) ⬝ᵥ
        (A *ᵥ ⇑(rightBasis A (headElem (α := n)))) = 0

noncomputable def SVDHeadBasisData.leftUnitary
    {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (data : SVDHeadBasisData m n) (A : Matrix m n ℂ) : Matrix m m ℂ :=
  matrixOfOrthonormalBasis (data.leftBasis A)

noncomputable def SVDHeadBasisData.rightUnitary
    {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (data : SVDHeadBasisData m n) (A : Matrix m n ℂ) : Matrix n n ℂ :=
  matrixOfOrthonormalBasis (data.rightBasis A)

@[simp] lemma matrixOfOrthonormalBasis_apply
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (i j : ι) :
    matrixOfOrthonormalBasis b i j = ⇑(b j) i := rfl

lemma svdHeadBasisData_entry
    {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (data : SVDHeadBasisData m n) (A : Matrix m n ℂ) (i : m) (j : n) :
    ((data.leftUnitary A)ᴴ * A * (data.rightUnitary A)) i j =
      star ⇑(data.leftBasis A i) ⬝ᵥ (A *ᵥ ⇑(data.rightBasis A j)) := by
  rw [star_dotProduct_mulVec_eq_entry]
  simp [SVDHeadBasisData.leftUnitary, SVDHeadBasisData.rightUnitary,
    Matrix.mul_apply, Matrix.conjTranspose, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/--
The remaining concrete singular-vector data for one SVD descent step.

The right Gram spectral data above constructs the right singular vectors and
nonnegative candidate singular values. This structure isolates the standard
left-vector completion step: choose left and right unitary bases that put a
chosen singular pair in head position and prove the transformed matrix is
block-ready.
-/
structure SVDHeadSingularVectorData
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  U : Matrix m n ℂ → Matrix m m ℂ
  V : Matrix m n ℂ → Matrix n n ℂ
  sigma : Matrix m n ℂ → ℝ
  sigma_nonneg : ∀ A, 0 ≤ sigma A
  unitary_U : ∀ A, IsUnitaryMatrix (U A)
  unitary_V : ∀ A, IsUnitaryMatrix (V A)
  head_block :
    ∀ A,
      let B := Matrix.reindex (headTailEquiv (α := m)) (headTailEquiv (α := n))
        ((U A)ᴴ * A * (V A))
      B.toBlocks₁₁ = (fun _ _ : Unit => (sigma A : ℂ)) ∧
        B.toBlocks₁₂ = 0 ∧ B.toBlocks₂₁ = 0

noncomputable def svdBlockReadyOracleOfHeadSingularVectorData
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (data : SVDHeadSingularVectorData m n) :
    SVDBlockReadyOracle m n where
  U := data.U
  V := data.V
  unitary_U := data.unitary_U
  unitary_V := data.unitary_V
  blockReady := by
    intro A
    rcases data.head_block A with ⟨h11, h12, h21⟩
    exact ⟨data.sigma A, data.sigma_nonneg A, h11, h12, h21⟩

noncomputable def svdHeadSingularVectorDataOfHeadBasisData
    (m n : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (data : SVDHeadBasisData m n) :
    SVDHeadSingularVectorData m n where
  U := data.leftUnitary
  V := data.rightUnitary
  sigma := data.sigma
  sigma_nonneg := data.sigma_nonneg
  unitary_U := fun A => matrixOfOrthonormalBasis_unitary (data.leftBasis A)
  unitary_V := fun A => matrixOfOrthonormalBasis_unitary (data.rightBasis A)
  head_block := by
    intro A
    let B := Matrix.reindex (headTailEquiv (α := m)) (headTailEquiv (α := n))
      ((data.leftUnitary A)ᴴ * A * (data.rightUnitary A))
    constructor
    · ext i j
      change
        ((data.leftUnitary A)ᴴ * A * (data.rightUnitary A))
            (headElem (α := m)) (headElem (α := n)) = (data.sigma A : ℂ)
      rw [svdHeadBasisData_entry data A]
      exact data.head_entry A
    · constructor
      · ext i j
        change
          ((data.leftUnitary A)ᴴ * A * (data.rightUnitary A))
              (headElem (α := m)) (j : n) = 0
        rw [svdHeadBasisData_entry data A]
        exact data.head_row_zero A _ j.2
      · ext i j
        change
          ((data.leftUnitary A)ᴴ * A * (data.rightUnitary A))
              (i : m) (headElem (α := n)) = 0
        rw [svdHeadBasisData_entry data A]
        exact data.head_col_zero A _ i.2

end MatDecompFormal.Instances
