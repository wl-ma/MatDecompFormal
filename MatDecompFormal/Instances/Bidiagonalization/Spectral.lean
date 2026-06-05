import MatDecompFormal.Instances.Bidiagonalization.Existence
import MatDecompFormal.Instances.SVD.Spectral

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Bidiagonalization Spectral One-Step Bridge

This file supplies a concrete complex one-step oracle for the current
block-ready bidiagonalization template by reusing the existing SVD head
block-ready construction. The final theorem is still assembled through
`exists_unitary_bidiagonalization_oracle`, hence through the rectangular
descent framework.
-/

/--
The SVD head block-ready oracle is stronger than the current
bidiagonalization readiness invariant.
-/
noncomputable def bidiagonalizationStepOracleOfSVDBlockReady
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (oracle : SVDBlockReadyOracle m n) :
    BidiagonalizationStepOracle ℂ m n where
  U := oracle.U
  V := oracle.V
  unitary_U := oracle.unitary_U
  unitary_V := oracle.unitary_V
  ready := by
    intro A
    rcases oracle.blockReady A with ⟨_σ, _hσ, _h11, h12, h21⟩
    exact ⟨by
      intro i
      simpa [BidiagonalizationReady] using congrFun (congrFun h21 i) (),
      by
        intro j
        simpa [BidiagonalizationReady] using congrFun (congrFun h12 ()) j⟩

/-- Concrete complex one-step oracle obtained from the existing SVD spectral step. -/
noncomputable def bidiagonalizationStepOracle
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    BidiagonalizationStepOracle ℂ m n :=
  bidiagonalizationStepOracleOfSVDBlockReady
    (svdBlockReadyOracleOfHeadSingularVectorData m n
      (svdHeadSingularVectorDataOfHeadBasisData m n (svdHeadBasisData m n)))

/--
Unconditional complex unitary bidiagonalization, routed through the
bidiagonalization rectangular descent framework.
-/
theorem exists_unitary_bidiagonalization
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasUnitaryBidiagonalization A := by
  exact exists_unitary_bidiagonalization_oracle
    (fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        bidiagonalizationStepOracle (m := p) (n := q))
    A

section RealSpectral

variable {m n : Type u} [Fintype m] [Fintype n]

omit [Fintype n] in
/-- Real right Gram matrix for the block-ready bidiagonalization step. -/
noncomputable def realBidiagonalizationRightGram (A : Matrix m n ℝ) : Matrix n n ℝ :=
  Aᴴ * A

omit [Fintype n] in
lemma realBidiagonalizationRightGram_isHermitian (A : Matrix m n ℝ) :
    (realBidiagonalizationRightGram A).IsHermitian := by
  simpa [realBidiagonalizationRightGram] using Matrix.isHermitian_conjTranspose_mul_self A

lemma realBidiagonalizationRightGram_posSemidef (A : Matrix m n ℝ) :
    (realBidiagonalizationRightGram A).PosSemidef := by
  simpa [realBidiagonalizationRightGram] using Matrix.posSemidef_conjTranspose_mul_self A

/-- Eigenvalues of the real right Gram matrix. -/
noncomputable def realBidiagonalizationRightEigenvalue [DecidableEq n]
    (A : Matrix m n ℝ) (j : n) : ℝ :=
  (realBidiagonalizationRightGram_isHermitian A).eigenvalues j

lemma realBidiagonalizationRightEigenvalue_nonneg [DecidableEq n]
    (A : Matrix m n ℝ) (j : n) :
    0 ≤ realBidiagonalizationRightEigenvalue A j := by
  simpa [realBidiagonalizationRightEigenvalue] using
    (realBidiagonalizationRightGram_posSemidef A).eigenvalues_nonneg j

/-- Real singular values from the right Gram matrix. -/
noncomputable def realBidiagonalizationSingularValue [DecidableEq n]
    (A : Matrix m n ℝ) (j : n) : ℝ :=
  Real.sqrt (realBidiagonalizationRightEigenvalue A j)

lemma realBidiagonalizationSingularValue_nonneg [DecidableEq n]
    (A : Matrix m n ℝ) (j : n) :
    0 ≤ realBidiagonalizationSingularValue A j := by
  exact Real.sqrt_nonneg _

/-- Right real singular-vector basis for the one-step oracle. -/
noncomputable def realBidiagonalizationRightBasis [DecidableEq n]
    (A : Matrix m n ℝ) :
    OrthonormalBasis n ℝ (EuclideanSpace ℝ n) :=
  (realBidiagonalizationRightGram_isHermitian A).eigenvectorBasis

lemma realBidiagonalizationRightGram_mulVec_rightBasis [DecidableEq n]
    (A : Matrix m n ℝ) (j : n) :
    (realBidiagonalizationRightGram A) *ᵥ ⇑(realBidiagonalizationRightBasis A j) =
      realBidiagonalizationRightEigenvalue A j •
        ⇑(realBidiagonalizationRightBasis A j) := by
  simpa [realBidiagonalizationRightBasis, realBidiagonalizationRightEigenvalue] using
    (realBidiagonalizationRightGram_isHermitian A).mulVec_eigenvectorBasis j

lemma real_image_dotProduct_image_eq_gram
    (A : Matrix m n ℝ) (v w : n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ w) =
      v ⬝ᵥ ((realBidiagonalizationRightGram A) *ᵥ w) := by
  calc
    (A *ᵥ v) ⬝ᵥ (A *ᵥ w)
        = ((A *ᵥ v) ᵥ* A) ⬝ᵥ w := by
      rw [Matrix.dotProduct_mulVec]
    _ = ((v ᵥ* Aᴴ) ᵥ* A) ⬝ᵥ w := by
      have h : A *ᵥ v = v ᵥ* Aᴴ := by
        simpa using (Matrix.vecMul_conjTranspose A v).symm
      rw [h]
    _ = (v ᵥ* (Aᴴ * A)) ⬝ᵥ w := by
      rw [Matrix.vecMul_vecMul]
    _ = v ⬝ᵥ ((realBidiagonalizationRightGram A) *ᵥ w) := by
      rw [Matrix.dotProduct_mulVec]
      simp [realBidiagonalizationRightGram]

lemma realBidiagonalizationRightBasis_image_dotProduct_image [DecidableEq n]
    (A : Matrix m n ℝ) (i j : n) :
    (A *ᵥ ⇑(realBidiagonalizationRightBasis A i)) ⬝ᵥ
        (A *ᵥ ⇑(realBidiagonalizationRightBasis A j)) =
      realBidiagonalizationRightEigenvalue A j *
        (⇑(realBidiagonalizationRightBasis A i) ⬝ᵥ
          ⇑(realBidiagonalizationRightBasis A j)) := by
  rw [real_image_dotProduct_image_eq_gram]
  rw [realBidiagonalizationRightGram_mulVec_rightBasis]
  simp [dotProduct_smul]

lemma dotProduct_orthonormalBasis_apply_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (i j : ι) :
    ⇑(b i) ⬝ᵥ ⇑(b j) = if i = j then 1 else 0 := by
  rw [← OrthonormalBasis.inner_eq_ite b i j]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  exact (dotProduct_comm _ _).symm

lemma realBidiagonalizationRightBasis_dotProduct [DecidableEq n]
    (A : Matrix m n ℝ) (i j : n) :
    ⇑(realBidiagonalizationRightBasis A i) ⬝ᵥ
        ⇑(realBidiagonalizationRightBasis A j) =
      if i = j then 1 else 0 := by
  exact dotProduct_orthonormalBasis_apply_real (realBidiagonalizationRightBasis A) i j

lemma realBidiagonalizationRightBasis_image_dotProduct_image_of_ne [DecidableEq n]
    (A : Matrix m n ℝ) {i j : n} (hij : i ≠ j) :
    (A *ᵥ ⇑(realBidiagonalizationRightBasis A i)) ⬝ᵥ
        (A *ᵥ ⇑(realBidiagonalizationRightBasis A j)) = 0 := by
  rw [realBidiagonalizationRightBasis_image_dotProduct_image]
  simp [realBidiagonalizationRightBasis_dotProduct, hij]

lemma realBidiagonalizationRightBasis_image_dotProduct_image_self [DecidableEq n]
    (A : Matrix m n ℝ) (j : n) :
    (A *ᵥ ⇑(realBidiagonalizationRightBasis A j)) ⬝ᵥ
        (A *ᵥ ⇑(realBidiagonalizationRightBasis A j)) =
      realBidiagonalizationRightEigenvalue A j := by
  rw [realBidiagonalizationRightBasis_image_dotProduct_image]
  simp [realBidiagonalizationRightBasis_dotProduct]

lemma realBidiagonalizationSingularValue_sq [DecidableEq n]
    (A : Matrix m n ℝ) (j : n) :
    (realBidiagonalizationSingularValue A j) ^ 2 =
      realBidiagonalizationRightEigenvalue A j := by
  exact Real.sq_sqrt (realBidiagonalizationRightEigenvalue_nonneg A j)

lemma realBidiagonalizationRightBasis_image_ne_zero_of_pos_eigenvalue [DecidableEq n]
    (A : Matrix m n ℝ) (j : n)
    (hpos : 0 < realBidiagonalizationRightEigenvalue A j) :
    A *ᵥ ⇑(realBidiagonalizationRightBasis A j) ≠ 0 := by
  intro hzero
  have hdot :
      (A *ᵥ ⇑(realBidiagonalizationRightBasis A j)) ⬝ᵥ
          (A *ᵥ ⇑(realBidiagonalizationRightBasis A j)) = 0 := by
    simp [hzero]
  have hzero_eigen : realBidiagonalizationRightEigenvalue A j = 0 := by
    rw [← realBidiagonalizationRightBasis_image_dotProduct_image_self A j]
    exact hdot
  exact hpos.ne' hzero_eigen

noncomputable def realBidiagonalizationLeftHeadVectorOfPositive [DecidableEq n]
    (A : Matrix m n ℝ) (j : n) : EuclideanSpace ℝ m :=
  WithLp.toLp 2 ((realBidiagonalizationSingularValue A j)⁻¹ •
    (A *ᵥ ⇑(realBidiagonalizationRightBasis A j)))

lemma realBidiagonalizationLeftHeadVectorOfPositive_apply [DecidableEq n]
    (A : Matrix m n ℝ) (j : n) :
    ⇑(realBidiagonalizationLeftHeadVectorOfPositive A j) =
      (realBidiagonalizationSingularValue A j)⁻¹ •
        (A *ᵥ ⇑(realBidiagonalizationRightBasis A j)) := by
  rfl

lemma realBidiagonalizationLeftHeadVectorOfPositive_dotProduct_self [DecidableEq n]
    (A : Matrix m n ℝ) (j : n)
    (hpos : 0 < realBidiagonalizationRightEigenvalue A j) :
    ⇑(realBidiagonalizationLeftHeadVectorOfPositive A j) ⬝ᵥ
        ⇑(realBidiagonalizationLeftHeadVectorOfPositive A j) = 1 := by
  let σ : ℝ := realBidiagonalizationSingularValue A j
  let x : m → ℝ := A *ᵥ ⇑(realBidiagonalizationRightBasis A j)
  have hσpos : 0 < σ := by
    dsimp [σ, realBidiagonalizationSingularValue]
    exact Real.sqrt_pos.2 hpos
  have hσ_ne : σ ≠ 0 := hσpos.ne'
  have hx : x ⬝ᵥ x = σ * σ := by
    dsimp [x, σ]
    rw [realBidiagonalizationRightBasis_image_dotProduct_image_self]
    rw [← realBidiagonalizationSingularValue_sq]
    ring
  calc
    ⇑(realBidiagonalizationLeftHeadVectorOfPositive A j) ⬝ᵥ
        ⇑(realBidiagonalizationLeftHeadVectorOfPositive A j)
        = (σ⁻¹ • x) ⬝ᵥ (σ⁻¹ • x) := by
      rfl
    _ = σ⁻¹ * (σ⁻¹ * (x ⬝ᵥ x)) := by
      simp [smul_eq_mul]
    _ = 1 := by
      rw [hx]
      field_simp [hσ_ne]

lemma realBidiagonalizationRightBasis_image_eq_singularValue_smul_leftHead [DecidableEq n]
    (A : Matrix m n ℝ) (j : n)
    (hpos : 0 < realBidiagonalizationRightEigenvalue A j) :
    A *ᵥ ⇑(realBidiagonalizationRightBasis A j) =
      realBidiagonalizationSingularValue A j •
        ⇑(realBidiagonalizationLeftHeadVectorOfPositive A j) := by
  let σ : ℝ := realBidiagonalizationSingularValue A j
  let x : m → ℝ := A *ᵥ ⇑(realBidiagonalizationRightBasis A j)
  have hσpos : 0 < σ := by
    dsimp [σ, realBidiagonalizationSingularValue]
    exact Real.sqrt_pos.2 hpos
  have hσ_ne : σ ≠ 0 := hσpos.ne'
  calc
    A *ᵥ ⇑(realBidiagonalizationRightBasis A j) = x := rfl
    _ = σ • (σ⁻¹ • x) := by
      ext i
      simp [hσ_ne, smul_eq_mul]
    _ = realBidiagonalizationSingularValue A j •
          ⇑(realBidiagonalizationLeftHeadVectorOfPositive A j) := by
      rfl

lemma realBidiagonalizationLeftHeadVectorOfPositive_head_row_zero [DecidableEq n]
    (A : Matrix m n ℝ) (i j : n) (hij : i ≠ j) :
    ⇑(realBidiagonalizationLeftHeadVectorOfPositive A i) ⬝ᵥ
        (A *ᵥ ⇑(realBidiagonalizationRightBasis A j)) = 0 := by
  let σ : ℝ := realBidiagonalizationSingularValue A i
  let xi : m → ℝ := A *ᵥ ⇑(realBidiagonalizationRightBasis A i)
  calc
    ⇑(realBidiagonalizationLeftHeadVectorOfPositive A i) ⬝ᵥ
        (A *ᵥ ⇑(realBidiagonalizationRightBasis A j))
        = σ⁻¹ * (xi ⬝ᵥ (A *ᵥ ⇑(realBidiagonalizationRightBasis A j))) := by
      simp [realBidiagonalizationLeftHeadVectorOfPositive, xi, σ, smul_eq_mul]
    _ = 0 := by
      rw [realBidiagonalizationRightBasis_image_dotProduct_image_of_ne A hij]
      simp

lemma realBidiagonalizationLeftHeadVectorOfPositive_head_entry [DecidableEq n]
    (A : Matrix m n ℝ) (j : n)
    (hpos : 0 < realBidiagonalizationRightEigenvalue A j) :
    ⇑(realBidiagonalizationLeftHeadVectorOfPositive A j) ⬝ᵥ
        (A *ᵥ ⇑(realBidiagonalizationRightBasis A j)) =
      realBidiagonalizationSingularValue A j := by
  rw [realBidiagonalizationRightBasis_image_eq_singularValue_smul_leftHead A j hpos]
  rw [dotProduct_smul]
  rw [realBidiagonalizationLeftHeadVectorOfPositive_dotProduct_self A j hpos]
  simp

lemma realBidiagonalizationLeftBasis_head_col_zero_of_head_eq_positive
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (leftHead : m) (rightHead : n)
    (b : OrthonormalBasis m ℝ (EuclideanSpace ℝ m))
    (hhead : b leftHead = realBidiagonalizationLeftHeadVectorOfPositive A rightHead)
    (hpos : 0 < realBidiagonalizationRightEigenvalue A rightHead)
    (i : m) (hi : i ≠ leftHead) :
    ⇑(b i) ⬝ᵥ (A *ᵥ ⇑(realBidiagonalizationRightBasis A rightHead)) = 0 := by
  calc
    ⇑(b i) ⬝ᵥ (A *ᵥ ⇑(realBidiagonalizationRightBasis A rightHead))
        = ⇑(b i) ⬝ᵥ
            (realBidiagonalizationSingularValue A rightHead •
              ⇑(realBidiagonalizationLeftHeadVectorOfPositive A rightHead)) := by
      rw [realBidiagonalizationRightBasis_image_eq_singularValue_smul_leftHead
        A rightHead hpos]
    _ = realBidiagonalizationSingularValue A rightHead *
          (⇑(b i) ⬝ᵥ
            ⇑(realBidiagonalizationLeftHeadVectorOfPositive A rightHead)) := by
      simp
    _ = realBidiagonalizationSingularValue A rightHead *
          (⇑(b i) ⬝ᵥ ⇑(b leftHead)) := by
      rw [← hhead]
    _ = 0 := by
      rw [dotProduct_orthonormalBasis_apply_real]
      simp [hi]

lemma realBidiagonalizationLeftHeadVectorOfPositive_singleton_orthonormal
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (leftHead : m) (rightHead : n)
    (hpos : 0 < realBidiagonalizationRightEigenvalue A rightHead) :
    Orthonormal ℝ
      (({leftHead} : Set m).restrict
        (fun _ : m => realBidiagonalizationLeftHeadVectorOfPositive A rightHead)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hij : i = j := Subtype.ext (i.2.trans j.2.symm)
  rw [if_pos hij]
  change
    inner ℝ (realBidiagonalizationLeftHeadVectorOfPositive A rightHead)
      (realBidiagonalizationLeftHeadVectorOfPositive A rightHead) = 1
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]
  exact realBidiagonalizationLeftHeadVectorOfPositive_dotProduct_self A rightHead hpos

noncomputable def realBidiagonalizationLeftBasisOfPositive
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (leftHead : m) (rightHead : n)
    (hpos : 0 < realBidiagonalizationRightEigenvalue A rightHead) :
    OrthonormalBasis m ℝ (EuclideanSpace ℝ m) :=
  Classical.choose
    (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := EuclideanSpace ℝ m) (ι := m)
      (by simp)
      (v := fun _ : m => realBidiagonalizationLeftHeadVectorOfPositive A rightHead)
      (s := {leftHead})
      (realBidiagonalizationLeftHeadVectorOfPositive_singleton_orthonormal
        A leftHead rightHead hpos))

lemma realBidiagonalizationLeftBasisOfPositive_head
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (leftHead : m) (rightHead : n)
    (hpos : 0 < realBidiagonalizationRightEigenvalue A rightHead) :
    realBidiagonalizationLeftBasisOfPositive A leftHead rightHead hpos leftHead =
      realBidiagonalizationLeftHeadVectorOfPositive A rightHead := by
  have hspec :=
    Classical.choose_spec
      (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℝ) (E := EuclideanSpace ℝ m) (ι := m)
        (by simp)
        (v := fun _ : m => realBidiagonalizationLeftHeadVectorOfPositive A rightHead)
        (s := {leftHead})
        (realBidiagonalizationLeftHeadVectorOfPositive_singleton_orthonormal
          A leftHead rightHead hpos))
  exact hspec leftHead (by simp)

lemma realBidiagonalizationLeftBasisOfPositive_head_col_zero
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (leftHead : m) (rightHead : n)
    (hpos : 0 < realBidiagonalizationRightEigenvalue A rightHead)
    (i : m) (hi : i ≠ leftHead) :
    ⇑(realBidiagonalizationLeftBasisOfPositive A leftHead rightHead hpos i) ⬝ᵥ
        (A *ᵥ ⇑(realBidiagonalizationRightBasis A rightHead)) = 0 := by
  exact
    realBidiagonalizationLeftBasis_head_col_zero_of_head_eq_positive
      A leftHead rightHead
      (realBidiagonalizationLeftBasisOfPositive A leftHead rightHead hpos)
      (realBidiagonalizationLeftBasisOfPositive_head A leftHead rightHead hpos)
      hpos i hi

structure RealBidiagonalizationHeadBasisWitness
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n ℝ) where
  leftBasis : OrthonormalBasis m ℝ (EuclideanSpace ℝ m)
  rightBasis : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)
  sigma : ℝ
  sigma_nonneg : 0 ≤ sigma
  head_image :
    A *ᵥ ⇑(rightBasis (headElem (α := n))) =
      sigma • ⇑(leftBasis (headElem (α := m)))
  head_entry :
    ⇑(leftBasis (headElem (α := m))) ⬝ᵥ
      (A *ᵥ ⇑(rightBasis (headElem (α := n)))) = sigma
  head_row_zero :
    ∀ j : n, j ≠ headElem (α := n) →
      ⇑(leftBasis (headElem (α := m))) ⬝ᵥ
        (A *ᵥ ⇑(rightBasis j)) = 0
  head_col_zero :
    ∀ i : m, i ≠ headElem (α := m) →
      ⇑(leftBasis i) ⬝ᵥ
        (A *ᵥ ⇑(rightBasis (headElem (α := n)))) = 0

noncomputable def realBidiagonalizationHeadBasisWitnessOfPositiveIndex
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n ℝ) (k : n)
    (hpos : 0 < realBidiagonalizationRightEigenvalue A k) :
    RealBidiagonalizationHeadBasisWitness m n A where
  leftBasis :=
    realBidiagonalizationLeftBasisOfPositive A (headElem (α := m)) k hpos
  rightBasis :=
    (realBidiagonalizationRightBasis A).reindex (Equiv.swap (headElem (α := n)) k)
  sigma := realBidiagonalizationSingularValue A k
  sigma_nonneg := realBidiagonalizationSingularValue_nonneg A k
  head_image := by
    rw [OrthonormalBasis.reindex_apply]
    rw [swap_symm_apply, Equiv.swap_apply_left]
    rw [realBidiagonalizationRightBasis_image_eq_singularValue_smul_leftHead A k hpos]
    rw [← realBidiagonalizationLeftBasisOfPositive_head A (headElem (α := m)) k hpos]
  head_entry := by
    rw [OrthonormalBasis.reindex_apply]
    rw [swap_symm_apply, Equiv.swap_apply_left]
    have hhead_fun :
        ⇑(realBidiagonalizationLeftBasisOfPositive A (headElem (α := m)) k hpos
            (headElem (α := m))) =
          ⇑(realBidiagonalizationLeftHeadVectorOfPositive A k) :=
      congrArg (fun v : EuclideanSpace ℝ m => ⇑v)
        (realBidiagonalizationLeftBasisOfPositive_head A (headElem (α := m)) k hpos)
    rw [hhead_fun]
    exact realBidiagonalizationLeftHeadVectorOfPositive_head_entry A k hpos
  head_row_zero := by
    intro j hj
    rw [OrthonormalBasis.reindex_apply]
    rw [swap_symm_apply]
    have hhead_fun :
        ⇑(realBidiagonalizationLeftBasisOfPositive A (headElem (α := m)) k hpos
            (headElem (α := m))) =
          ⇑(realBidiagonalizationLeftHeadVectorOfPositive A k) :=
      congrArg (fun v : EuclideanSpace ℝ m => ⇑v)
        (realBidiagonalizationLeftBasisOfPositive_head A (headElem (α := m)) k hpos)
    rw [hhead_fun]
    exact realBidiagonalizationLeftHeadVectorOfPositive_head_row_zero A k
      (Equiv.swap (headElem (α := n)) k j)
      (Ne.symm (swap_apply_ne_right_of_ne_left (headElem (α := n)) k j hj))
  head_col_zero := by
    intro i hi
    rw [OrthonormalBasis.reindex_apply]
    rw [swap_symm_apply, Equiv.swap_apply_left]
    exact realBidiagonalizationLeftBasisOfPositive_head_col_zero A
      (headElem (α := m)) k hpos i hi

lemma matrix_eq_zero_of_realBidiagonalizationRightEigenvalue_eq_zero
    {m n : Type u} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ)
    (hzero : ∀ j : n, realBidiagonalizationRightEigenvalue A j = 0) :
    A = 0 := by
  have hgram_zero : realBidiagonalizationRightGram A = 0 := by
    have heigs : (realBidiagonalizationRightGram_isHermitian A).eigenvalues = 0 := by
      ext j
      exact hzero j
    simpa using (realBidiagonalizationRightGram_isHermitian A).eigenvalues_eq_zero_iff.mp heigs
  exact Matrix.conjTranspose_mul_self_eq_zero.mp
    (by simpa [realBidiagonalizationRightGram] using hgram_zero)

noncomputable def realBidiagonalizationHeadBasisWitnessOfZeroMatrix
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n ℝ) (hA : A = 0) :
    RealBidiagonalizationHeadBasisWitness m n A where
  leftBasis := EuclideanSpace.basisFun m ℝ
  rightBasis := EuclideanSpace.basisFun n ℝ
  sigma := 0
  sigma_nonneg := le_rfl
  head_image := by
    rw [hA]
    ext i
    simp
  head_entry := by
    rw [hA]
    simp
  head_row_zero := by
    intro j hj
    rw [hA]
    simp
  head_col_zero := by
    intro i hi
    rw [hA]
    simp

noncomputable def realBidiagonalizationHeadBasisWitnessOfZeroEigenvalues
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n ℝ)
    (hzero : ∀ j : n, realBidiagonalizationRightEigenvalue A j = 0) :
    RealBidiagonalizationHeadBasisWitness m n A :=
  realBidiagonalizationHeadBasisWitnessOfZeroMatrix A
    (matrix_eq_zero_of_realBidiagonalizationRightEigenvalue_eq_zero A hzero)

noncomputable def realBidiagonalizationHeadBasisWitness
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n ℝ) :
    RealBidiagonalizationHeadBasisWitness m n A := by
  classical
  by_cases hpos_exists : ∃ k : n, 0 < realBidiagonalizationRightEigenvalue A k
  · let k := Classical.choose hpos_exists
    exact realBidiagonalizationHeadBasisWitnessOfPositiveIndex A k
      (Classical.choose_spec hpos_exists)
  · have hzero : ∀ j : n, realBidiagonalizationRightEigenvalue A j = 0 := by
      intro j
      have hnonneg : 0 ≤ realBidiagonalizationRightEigenvalue A j :=
        realBidiagonalizationRightEigenvalue_nonneg A j
      have hnotpos : ¬ 0 < realBidiagonalizationRightEigenvalue A j := by
        intro hj
        exact hpos_exists ⟨j, hj⟩
      exact le_antisymm (not_lt.mp hnotpos) hnonneg
    exact realBidiagonalizationHeadBasisWitnessOfZeroEigenvalues A hzero

/-- Matrix whose columns are a real orthonormal basis. -/
noncomputable def realMatrixOfOrthonormalBasis
    {ι : Type u} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    Matrix ι ι ℝ :=
  (EuclideanSpace.basisFun ι ℝ).toBasis.toMatrix b.toBasis

lemma realMatrixOfOrthonormalBasis_unitary
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    IsUnitaryMatrix (realMatrixOfOrthonormalBasis b) := by
  constructor
  · exact (EuclideanSpace.basisFun ι ℝ).toMatrix_orthonormalBasis_conjTranspose_mul_self b
  · exact (EuclideanSpace.basisFun ι ℝ).toMatrix_orthonormalBasis_self_mul_conjTranspose b

lemma realMatrixOfOrthonormalBasis_orthogonal
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    IsOrthogonalMatrix (realMatrixOfOrthonormalBasis b) := by
  have hmem : realMatrixOfOrthonormalBasis b ∈ Matrix.orthogonalGroup ι ℝ :=
    (EuclideanSpace.basisFun ι ℝ).toMatrix_orthonormalBasis_mem_orthogonal b
  exact (Matrix.mem_orthogonalGroup_iff' (A := realMatrixOfOrthonormalBasis b)).1 hmem

@[simp] lemma realMatrixOfOrthonormalBasis_apply
    {ι : Type u} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (i j : ι) :
    realMatrixOfOrthonormalBasis b i j = ⇑(b j) i := rfl

lemma real_dotProduct_mulVec_eq_entry
    {m n : Type u} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (u : m → ℝ) (v : n → ℝ) :
    u ⬝ᵥ (A *ᵥ v) = ∑ x, u x * ∑ y, A x y * v y := by
  rfl

lemma realBidiagonalizationHeadBasisWitness_entry
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    {A : Matrix m n ℝ} (w : RealBidiagonalizationHeadBasisWitness m n A)
    (i : m) (j : n) :
    ((realMatrixOfOrthonormalBasis w.leftBasis)ᴴ *
        A * (realMatrixOfOrthonormalBasis w.rightBasis)) i j =
      ⇑(w.leftBasis i) ⬝ᵥ (A *ᵥ ⇑(w.rightBasis j)) := by
  rw [real_dotProduct_mulVec_eq_entry]
  simp [Matrix.mul_apply, Matrix.conjTranspose, realMatrixOfOrthonormalBasis_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Concrete real one-step oracle from the symmetric right Gram spectral data. -/
noncomputable def realBidiagonalizationStepOracle
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    BidiagonalizationStepOracle ℝ m n where
  U := fun A => realMatrixOfOrthonormalBasis
    (realBidiagonalizationHeadBasisWitness A).leftBasis
  V := fun A => realMatrixOfOrthonormalBasis
    (realBidiagonalizationHeadBasisWitness A).rightBasis
  unitary_U := fun A =>
    realMatrixOfOrthonormalBasis_unitary (realBidiagonalizationHeadBasisWitness A).leftBasis
  unitary_V := fun A =>
    realMatrixOfOrthonormalBasis_unitary (realBidiagonalizationHeadBasisWitness A).rightBasis
  ready := by
    intro A
    let w := realBidiagonalizationHeadBasisWitness A
    constructor
    · intro i
      change
        ((realMatrixOfOrthonormalBasis w.leftBasis)ᴴ *
            A * (realMatrixOfOrthonormalBasis w.rightBasis))
          (i : m) (headElem (α := n)) = 0
      rw [realBidiagonalizationHeadBasisWitness_entry w]
      exact w.head_col_zero i i.2
    · intro j
      change
        ((realMatrixOfOrthonormalBasis w.leftBasis)ᴴ *
            A * (realMatrixOfOrthonormalBasis w.rightBasis))
          (headElem (α := m)) (j : n) = 0
      rw [realBidiagonalizationHeadBasisWitness_entry w]
      exact w.head_row_zero j j.2

/--
Unconditional real orthogonal bidiagonalization, routed through the
bidiagonalization rectangular descent framework.
-/
theorem exists_orthogonal_bidiagonalization
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℝ) :
    HasOrthogonalBidiagonalization A := by
  exact exists_orthogonal_bidiagonalization_oracle
    (fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        realBidiagonalizationStepOracle (m := p) (n := q))
    A

end RealSpectral

end MatDecompFormal.Instances
