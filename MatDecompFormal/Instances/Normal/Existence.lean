import MatDecompFormal.Instances.Normal.Direct

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Normal Matrix Spectral Decomposition: Framework Entry

This file assembles the normal-matrix descent strategy through the same bridge
used by the other decompositions:

```lean
SquareStrategyData
mkSquareSubtypeInductionInstanceFromStrategy
SquareSubtypeInductionInstance.prove_for_matrix
```

At this stage the theorem is conditional on `NormalSimilarityOracle` and
the concrete descent hooks are constructed in `Direct.lean` from block lift,
tail-normality, and unitary-similarity transport lemmas.
-/

/-- Universe-level base case for the normal spectral target. -/
theorem normalSpectral_base_univ (x : SquareUniverse ℂ) :
    ((∀ (x_sub : PosSquareUniverse ℂ), (x_sub : SquareUniverse ℂ) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      NormalSpectral_P x := by
  intro hx _hNormal
  have hzero : Fintype.card x.ι = 0 := by
    have hxcard : Fintype.card x.ι ≤ 0 := by
      rcases hx with hnot | hle
      · by_contra hnotzero
        have hposCard : 0 < Fintype.card x.ι :=
          Nat.pos_of_ne_zero (fun hz => hnotzero (hz.le))
        let x_sub : PosSquareUniverse ℂ := ⟨x, hposCard⟩
        exact hnot x_sub rfl
      · simpa [squareSubtypeμ, squareSubtypeμBase] using hle
    exact Nat.le_zero.mp hxcard
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  letI : Subsingleton x.ι := by infer_instance
  exact base_normalSpectral_subsingleton x.A

noncomputable def normal_strategy_data
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι)
    (hooks : NormalDescentHooks oracle) :
    SquareStrategyData ℂ NormalSpectral_P :=
  mkSquareStrategyData
    (normal_strategy_core oracle)
    (normal_strategy_proof oracle hooks)

noncomputable def normal_framework_inst
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        NormalSimilarityOracle ι)
    (hooks : NormalDescentHooks oracle) :
    SquareSubtypeInductionInstance ℂ :=
  mkSquareSubtypeInductionInstanceFromStrategy
    NormalSpectral_P
    normalSpectral_base_univ
    (normal_strategy_data oracle hooks)

/--
Conditional framework-routed normal spectral decomposition theorem.

This variant keeps the explicit `hooks` argument for callers that want to
override the default block-lift proof package.
-/
theorem exists_normal_spectral_decomposition_framework
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        NormalSimilarityOracle κ)
    (hooks : NormalDescentHooks oracle)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  have hP :
      (normal_framework_inst oracle hooks).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := normal_framework_inst oracle hooks) A
  exact hP hA

/--
Framework-routed normal spectral decomposition theorem conditional only on the
unitary-similarity oracle. The proof-side transport and lift hooks are now
constructed concretely from the descent algebra in `Direct.lean`.
-/
theorem exists_normal_spectral_decomposition_framework_oracle
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        NormalSimilarityOracle κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  exact exists_normal_spectral_decomposition_framework
    oracle (normal_descent_hooks oracle) A hA

/--
Framework-routed theorem in terms of the remaining normal-case block-ready
oracle. Non-normal matrices are handled by the strategy-side `NormalDescentReady`
branch, while the final target consumes only the supplied normality assumption.
-/
theorem exists_normal_spectral_decomposition_framework_blockOracle
    (blockOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalBlockReadyOracle κ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        NormalSimilarityOracle κ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalSimilarityOracleOfBlockReady κ (blockOracle (κ := κ))
  exact exists_normal_spectral_decomposition_framework_oracle oracle A hA

/--
Framework-routed theorem in terms of the standard normal diagonalization
oracle. This is the closest current interface to the intended final
normal-matrix spectral theorem: once mathlib supplies, or we prove, unitary
diagonalization of every normal matrix, the descent framework produces the
project's `HasNormalSpectral` target.
-/
theorem exists_normal_spectral_decomposition_framework_diagonalization
    (diagOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalDiagonalizationOracle κ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let blockOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalBlockReadyOracle κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalBlockReadyOracleOfDiagonalization κ (diagOracle (κ := κ))
  exact exists_normal_spectral_decomposition_framework_blockOracle blockOracle A hA

/--
Framework-routed theorem in terms of a joint Hermitian-pair diagonalization
oracle. This is the intended bridge to mathlib's commuting self-adjoint joint
eigenspace theorem.
-/
theorem exists_normal_spectral_decomposition_framework_hermitianPair
    (pairOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPairDiagonalizationOracle κ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let diagOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalDiagonalizationOracle κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalDiagonalizationOracleOfHermitianPair κ (pairOracle (κ := κ))
  exact exists_normal_spectral_decomposition_framework_diagonalization diagOracle A hA

/--
Framework-routed theorem in terms of simultaneous diagonalization of the
canonical Hermitian real and imaginary parts of a normal matrix.
-/
theorem exists_normal_spectral_decomposition_framework_hermitianParts
    (partsOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartSimultaneousDiagonalizationOracle κ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let pairOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPairDiagonalizationOracle κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalHermitianPairOracleOfParts κ (partsOracle (κ := κ))
  exact exists_normal_spectral_decomposition_framework_hermitianPair pairOracle A hA

/--
Framework-routed theorem in terms of an orthonormal simultaneous eigenbasis
for the canonical Hermitian real and imaginary parts.
-/
theorem exists_normal_spectral_decomposition_framework_jointEigenbasis
    (joint :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasis κ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let partsOracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartSimultaneousDiagonalizationOracle κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalHermitianPartOracleOfJointEigenbasis κ (joint (κ := κ))
  exact exists_normal_spectral_decomposition_framework_hermitianParts partsOracle A hA

/--
Framework-routed theorem in terms of an orthonormal basis subordinate to joint
eigenspaces of the canonical Hermitian real and imaginary parts.
-/
theorem exists_normal_spectral_decomposition_framework_subordinateJointEigenbasis
    (sub :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinate κ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let joint :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasis κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalHermitianPartJointEigenbasisOfSubordinate κ (sub (κ := κ))
  exact exists_normal_spectral_decomposition_framework_jointEigenbasis joint A hA

/--
Framework-routed theorem in terms of a `Fin (Fintype.card κ)`-indexed
orthonormal basis subordinate to the joint eigenspaces.
-/
theorem exists_normal_spectral_decomposition_framework_subordinateJointEigenbasisFin
    (subFin :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinateFin κ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let sub :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinate κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalHermitianPartSubordinateOfFin κ (subFin (κ := κ))
  exact exists_normal_spectral_decomposition_framework_subordinateJointEigenbasis sub A hA

/--
Framework-routed theorem in terms of a finite family of joint eigenspaces plus a
subordinate `Fin (Fintype.card κ)`-indexed orthonormal basis.
-/
theorem exists_normal_spectral_decomposition_framework_finiteJointSubordinate
    (γ : Type v)
    [Fintype γ] [DecidableEq γ]
    (finite :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartFiniteJointSubordinate κ γ _ _ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let subFin :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinateFin κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalHermitianPartSubordinateFinOfFiniteJoint κ γ (finite (κ := κ))
  exact exists_normal_spectral_decomposition_framework_subordinateJointEigenbasisFin subFin A hA

/--
Framework-routed theorem in terms of a sigma-indexed orthonormal basis
subordinate to finitely many joint eigenspaces.
-/
theorem exists_normal_spectral_decomposition_framework_subordinateJointEigenbasisSigma
    (γ : Type v)
    [Fintype γ] [DecidableEq γ]
    (subSigma :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinateSigma κ γ _ _ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let subFin :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinateFin κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalHermitianPartSubordinateFinOfSigma κ γ (subSigma (κ := κ))
  exact exists_normal_spectral_decomposition_framework_subordinateJointEigenbasisFin subFin A hA

/--
Framework-routed theorem in terms of a sigma-indexed orthonormal basis
subordinate to joint eigenspaces, without requiring the outer label type to be
finite. This matches mathlib's simultaneous eigenspace decomposition indexed by
all pairs of complex eigenvalues; only the total sigma basis index has to be
finite.
-/
theorem exists_normal_spectral_decomposition_framework_subordinateJointEigenbasisGeneralSigma
    (γ : Type v)
    (subSigma :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinateGeneralSigma κ γ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let subFin :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinateFin κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalHermitianPartSubordinateFinOfGeneralSigma κ γ (subSigma (κ := κ))
  exact exists_normal_spectral_decomposition_framework_subordinateJointEigenbasisFin subFin A hA

/--
Framework-routed theorem in terms of a sigma-indexed orthonormal basis whose
fiber type may depend on the matrix. This matches the basis naturally produced
by `DirectSum.IsInternal.collectedOrthonormalBasis`, where the fiber over a
joint eigenspace label is `Fin (finrank jointSpace)`.
-/
theorem exists_normal_spectral_decomposition_framework_subordinateJointEigenbasisDependentSigma
    (γ : Type v)
    (subSigma :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinateDependentSigma κ γ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let subFin :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinateFin κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalHermitianPartSubordinateFinOfDependentSigma κ γ (subSigma (κ := κ))
  exact exists_normal_spectral_decomposition_framework_subordinateJointEigenbasisFin subFin A hA

/--
Framework-routed theorem in terms of a sigma-indexed orthonormal basis whose
label type and fiber type may both depend on the matrix. This matches finite
labels such as the product of the actual eigenvalue subtypes of the Hermitian
real and imaginary parts.
-/
theorem exists_normal_spectral_decomposition_framework_subordinateJointEigenbasisMatrixSigma
    (subSigma :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinateMatrixSigma κ _ _ _ _)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let subFin :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinateFin κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalHermitianPartSubordinateFinOfMatrixSigma κ (subSigma (κ := κ))
  exact exists_normal_spectral_decomposition_framework_subordinateJointEigenbasisFin subFin A hA

/--
Unconditional framework-routed normal spectral decomposition theorem.

The spectral step is discharged by diagonalizing the canonical commuting
Hermitian real and imaginary parts via finite joint eigenspaces, then routing the
result through the project's square descent framework.
-/
theorem exists_normal_spectral_decomposition
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A := by
  let subSigma :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        @NormalHermitianPartJointEigenbasisSubordinateMatrixSigma κ _ _ _ _ :=
    fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      normalHermitianPartMatrixSigma κ
  exact exists_normal_spectral_decomposition_framework_subordinateJointEigenbasisMatrixSigma
    subSigma A hA

end MatDecompFormal.Instances
