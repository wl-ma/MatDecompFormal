import MatDecompFormal.Instances.RationalCanonical.ModuleBridge

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Rational Canonical Form: Cyclic Block Descent Template

The existing square strategy framework removes one distinguished index.  The
general rational-canonical theorem over an arbitrary field needs a block step:
one cyclic `K[X]` summand contributes a companion block whose dimension may be
greater than one.

This file keeps the proof on the project subtype-descent route by instantiating
the lower-level `SquareSliceData`/`SquareProofData` driver directly.  The cyclic
block oracle is still mathematical input; the driver assembly itself is the
same recursive template used elsewhere in the project.
-/

/-- A positive-dimensional matrix together with one cyclic companion-block step. -/
structure RationalCanonicalBlockStepOracle
    (K : Type v) [Field K] : Type (max (u + 1) (v + 1)) where
  step :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      (A : Matrix ι ι K) →
        RationalCanonicalCyclicBlockStepData K ι A

/--
Polynomial-module bridge for the block-size rational-canonical driver.

Unlike the legacy one-index `RationalCanonicalPolynomialModuleBridge`, this
bridge targets the mathematically correct cyclic block step: a PID summand may
have degree greater than one, and the descent removes that whole companion
block at once.
-/
structure RationalCanonicalPolynomialBlockStepData
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A)
    (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) where
  step : RationalCanonicalCyclicBlockStepData K ι A
  cyclic_annihilator_eq_selected :
    step.cyclic_annihilator = selected.annihilator
  cyclic_blockSize_eq_selected_natDegree :
    step.cyclic_blockSize = selected.annihilator.natDegree

/- See `RationalCanonicalPolynomialBlockStepData` for the consistency payload
between the selected PID summand and the emitted matrix block step. -/
structure RationalCanonicalPolynomialBlockBridge
    (K : Type v) [Field K] : Type (max (u + 1) (v + 1)) where
  stepData :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      (A : Matrix ι ι K) →
        RationalCanonicalPolynomialModuleData K ι A →
          (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) →
            (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) →
              RationalCanonicalPolynomialBlockStepData K ι A decomposition selected

/--
Sharper bridge target for the remaining algebra: prove the selected/tail
certificate, then obtain the full block-step payload mechanically.
-/
structure RationalCanonicalSelectedBlockStepCertificateBridge
    (K : Type v) [Field K] : Type (max (u + 1) (v + 1)) where
  certificate :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      (A : Matrix ι ι K) →
        RationalCanonicalPolynomialModuleData K ι A →
          (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) →
            (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) →
              RationalCanonicalSelectedBlockStepCertificate K ι A decomposition selected

/--
Most precise bridge target currently exposed: prove the head action and
off-diagonal zero blocks separately.
-/
structure RationalCanonicalSelectedAlgebraicBlockCertificateBridge
    (K : Type v) [Field K] : Type (max (u + 1) (v + 1)) where
  certificate :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      (A : Matrix ι ι K) →
        RationalCanonicalPolynomialModuleData K ι A →
          (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) →
            (selected : RationalCanonicalSelectedCyclicSummand K ι A decomposition) →
              RationalCanonicalSelectedAlgebraicBlockCertificate K ι A decomposition selected

/--
Concrete selected algebraic certificate bridge over an arbitrary field.

The proof is still routed through the block-size descent template: this bridge
only supplies the one-step selected/tail matrix certificate consumed by the
template.
-/
noncomputable def rationalCanonicalSelectedAlgebraicBlockCertificateBridge
    (K : Type v) [Field K] :
    RationalCanonicalSelectedAlgebraicBlockCertificateBridge.{u, v} K where
  certificate := fun _A _data _decomposition selected =>
    rationalCanonicalSelectedAlgebraicBlockCertificate selected

/-- The finer algebraic certificate bridge supplies the selected block-step bridge. -/
noncomputable def rationalCanonicalSelectedBlockStepCertificateBridgeOfAlgebraicBridge
    {K : Type v} [Field K]
    (bridge : RationalCanonicalSelectedAlgebraicBlockCertificateBridge.{u, v} K) :
    RationalCanonicalSelectedBlockStepCertificateBridge.{u, v} K where
  certificate := fun A data decomposition selected =>
    rationalCanonicalSelectedBlockStepCertificateOfAlgebraicCertificate
      (bridge.certificate A data decomposition selected)

/--
A selected/tail certificate bridge supplies the polynomial block bridge consumed
by the cyclic-block descent driver.
-/
noncomputable def rationalCanonicalPolynomialBlockBridgeOfSelectedCertificateBridge
    {K : Type v} [Field K]
    (bridge : RationalCanonicalSelectedBlockStepCertificateBridge.{u, v} K) :
    RationalCanonicalPolynomialBlockBridge.{u, v} K where
  stepData := fun A data decomposition selected =>
    let certificate := bridge.certificate A data decomposition selected
    let step :=
      rationalCanonicalCyclicBlockStepDataOfSelectedCertificate certificate
    { step := step
      cyclic_annihilator_eq_selected := rfl
      cyclic_blockSize_eq_selected_natDegree := rfl }

/-- Concrete polynomial block bridge over `[Field K]`. -/
noncomputable def rationalCanonicalPolynomialBlockBridge
    (K : Type v) [Field K] :
    RationalCanonicalPolynomialBlockBridge.{u, v} K :=
  rationalCanonicalPolynomialBlockBridgeOfSelectedCertificateBridge
    (rationalCanonicalSelectedBlockStepCertificateBridgeOfAlgebraicBridge
      (rationalCanonicalSelectedAlgebraicBlockCertificateBridge (K := K)))

/-- A polynomial block bridge supplies the block-step oracle used by descent. -/
noncomputable def rationalCanonicalBlockStepOracleOfPolynomialBlockBridge
    {K : Type v} [Field K]
    (selectionBridge : RationalCanonicalSelectedCyclicSummandBridge.{u, v} K)
    (bridge : RationalCanonicalPolynomialBlockBridge.{u, v} K) :
    RationalCanonicalBlockStepOracle.{u, v} K where
  step := fun A =>
    let data := rationalCanonicalPolynomialModuleData A
    let decomposition := rationalCanonicalPolynomialModuleDecompositionData A data
    let selected := selectionBridge.select A data decomposition
    (bridge.stepData A data decomposition selected).step

/-- Evaluate the block-step oracle on a positive square-universe object. -/
noncomputable def rationalCanonicalBlockStep
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K)
    (x_sub : PosSquareUniverse K) :
    RationalCanonicalCyclicBlockStepData K x_sub.1.ι x_sub.1.A := by
  classical
  letI : Nonempty x_sub.1.ι := posSquareUniverse_nonempty x_sub
  exact oracle.step x_sub.1.A

/-- The matrix obtained after applying the cyclic-block similarity step. -/
noncomputable def rationalCanonicalBlockStepMatrix
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K)
    (x_sub : PosSquareUniverse K) :
    Matrix x_sub.1.ι x_sub.1.ι K :=
  let step := rationalCanonicalBlockStep oracle x_sub
  step.Pinv * x_sub.1.A * step.P

/-- Positive-universe wrapper for the transformed matrix in a block step. -/
noncomputable def rationalCanonicalBlockStepUniverse
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K)
    (x_sub : PosSquareUniverse K) : PosSquareUniverse K :=
  ⟨{ ι := x_sub.1.ι
     fintype_ι := x_sub.1.fintype_ι
     decEq_ι := x_sub.1.decEq_ι
     linOrder_ι := x_sub.1.linOrder_ι
     A := rationalCanonicalBlockStepMatrix oracle x_sub }, by
    simpa [squareSubtypeμ] using x_sub.2⟩

/-- Square-universe tail slice after removing the selected cyclic block. -/
noncomputable def rationalCanonicalBlockSliceUniverse
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K)
    (x_sub : PosSquareUniverse K) : SquareUniverse K :=
  let step := rationalCanonicalBlockStep oracle x_sub
  { ι := step.tailIdx
    fintype_ι := step.fintype_tailIdx
    decEq_ι := step.decEq_tailIdx
    linOrder_ι := step.linearOrder_tailIdx
    A := step.tail }

/-- Similarity reachability relation for the cyclic block step. -/
noncomputable def rationalCanonicalBlockR
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K)
    (y_sub x_sub : PosSquareUniverse K) : Prop :=
  y_sub = rationalCanonicalBlockStepUniverse oracle x_sub

/-- Slicability is exactly the presence of oracle-provided cyclic-block data. -/
def rationalCanonicalBlockIsSliceable
    {K : Type v} [Field K]
    (_oracle : RationalCanonicalBlockStepOracle.{u, v} K)
    (_x_sub : PosSquareUniverse K) : Prop :=
  True

/-- `SquareSliceData` induced by a cyclic-block oracle. -/
noncomputable def rationalCanonicalBlockSliceData
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K) :
    SquareSliceData K where
  r_sub := rationalCanonicalBlockR oracle
  IsSliceable_sub := rationalCanonicalBlockIsSliceable oracle
  slice_sub := fun x_sub _ => rationalCanonicalBlockSliceUniverse oracle x_sub

/--
The transformed matrix is similar to the original matrix, so rational-canonical
existence transports backward along the oracle similarity.
-/
theorem rationalCanonicalBlock_transport
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K) :
    SquareTransportType RationalCanonical_P
      (rationalCanonicalBlockSliceData oracle) := by
  intro x_sub y_sub h_r hP
  subst y_sub
  dsimp [RationalCanonical_P] at hP ⊢
  let step := rationalCanonicalBlockStep oracle x_sub
  simpa [rationalCanonicalBlockStepUniverse, rationalCanonicalBlockStepMatrix]
    using rationalCanonical_transport_similarity
      step.P step.Pinv x_sub.1.A
      (step.Pinv * x_sub.1.A * step.P)
      step.inverse_P rfl hP

/--
The cyclic-block lift combines the companion head block supplied by the oracle
with the recursive tail witness.
-/
theorem rationalCanonicalBlock_lift
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K) :
    SquareLiftType RationalCanonical_P
      (rationalCanonicalBlockSliceData oracle) := by
  intro x_sub _ hTail
  dsimp [RationalCanonical_P] at hTail ⊢
  let step := rationalCanonicalBlockStep oracle x_sub
  have hHeadRC : IsRationalCanonicalMatrix step.head :=
    isRationalCanonicalMatrix_singleCompanion
      step.head step.cyclic_annihilator step.head_companion
  have hBlock :
      HasRationalCanonical
        (rationalCanonicalBlockDiagLex step.head step.tail) :=
    hasRationalCanonical_blockDiag_lex step.head step.tail
      (hasRationalCanonical_of_isRationalCanonicalMatrix hHeadRC) hTail
  have hReindexed :
      HasRationalCanonical
        (Matrix.reindex step.splitIndex step.splitIndex
          (step.Pinv * x_sub.1.A * step.P)) := by
    rw [step.block_eq]
    exact hBlock
  have hBack :=
    hasRationalCanonical_reindex (e := step.splitIndex.symm) hReindexed
  have hTransformed :
      HasRationalCanonical (step.Pinv * x_sub.1.A * step.P) := by
    simpa [step, reindex_reindex] using hBack
  exact rationalCanonical_transport_similarity
    step.P step.Pinv x_sub.1.A (step.Pinv * x_sub.1.A * step.P)
    step.inverse_P rfl hTransformed

/-- Proof hooks for the cyclic block subtype-descent driver. -/
noncomputable def rationalCanonicalBlockProofData
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K) :
    SquareProofData RationalCanonical_P
      (rationalCanonicalBlockSliceData oracle) where
  transport_sub := rationalCanonicalBlock_transport oracle
  lift_from_slice_sub := rationalCanonicalBlock_lift oracle

/-- Reachability and strict progress for the cyclic block driver. -/
noncomputable def rationalCanonicalBlockReach
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K) :
    ∀ (x_sub : PosSquareUniverse K),
      squareSubtypeμ (x_sub : SquareUniverse K) > squareSubtypeμBase →
        SquareReachType (rationalCanonicalBlockSliceData oracle) x_sub := by
  intro x_sub _hgt
  let y_sub := rationalCanonicalBlockStepUniverse oracle x_sub
  refine ⟨y_sub, trivial, ?_, ?_⟩
  · rfl
  · let step := rationalCanonicalBlockStep oracle y_sub
    have hslice_card :
        squareSubtypeμ
            ((rationalCanonicalBlockSliceData oracle).slice_sub y_sub trivial) =
          Fintype.card step.tailIdx := by
      rfl
    have hsplit :
        Fintype.card y_sub.1.ι = Fintype.card step.blockIdx + Fintype.card step.tailIdx := by
      simpa [Fintype.card_lex] using (Fintype.card_congr step.splitIndex)
    have hblock_pos : 0 < Fintype.card step.blockIdx := by
      rw [step.block_card_eq]
      exact step.cyclic_blockSize_pos
    have hy_card : Fintype.card y_sub.1.ι = Fintype.card x_sub.1.ι := by
      simp [y_sub, rationalCanonicalBlockStepUniverse]
    rw [hslice_card]
    change Fintype.card step.tailIdx < Fintype.card x_sub.1.ι
    omega

/-- Cyclic-block rational canonical driver assembled through subtype descent. -/
noncomputable def rationalCanonical_block_framework_inst
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstance
    RationalCanonical_P
    rationalCanonical_base_univ
    (rationalCanonicalBlockSliceData oracle)
    (rationalCanonicalBlockReach oracle)
    (rationalCanonicalBlockProofData oracle)

/--
Framework-routed rational canonical theorem from a cyclic-block oracle.

This is the block-size analogue of `exists_rational_canonical_matrix_framework`;
it still uses the project subtype-descent template, but the recursive slice is
the complement of a full cyclic companion block.
-/
theorem exists_rational_canonical_matrix_block_framework
    {K : Type v} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, v} K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasRationalCanonical A := by
  have hP :
      (rationalCanonical_block_framework_inst oracle).P
        (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := rationalCanonical_block_framework_inst oracle) A
  exact hP

/--
Matrix rational-canonical theorem from the polynomial-module block bridge.

This is the intended bridge shape for the general `[Field K]` theorem: the PID
module decomposition is converted to cyclic block step data, and the final proof
is discharged by the block-size subtype-descent driver.
-/
theorem exists_rational_canonical_matrix_polynomial_block_bridge
    {K : Type v} [Field K]
    (selectionBridge : RationalCanonicalSelectedCyclicSummandBridge.{u, v} K)
    (bridge : RationalCanonicalPolynomialBlockBridge.{u, v} K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasRationalCanonical A :=
  exists_rational_canonical_matrix_block_framework
    (rationalCanonicalBlockStepOracleOfPolynomialBlockBridge selectionBridge bridge) A

/--
Matrix rational-canonical theorem over an arbitrary field, routed through the
cyclic block-size subtype-descent template.
-/
theorem exists_rational_canonical_matrix
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasRationalCanonical A :=
  exists_rational_canonical_matrix_polynomial_block_bridge
    (rationalCanonicalSelectedCyclicSummandBridgeOfEffectiveIndexBridge
      (rationalCanonicalEffectiveSummandIndexBridge K))
    (rationalCanonicalPolynomialBlockBridge K)
    A

/--
Finite-dimensional linear-operator entry point through the polynomial-module
block bridge.  The matrix theorem used here is the block-size descent-template
theorem above.
-/
theorem exists_rational_canonical_form_polynomial_block_bridge
    {K : Type v} {V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (selectionBridge : RationalCanonicalSelectedCyclicSummandBridge.{u, v} K)
    (bridge : RationalCanonicalPolynomialBlockBridge.{u, v} K)
    (T : V →ₗ[K] V) :
    ∃ b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V,
      HasRationalCanonical
        (K := K) (ι := ULift.{u, 0} (Fin (Module.finrank K V)))
        (LinearMap.toMatrix b b T) := by
  classical
  let b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V :=
    (Module.finBasis K V).reindex Equiv.ulift.symm
  exact ⟨b, exists_rational_canonical_matrix_polynomial_block_bridge
    (K := K) (ι := ULift.{u, 0} (Fin (Module.finrank K V)))
    selectionBridge bridge
    (LinearMap.toMatrix b b T)⟩

/--
Finite-dimensional linear-operator rational-canonical entry point over an
arbitrary field.  This wrapper uses the matrix theorem above, so the proof path
remains the cyclic block-size descent template.
-/
theorem exists_rational_canonical_form
    {K : Type v} {V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (T : V →ₗ[K] V) :
    ∃ b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V,
      HasRationalCanonical
        (K := K) (ι := ULift.{u, 0} (Fin (Module.finrank K V)))
        (LinearMap.toMatrix b b T) := by
  classical
  let b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V :=
    (Module.finBasis K V).reindex Equiv.ulift.symm
  exact ⟨b, exists_rational_canonical_matrix
    (K := K) (ι := ULift.{u, 0} (Fin (Module.finrank K V)))
    (LinearMap.toMatrix b b T)⟩

end MatDecompFormal.Instances
