import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Instances.Jordan.Generalized
import MatDecompFormal.Instances.Jordan.Strategy
import MatDecompFormal.Instances.Jordan.GeneralizedCompanion
import MatDecompFormal.Instances.RationalCanonical.BlockStrategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Generalized Jordan Existence: Framework Layer

This file provides the dependent block-descent assembly for generalized Jordan
form, including the concrete RCF-backed block driver.
-/

/-- Universe-level generalized Jordan predicate. -/
def GeneralizedJordan_P {K : Type u} [Field K] (x : SquareUniverse K) : Prop :=
  HasGeneralizedJordanMatrix x.A

/-- Base case for the generalized Jordan target. -/
theorem generalized_jordan_base_univ
    {K : Type u} [Field K] (x : SquareUniverse K) :
    ((∀ (x_sub : PosSquareUniverse K), (x_sub : SquareUniverse K) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      GeneralizedJordan_P x := by
  intro hx
  have hzero : Fintype.card x.ι = 0 :=
    squareSubtypeBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  exact base_generalized_jordan_empty x.A

/-- Block-step readiness for generalized Jordan descent. -/
structure GeneralizedJordanBlockStepReady
    (K : Type u) (ι : Type u) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (β γ : Type u) [Fintype β] [DecidableEq β] [LinearOrder β]
    [Fintype γ] [DecidableEq γ] [LinearOrder γ]
    (A : Matrix ι ι K) where
  e : ι ≃ β ⊕ₗ γ
  head : Matrix β β K
  head_hasGeneralizedJordan : HasGeneralizedJordanMatrix head
  head_nonempty : Nonempty β
  block_eq :
    Matrix.reindex e e A =
      jordanBlockDiagLex head (jordanBlockSlice e A)

/-- A generalized block step strictly decreases dimension. -/
theorem generalized_jordan_block_slice_card_lt
    {K : Type u} {ι β γ : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype β] [DecidableEq β] [LinearOrder β]
    [Fintype γ] [DecidableEq γ] [LinearOrder γ]
    {A : Matrix ι ι K}
    (ready : GeneralizedJordanBlockStepReady K ι β γ A) :
    Fintype.card γ < Fintype.card ι := by
  have hcard : Fintype.card ι = Fintype.card (β ⊕ₗ γ) :=
    Fintype.card_congr ready.e
  have hβpos : 0 < Fintype.card β :=
    Fintype.card_pos_iff.mpr ready.head_nonempty
  rw [hcard, Fintype.card_lex, Fintype.card_sum]
  omega

/-- Lift a recursive generalized Jordan witness across a block step. -/
theorem generalized_jordan_lift_of_blockStepReady
    {K : Type u} {ι β γ : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype β] [DecidableEq β] [LinearOrder β]
    [Fintype γ] [DecidableEq γ] [LinearOrder γ]
    {A : Matrix ι ι K}
    (ready : GeneralizedJordanBlockStepReady K ι β γ A)
    (hTail : HasGeneralizedJordanMatrix (jordanBlockSlice ready.e A)) :
    HasGeneralizedJordanMatrix A := by
  have hBlock :
      HasGeneralizedJordanMatrix
        (jordanBlockDiagLex ready.head (jordanBlockSlice ready.e A)) :=
    hasGeneralizedJordanMatrix_blockDiag_lex ready.head
      (jordanBlockSlice ready.e A)
      ready.head_hasGeneralizedJordan
      hTail
  have hReindexed :
      HasGeneralizedJordanMatrix (Matrix.reindex ready.e ready.e A) := by
    rw [ready.block_eq]
    exact hBlock
  have hBack := hasGeneralizedJordanMatrix_reindex (e := ready.e.symm) hReindexed
  simpa [reindex_reindex] using hBack

/-- Slice witness for a generalized Jordan block step. -/
structure GeneralizedJordanBlockSliceWitness
    {K : Type u} [Field K] (x_sub : PosSquareUniverse K) where
  β : Type u
  [fintype_β : Fintype β]
  [decEq_β : DecidableEq β]
  [linOrder_β : LinearOrder β]
  γ : Type u
  [fintype_γ : Fintype γ]
  [decEq_γ : DecidableEq γ]
  [linOrder_γ : LinearOrder γ]
  ready : GeneralizedJordanBlockStepReady K x_sub.1.ι β γ x_sub.1.A

attribute [instance] GeneralizedJordanBlockSliceWitness.fintype_β
attribute [instance] GeneralizedJordanBlockSliceWitness.decEq_β
attribute [instance] GeneralizedJordanBlockSliceWitness.linOrder_β
attribute [instance] GeneralizedJordanBlockSliceWitness.fintype_γ
attribute [instance] GeneralizedJordanBlockSliceWitness.decEq_γ
attribute [instance] GeneralizedJordanBlockSliceWitness.linOrder_γ

/-- The recursive slice selected by a generalized block witness. -/
noncomputable def GeneralizedJordanBlockSliceWitness.slice
    {K : Type u} [Field K] {x_sub : PosSquareUniverse K}
    (w : GeneralizedJordanBlockSliceWitness x_sub) :
    SquareUniverse K :=
  { ι := w.γ
    A := jordanBlockSlice w.ready.e x_sub.1.A }

/-- One dependent generalized Jordan block-descent step. -/
structure GeneralizedJordanBlockDriverStepData
    {K : Type u} [Field K] (x_sub : PosSquareUniverse K) where
  B : Matrix x_sub.1.ι x_sub.1.ι K
  P : Matrix x_sub.1.ι x_sub.1.ι K
  invertible_P : InvertibleMatrix P
  B_eq : B = P⁻¹ * x_sub.1.A * P
  witness :
    GeneralizedJordanBlockSliceWitness
      (⟨SquareUniverse.ofMatrix B, by simpa using x_sub.2⟩ : PosSquareUniverse K)

/-- Target universe object produced by a generalized block-driver step. -/
noncomputable def GeneralizedJordanBlockDriverStepData.target
    {K : Type u} [Field K] {x_sub : PosSquareUniverse K}
    (data : GeneralizedJordanBlockDriverStepData x_sub) :
    PosSquareUniverse K :=
  ⟨SquareUniverse.ofMatrix data.B, by simpa using x_sub.2⟩

/-- Explicit generalized Jordan block-driver bridge. -/
structure GeneralizedJordanBlockDriverBridge
    (K : Type u) [Field K] : Type (u + 1) where
  step : ∀ (x_sub : PosSquareUniverse K),
    GeneralizedJordanBlockDriverStepData x_sub

/-- Slice data for the generalized Jordan dependent block driver. -/
noncomputable def generalized_jordan_sliceData
    (K : Type u) [Field K] :
    SquareSliceData K where
  r_sub := fun y_sub x_sub =>
    ∃ data : GeneralizedJordanBlockDriverStepData x_sub, y_sub = data.target
  IsSliceable_sub := fun y_sub =>
    Nonempty (GeneralizedJordanBlockSliceWitness y_sub)
  slice_sub := fun _y_sub hy =>
    let w := Classical.choice hy
    w.slice

/-- Reachability for the generalized Jordan dependent block driver. -/
noncomputable def generalized_jordan_reach
    (K : Type u) [Field K]
    (bridge : GeneralizedJordanBlockDriverBridge K) :
    ∀ (x_sub : PosSquareUniverse K),
      squareSubtypeμ (x_sub : SquareUniverse K) > squareSubtypeμBase →
        SquareReachType (generalized_jordan_sliceData K) x_sub := by
  intro x_sub _hgt
  let data := bridge.step x_sub
  let y_sub : PosSquareUniverse K := data.target
  have hySlice : (generalized_jordan_sliceData K).IsSliceable_sub y_sub := by
    exact ⟨data.witness⟩
  refine ⟨y_sub, hySlice, ?_, ?_⟩
  · refine ⟨data, ?_⟩
    rfl
  · change Fintype.card (Classical.choice hySlice).γ < Fintype.card x_sub.1.ι
    have hready :
        Fintype.card (Classical.choice hySlice).γ <
          Fintype.card y_sub.1.ι :=
      generalized_jordan_block_slice_card_lt (Classical.choice hySlice).ready
    simpa [y_sub, GeneralizedJordanBlockDriverStepData.target] using hready

/-- Proof hooks for the generalized Jordan dependent block driver. -/
noncomputable def generalized_jordan_proofData
    (K : Type u) [Field K] :
    SquareProofData GeneralizedJordan_P (generalized_jordan_sliceData K) where
  transport_sub := by
    intro x_sub y_sub hrel hPy
    rcases hrel with ⟨data, hy⟩
    have hGeneralizedB : HasGeneralizedJordanMatrix data.B := by
      have hPy' : GeneralizedJordan_P (SquareUniverse.ofMatrix data.B) := by
        simpa [hy, GeneralizedJordanBlockDriverStepData.target] using hPy
      exact hPy'
    rcases hGeneralizedB with ⟨S, J, hS, hJ, hBJ⟩
    refine ⟨data.P * S, J, data.invertible_P.mul hS, hJ, ?_⟩
    haveI : Invertible data.P := data.invertible_P.invertible
    haveI : Invertible S := hS.invertible
    calc
      x_sub.1.A = data.P * data.B * data.P⁻¹ := by
        rw [data.B_eq]
        simp [Matrix.mul_assoc]
      _ = data.P * (S * J * S⁻¹) * data.P⁻¹ := by
        rw [hBJ]
      _ = (data.P * S) * J * (data.P * S)⁻¹ := by
        rw [Matrix.mul_inv_rev]
        simp [Matrix.mul_assoc]
  lift_from_slice_sub := by
    intro y_sub hy hSlice
    let w := Classical.choice hy
    have hTail : HasGeneralizedJordanMatrix w.slice.A := hSlice
    exact generalized_jordan_lift_of_blockStepReady w.ready hTail

/-- Generalized Jordan dependent block induction instance. -/
noncomputable def generalized_jordan_framework_inst
    (K : Type u) [Field K]
    (bridge : GeneralizedJordanBlockDriverBridge K) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstance
    GeneralizedJordan_P
    generalized_jordan_base_univ
    (generalized_jordan_sliceData K)
    (generalized_jordan_reach K bridge)
    (generalized_jordan_proofData K)

/--
Framework-routed generalized Jordan theorem, conditional on explicit
generalized block-driver bridge data.
-/
theorem exists_generalized_jordan_matrix_framework_bridge
    {K : Type u} [Field K]
    (bridge : GeneralizedJordanBlockDriverBridge K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasGeneralizedJordanMatrix A := by
  have hP :
      (generalized_jordan_framework_inst K bridge).P
        (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := generalized_jordan_framework_inst K bridge) A
  exact hP

/--
Generalized-Jordan slice witness selected by the concrete RCF prime-power
cyclic block step.
-/
noncomputable def generalizedJordanRCFBlockSliceWitness
    {K : Type u} [Field K]
    (x_sub : PosSquareUniverse K)
    (_data : RationalCanonicalPolynomialModuleData K x_sub.1.ι x_sub.1.A)
    (decomposition :
      RationalCanonicalPolynomialModuleDecompositionData K x_sub.1.ι x_sub.1.A)
    (selected :
      RationalCanonicalSelectedCyclicSummand K x_sub.1.ι x_sub.1.A decomposition)
    (stepData :
      RationalCanonicalPolynomialBlockStepData K x_sub.1.ι x_sub.1.A
        decomposition selected) :
    GeneralizedJordanBlockSliceWitness
      (⟨SquareUniverse.ofMatrix
          (stepData.step.Pinv * x_sub.1.A * stepData.step.P),
        by simpa using x_sub.2⟩ : PosSquareUniverse K) := by
  classical
  let step := stepData.step
  have hHeadGeneralized : HasGeneralizedJordanMatrix step.head := by
    have hcomp :
        SingleCompanionBlockForm step.head
          (selected.cyclic_factor ^ decomposition.exponent selected.selected) := by
      have hann : step.cyclic_annihilator =
          selected.cyclic_factor ^ decomposition.exponent selected.selected := by
        calc
          step.cyclic_annihilator = selected.annihilator := stepData.cyclic_annihilator_eq_selected
          _ = selected.cyclic_factor ^ decomposition.exponent selected.selected :=
            selected.annihilator_eq
      simpa [hann] using step.head_companion
    exact companion_power_hasGeneralizedJordan
      (K := K) (ι := step.blockIdx)
      (decomposition.exponent selected.selected)
      selected.cyclic_factor_monic
      ((selected.cyclic_factor_associated.irreducible_iff).mpr
        (decomposition.prime_irreducible selected.selected))
      selected.exponent_pos
      hcomp
  have hReady :
      GeneralizedJordanBlockStepReady K x_sub.1.ι step.blockIdx step.tailIdx
        (step.Pinv * x_sub.1.A * step.P) := by
    refine {
      e := step.splitIndex
      head := step.head
      head_hasGeneralizedJordan := hHeadGeneralized
      head_nonempty := ?_
      block_eq := ?_
    }
    · exact Fintype.card_pos_iff.mp (by
        rw [step.block_card_eq]
        exact step.cyclic_blockSize_pos)
    · have hblock :
          Matrix.reindex step.splitIndex step.splitIndex
              (step.Pinv * x_sub.1.A * step.P) =
            jordanBlockDiagLex step.head step.tail := by
        simpa [rationalCanonicalBlockDiagLex, jordanBlockDiagLex] using
          step.block_eq
      have htail :
          jordanBlockSlice step.splitIndex
              (step.Pinv * x_sub.1.A * step.P) = step.tail := by
        unfold jordanBlockSlice
        rw [hblock]
        ext i j
        simp [jordanBlockDiagLex, Matrix.toBlocks₂₂, Matrix.reindex_apply]
      rw [htail]
      exact hblock
  exact {
    β := step.blockIdx
    γ := step.tailIdx
    ready := hReady
  }

/-- Concrete RCF prime-power block step as generalized-Jordan driver data. -/
noncomputable def generalizedJordanRCFBlockDriverStepData
    {K : Type u} [Field K]
    (x_sub : PosSquareUniverse K) :
    GeneralizedJordanBlockDriverStepData x_sub := by
  classical
  letI : Nonempty x_sub.1.ι := posSquareUniverse_nonempty x_sub
  let data := rationalCanonicalPolynomialModuleData x_sub.1.A
  let decomposition :=
    rationalCanonicalPolynomialModuleDecompositionData x_sub.1.A data
  let selected :=
    rationalCanonicalSelectedCyclicSummandBridgeOfEffectiveIndexBridge
      (rationalCanonicalEffectiveSummandIndexBridge K) |>.select
        x_sub.1.A data decomposition
  let stepData :=
    (rationalCanonicalPolynomialBlockBridge K).stepData
      x_sub.1.A data decomposition selected
  exact {
    B := stepData.step.Pinv * x_sub.1.A * stepData.step.P
    P := stepData.step.P
    invertible_P := by
      exact ⟨⟨stepData.step.P, stepData.step.Pinv,
        stepData.step.inverse_P.2, stepData.step.inverse_P.1⟩, rfl⟩
    B_eq := by
      have hInvUnit : InvertibleMatrix stepData.step.P := by
        exact ⟨⟨stepData.step.P, stepData.step.Pinv,
          stepData.step.inverse_P.2, stepData.step.inverse_P.1⟩, rfl⟩
      haveI : Invertible stepData.step.P := hInvUnit.invertible
      have hPinv : stepData.step.P⁻¹ = stepData.step.Pinv :=
        Matrix.inv_eq_left_inv stepData.step.inverse_P.1
      simp [hPinv]
    witness :=
      generalizedJordanRCFBlockSliceWitness x_sub
        data decomposition selected stepData
  }

/-- Concrete RCF-backed generalized-Jordan block driver. -/
noncomputable def generalizedJordanRCFBlockDriverBridge
    (K : Type u) [Field K] :
    GeneralizedJordanBlockDriverBridge K where
  step := generalizedJordanRCFBlockDriverStepData

/--
Framework-routed generalized Jordan theorem through the concrete RCF
prime-power block driver.
-/
theorem exists_generalized_jordan_matrix
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasGeneralizedJordanMatrix A :=
  exists_generalized_jordan_matrix_framework_bridge
    (generalizedJordanRCFBlockDriverBridge K) A

end MatDecompFormal.Instances
