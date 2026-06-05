import MatDecompFormal.Instances.Jordan.Direct
import MatDecompFormal.Instances.RationalCanonical.BlockStrategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open scoped Polynomial

/-!
# Jordan Form: Framework Entry

This file assembles the Jordan descent strategy through the project square
descent framework.  The theorem is conditional on `JordanStepOracle`;
constructing that oracle from rational canonical form or primary decomposition
is the remaining algebraic work.
-/

/-- Universe-level base case for the Jordan target. -/
theorem jordan_base_univ
    {K : Type u} [Field K] (x : SquareUniverse K) :
    ((∀ (x_sub : PosSquareUniverse K), (x_sub : SquareUniverse K) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      Jordan_P x := by
  intro hx _hsplit
  have hzero : Fintype.card x.ι = 0 :=
    squareSubtypeBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  exact base_jordan_empty x.A

/--
Block-slice witness for a positive square-universe object.

This is the sliceability payload: it depends on the actual matrix being sliced,
and therefore supports matrix-dependent block/complement types.
-/
structure JordanBlockSliceWitness
    {K : Type u} [Field K] (x_sub : PosSquareUniverse K) where
  β : Type u
  [fintype_β : Fintype β]
  [decEq_β : DecidableEq β]
  [linOrder_β : LinearOrder β]
  γ : Type u
  [fintype_γ : Fintype γ]
  [decEq_γ : DecidableEq γ]
  [linOrder_γ : LinearOrder γ]
  ready : JordanBlockStepReady K x_sub.1.ι β γ x_sub.1.A

attribute [instance] JordanBlockSliceWitness.fintype_β
attribute [instance] JordanBlockSliceWitness.decEq_β
attribute [instance] JordanBlockSliceWitness.linOrder_β
attribute [instance] JordanBlockSliceWitness.fintype_γ
attribute [instance] JordanBlockSliceWitness.decEq_γ
attribute [instance] JordanBlockSliceWitness.linOrder_γ

/-- The square-universe recursive slice selected by a block-slice witness. -/
noncomputable def JordanBlockSliceWitness.slice
    {K : Type u} [Field K] {x_sub : PosSquareUniverse K}
    (w : JordanBlockSliceWitness x_sub) :
    SquareUniverse K :=
  { ι := w.γ
    A := jordanBlockSlice w.ready.e x_sub.1.A }

/--
One dependent block-descent step for a positive square-universe object.

The transformed matrix has the same ambient index as `x_sub`; its recursive
slice may have a matrix-dependent complement type.
-/
structure JordanBlockDriverStepData
    {K : Type u} [Field K] (x_sub : PosSquareUniverse K) where
  B : Matrix x_sub.1.ι x_sub.1.ι K
  P : Matrix x_sub.1.ι x_sub.1.ι K
  invertible_P : InvertibleMatrix P
  B_eq : B = P⁻¹ * x_sub.1.A * P
  witness :
    JordanBlockSliceWitness
      (⟨SquareUniverse.ofMatrix B, by simpa using x_sub.2⟩ : PosSquareUniverse K)

/-- The transformed positive universe object produced by a block-driver step. -/
noncomputable def JordanBlockDriverStepData.target
    {K : Type u} [Field K] {x_sub : PosSquareUniverse K}
    (data : JordanBlockDriverStepData x_sub) :
    PosSquareUniverse K :=
  ⟨SquareUniverse.ofMatrix data.B, by simpa using x_sub.2⟩

/-- Block-driver oracle: every positive object has a concrete block step. -/
structure JordanBlockDriverOracle
    (K : Type u) [Field K] : Type (u + 1) where
  step : ∀ (x_sub : PosSquareUniverse K), JordanBlockDriverStepData x_sub

/-- Convert an explicit two-sided inverse into the public matrix invertibility predicate. -/
lemma invertibleMatrix_of_hasMatrixInverse
    {K : Type u} [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {P Pinv : Matrix ι ι K}
    (hInv : HasMatrixInverse P Pinv) :
    InvertibleMatrix P := by
  exact ⟨⟨P, Pinv, hInv.2, hInv.1⟩, rfl⟩

/--
Structured companion-block bridge for the RCF-to-Jordan route.

This is the real algebraic obligation for a cyclic RCF head block: a companion
matrix for a split polynomial has Jordan form.  It is intentionally more
specific than an arbitrary Jordan step oracle.
-/
structure JordanCompanionBlockBridge
    (K : Type u) [Field K] : Type (u + 1) where
  companion_hasJordan_of_splits :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
      {C : Matrix ι ι K} {p : K[X]},
      SingleCompanionBlockForm C p →
        p.Splits (RingHom.id K) →
          HasJordanMatrix C

/--
Split-aware RCF bridge for the Jordan block driver.

The selected cyclic annihilator is an internal invariant-factor object.  This
bridge records the usable API needed by the recursive driver: whenever the
current recursive matrix has split characteristic polynomial, the selected
annihilator also splits, so the companion head block can be converted to a
Jordan block.
-/
structure JordanRCFSplitBlockBridge
    (K : Type u) [Field K] : Type (u + 1) where
  rcfOracle : RationalCanonicalBlockStepOracle.{u, u} K
  cyclic_annihilator_splits :
    ∀ (x_sub : PosSquareUniverse K)
      (_hsplit : x_sub.1.A.charpoly.Splits (RingHom.id K)),
      let step := rationalCanonicalBlockStep rcfOracle x_sub
      step.cyclic_annihilator.Splits (RingHom.id K)
  companionBridge : JordanCompanionBlockBridge K

/--
Sharper RCF bridge target: prove the selected cyclic annihilator divides the
current characteristic polynomial.

Together with `A.charpoly.Splits`, this mechanically yields the split condition
required by `JordanRCFSplitBlockBridge`.  This keeps the remaining RCF algebra
focused on the invariant-factor divisibility theorem.
-/
structure JordanRCFAnnihilatorDivisibilityBridge
    (K : Type u) [Field K] : Type (u + 1) where
  rcfOracle : RationalCanonicalBlockStepOracle.{u, u} K
  cyclic_annihilator_dvd_charpoly :
    ∀ (x_sub : PosSquareUniverse K),
      let step := rationalCanonicalBlockStep rcfOracle x_sub
      step.cyclic_annihilator ∣ x_sub.1.A.charpoly
  companionBridge : JordanCompanionBlockBridge K

/-- Divisibility of the selected cyclic annihilator supplies the split-aware RCF bridge. -/
noncomputable def JordanRCFAnnihilatorDivisibilityBridge.toSplitBlockBridge
    {K : Type u} [Field K]
    (bridge : JordanRCFAnnihilatorDivisibilityBridge K) :
    JordanRCFSplitBlockBridge K where
  rcfOracle := bridge.rcfOracle
  cyclic_annihilator_splits := by
    intro x_sub hsplit
    let step := rationalCanonicalBlockStep bridge.rcfOracle x_sub
    exact Polynomial.splits_of_splits_of_dvd (RingHom.id K)
      (Matrix.charpoly_monic x_sub.1.A).ne_zero
      hsplit
      (bridge.cyclic_annihilator_dvd_charpoly x_sub)
  companionBridge := bridge.companionBridge

/--
In an RCF cyclic block step, the selected head block characteristic polynomial
divides the characteristic polynomial of the current matrix.

This follows only from the block equation and similarity invariance.  The
remaining RCF/Jordan algebra is to identify the companion head characteristic
polynomial with the selected cyclic annihilator.
-/
theorem rationalCanonicalBlockStep_head_charpoly_dvd_charpoly
    {K : Type u} [Field K]
    (oracle : RationalCanonicalBlockStepOracle.{u, u} K)
    (x_sub : PosSquareUniverse K) :
    let step := rationalCanonicalBlockStep oracle x_sub
    step.head.charpoly ∣ x_sub.1.A.charpoly := by
  classical
  let step := rationalCanonicalBlockStep oracle x_sub
  let B : Matrix x_sub.1.ι x_sub.1.ι K := step.Pinv * x_sub.1.A * step.P
  have hInvUnit : InvertibleMatrix step.P :=
    invertibleMatrix_of_hasMatrixInverse step.inverse_P
  have hPinv : step.P⁻¹ = step.Pinv := by
    haveI : Invertible step.P := hInvUnit.invertible
    exact Matrix.inv_eq_left_inv step.inverse_P.1
  have hcharB : B.charpoly = x_sub.1.A.charpoly := by
    simpa [B, hPinv] using
      (jordan_similarity_charpoly
        (P := step.P)
        (A := x_sub.1.A)
        hInvUnit)
  have hcharReindex :
      (Matrix.reindex step.splitIndex step.splitIndex B).charpoly = B.charpoly := by
    exact Matrix.charpoly_reindex step.splitIndex B
  have hcharBlock :
      (rationalCanonicalBlockDiagLex step.head step.tail).charpoly =
        step.head.charpoly * step.tail.charpoly := by
    calc
      (rationalCanonicalBlockDiagLex step.head step.tail).charpoly =
          (Matrix.fromBlocks step.head 0 0 step.tail :
            Matrix (step.blockIdx ⊕ step.tailIdx) (step.blockIdx ⊕ step.tailIdx) K).charpoly := by
        simpa [rationalCanonicalBlockDiagLex] using
          Matrix.charpoly_reindex
            (sumToLexEquiv step.blockIdx step.tailIdx)
            (Matrix.fromBlocks step.head 0 0 step.tail :
              Matrix (step.blockIdx ⊕ step.tailIdx) (step.blockIdx ⊕ step.tailIdx) K)
      _ = step.head.charpoly * step.tail.charpoly := by
        simp
  have hprod : step.head.charpoly * step.tail.charpoly = x_sub.1.A.charpoly := by
    rw [← hcharBlock, ← step.block_eq, hcharReindex, hcharB]
  exact ⟨step.tail.charpoly, hprod.symm⟩

/--
Companion-head characteristic polynomial bridge for the RCF step.

After `rationalCanonicalBlockStep_head_charpoly_dvd_charpoly`, proving this
bridge is enough to obtain the selected-annihilator divisibility bridge.
-/
structure JordanRCFCompanionCharpolyBridge
    (K : Type u) [Field K] : Type (u + 1) where
  rcfOracle : RationalCanonicalBlockStepOracle.{u, u} K
  companion_head_charpoly :
    ∀ (x_sub : PosSquareUniverse K),
      let step := rationalCanonicalBlockStep rcfOracle x_sub
      step.head.charpoly = step.cyclic_annihilator
  companionBridge : JordanCompanionBlockBridge K

/-- The companion-head charpoly bridge supplies selected-annihilator divisibility. -/
noncomputable def JordanRCFCompanionCharpolyBridge.toAnnihilatorDivisibilityBridge
    {K : Type u} [Field K]
    (bridge : JordanRCFCompanionCharpolyBridge K) :
    JordanRCFAnnihilatorDivisibilityBridge K where
  rcfOracle := bridge.rcfOracle
  cyclic_annihilator_dvd_charpoly := by
    intro x_sub
    let step := rationalCanonicalBlockStep bridge.rcfOracle x_sub
    have hhead_dvd :
        step.head.charpoly ∣ x_sub.1.A.charpoly :=
      rationalCanonicalBlockStep_head_charpoly_dvd_charpoly bridge.rcfOracle x_sub
    simpa [(bridge.companion_head_charpoly x_sub).symm] using hhead_dvd
  companionBridge := bridge.companionBridge

/--
The split-dependent block-slice witness selected by an RCF cyclic block.

This is deliberately not a split-independent `JordanBlockDriverStepData`: the
head Jordan witness is obtained from the current recursive split hypothesis.
-/
noncomputable def JordanRCFSplitBlockBridge.blockSliceWitness
    {K : Type u} [Field K]
    (bridge : JordanRCFSplitBlockBridge K)
    (x_sub : PosSquareUniverse K)
    (hsplit : x_sub.1.A.charpoly.Splits (RingHom.id K)) :
    JordanBlockSliceWitness
      (⟨SquareUniverse.ofMatrix
        (rationalCanonicalBlockStepMatrix bridge.rcfOracle x_sub),
        by simpa [rationalCanonicalBlockStepMatrix] using x_sub.2⟩ :
        PosSquareUniverse K) := by
  classical
  let step := rationalCanonicalBlockStep bridge.rcfOracle x_sub
  let B : Matrix x_sub.1.ι x_sub.1.ι K := step.Pinv * x_sub.1.A * step.P
  have hHeadJordan : HasJordanMatrix step.head :=
    bridge.companionBridge.companion_hasJordan_of_splits
      step.head_companion
      (bridge.cyclic_annihilator_splits x_sub hsplit)
  have hReady :
      JordanBlockStepReady K x_sub.1.ι step.blockIdx step.tailIdx B := by
    refine {
      e := step.splitIndex
      head := step.head
      head_hasJordan := hHeadJordan
      head_nonempty := ?_
      block_eq := ?_
    }
    · exact Fintype.card_pos_iff.mp (by
        rw [step.block_card_eq]
        exact step.cyclic_blockSize_pos)
    · have hblock :
          Matrix.reindex step.splitIndex step.splitIndex B =
            jordanBlockDiagLex step.head step.tail := by
        simpa [B, rationalCanonicalBlockDiagLex, jordanBlockDiagLex] using
          step.block_eq
      have htail : jordanBlockSlice step.splitIndex B = step.tail := by
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

/--
Split-dependent proof hooks for the RCF-backed Jordan block driver.

The slicing data remains structural, while the witness is constructed inside
the lift hook from the current matrix's split hypothesis.
-/
noncomputable def jordan_rcf_split_block_proofData
    (K : Type u) [Field K]
    (bridge : JordanRCFSplitBlockBridge K) :
    SquareProofData Jordan_P
      (rationalCanonicalBlockSliceData bridge.rcfOracle) where
  transport_sub := by
    intro x_sub y_sub hrel hPy hsplitX
    subst y_sub
    have hsplitB :
        (rationalCanonicalBlockStepMatrix bridge.rcfOracle x_sub).charpoly.Splits
          (RingHom.id K) := by
      let step := rationalCanonicalBlockStep bridge.rcfOracle x_sub
      have hchar :
          (rationalCanonicalBlockStepMatrix bridge.rcfOracle x_sub).charpoly =
            x_sub.1.A.charpoly := by
        have hInvUnit : InvertibleMatrix step.P :=
          invertibleMatrix_of_hasMatrixInverse step.inverse_P
        have hPinv : step.P⁻¹ = step.Pinv := by
          haveI : Invertible step.P := hInvUnit.invertible
          exact Matrix.inv_eq_left_inv step.inverse_P.1
        simpa [rationalCanonicalBlockStepMatrix, hPinv] using
          (jordan_similarity_charpoly
            (P := step.P)
            (A := x_sub.1.A)
            hInvUnit)
      simpa [hchar] using hsplitX
    have hJordanB :
        HasJordanMatrix (rationalCanonicalBlockStepMatrix bridge.rcfOracle x_sub) :=
      hPy hsplitB
    let step := rationalCanonicalBlockStep bridge.rcfOracle x_sub
    have hInvUnit : InvertibleMatrix step.P :=
      invertibleMatrix_of_hasMatrixInverse step.inverse_P
    have hPinv : step.P⁻¹ = step.Pinv := by
      haveI : Invertible step.P := hInvUnit.invertible
      exact Matrix.inv_eq_left_inv step.inverse_P.1
    exact jordan_transport_similarity
      hInvUnit
      (by simp [rationalCanonicalBlockStepMatrix, step, hPinv])
      hJordanB
  lift_from_slice_sub := by
    intro y_sub _ hSlice hsplitY
    let step := rationalCanonicalBlockStep bridge.rcfOracle y_sub
    let B : Matrix y_sub.1.ι y_sub.1.ι K := step.Pinv * y_sub.1.A * step.P
    have hHeadJordan : HasJordanMatrix step.head :=
      bridge.companionBridge.companion_hasJordan_of_splits
        step.head_companion
        (bridge.cyclic_annihilator_splits y_sub hsplitY)
    let hReady :
        JordanBlockStepReady K y_sub.1.ι step.blockIdx step.tailIdx B := {
      e := step.splitIndex
      head := step.head
      head_hasJordan := hHeadJordan
      head_nonempty := Fintype.card_pos_iff.mp (by
        rw [step.block_card_eq]
        exact step.cyclic_blockSize_pos)
      block_eq := by
        have hblock :
            Matrix.reindex step.splitIndex step.splitIndex B =
              jordanBlockDiagLex step.head step.tail := by
          simpa [B, rationalCanonicalBlockDiagLex, jordanBlockDiagLex] using
            step.block_eq
        have htail : jordanBlockSlice step.splitIndex B = step.tail := by
          unfold jordanBlockSlice
          rw [hblock]
          ext i j
          simp [jordanBlockDiagLex, Matrix.toBlocks₂₂, Matrix.reindex_apply]
        rw [htail]
        exact hblock
    }
    have hTail' :
        (jordanBlockSlice hReady.e B).charpoly.Splits (RingHom.id K) →
          HasJordanMatrix (jordanBlockSlice hReady.e B) := by
      intro hsplitTail
      change
        HasJordanMatrix (jordanBlockSlice step.splitIndex B)
      change
        (jordanBlockSlice step.splitIndex B).charpoly.Splits (RingHom.id K)
        at hsplitTail
      have htail : jordanBlockSlice hReady.e B = step.tail := by
        change jordanBlockSlice step.splitIndex B = step.tail
        unfold jordanBlockSlice
        have hblock :
            Matrix.reindex step.splitIndex step.splitIndex B =
              jordanBlockDiagLex step.head step.tail := by
          simpa [B, rationalCanonicalBlockDiagLex, jordanBlockDiagLex] using
            step.block_eq
        rw [hblock]
        ext i j
        simp [jordanBlockDiagLex, Matrix.toBlocks₂₂, Matrix.reindex_apply]
      have hsplitTail' : step.tail.charpoly.Splits (RingHom.id K) := by
        rwa [htail] at hsplitTail
      have hTailJordan : HasJordanMatrix step.tail := by
        exact hSlice hsplitTail'
      rwa [htail]
    have hInvUnit : InvertibleMatrix step.P :=
      invertibleMatrix_of_hasMatrixInverse step.inverse_P
    have hPinv : step.P⁻¹ = step.Pinv := by
      haveI : Invertible step.P := hInvUnit.invertible
      exact Matrix.inv_eq_left_inv step.inverse_P.1
    have hsplitB : B.charpoly.Splits (RingHom.id K) := by
      have hchar : B.charpoly = y_sub.1.A.charpoly := by
        simpa [B, hPinv] using
          (jordan_similarity_charpoly
            (P := step.P)
            (A := y_sub.1.A)
            hInvUnit)
      simpa [hchar] using hsplitY
    have hJordanB : HasJordanMatrix B :=
      jordanLiftReady_of_blockStepReady hReady hTail' hsplitB
    exact jordan_transport_similarity
      hInvUnit
      (by simp [B, hPinv])
      hJordanB

/-- RCF-backed split block Jordan induction instance. -/
noncomputable def jordan_rcf_split_block_framework_inst
    (K : Type u) [Field K]
    (bridge : JordanRCFSplitBlockBridge K) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstance
    Jordan_P
    jordan_base_univ
    (rationalCanonicalBlockSliceData bridge.rcfOracle)
    (rationalCanonicalBlockReach bridge.rcfOracle)
    (jordan_rcf_split_block_proofData K bridge)

/--
Framework-routed Jordan theorem from a split-aware RCF block bridge.

This is still conditional on the two algebraic bridge obligations recorded in
`JordanRCFSplitBlockBridge`, but the recursion itself is fully routed through
the dependent block subtype-descent template.
-/
theorem exists_jordan_matrix_framework_rcf_split_bridge
    {K : Type u} [Field K]
    (bridge : JordanRCFSplitBlockBridge K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  have hP :
      (jordan_rcf_split_block_framework_inst K bridge).P
        (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := jordan_rcf_split_block_framework_inst K bridge) A
  exact hP hsplit

/--
Framework-routed Jordan theorem from an RCF annihilator-divisibility bridge.

This is the preferred conditional RCF API: the remaining RCF-side obligation is
the invariant-factor divisibility theorem
`step.cyclic_annihilator ∣ A.charpoly`; splitness is then derived automatically
from the public `A.charpoly.Splits` hypothesis.
-/
theorem exists_jordan_matrix_framework_rcf_divisibility_bridge
    {K : Type u} [Field K]
    (bridge : JordanRCFAnnihilatorDivisibilityBridge K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A :=
  exists_jordan_matrix_framework_rcf_split_bridge
    bridge.toSplitBlockBridge A hsplit

/-- Slice data for the dependent Jordan block driver. -/
noncomputable def jordan_block_sliceData
    (K : Type u) [Field K] :
    SquareSliceData K where
  r_sub := fun y_sub x_sub =>
    ∃ data : JordanBlockDriverStepData x_sub, y_sub = data.target
  IsSliceable_sub := fun y_sub =>
    Nonempty (JordanBlockSliceWitness y_sub)
  slice_sub := fun _y_sub hy =>
    let w := Classical.choice hy
    w.slice

/-- Reachability for the dependent Jordan block driver. -/
noncomputable def jordan_block_reach
    (K : Type u) [Field K]
    (oracle : JordanBlockDriverOracle K) :
    ∀ (x_sub : PosSquareUniverse K),
      squareSubtypeμ (x_sub : SquareUniverse K) > squareSubtypeμBase →
        SquareReachType (jordan_block_sliceData K) x_sub := by
  intro x_sub _hgt
  let data := oracle.step x_sub
  let y_sub : PosSquareUniverse K := data.target
  have hySlice : (jordan_block_sliceData K).IsSliceable_sub y_sub := by
    exact ⟨data.witness⟩
  refine ⟨y_sub, hySlice, ?_, ?_⟩
  · refine ⟨data, ?_⟩
    rfl
  · change Fintype.card (Classical.choice hySlice).γ < Fintype.card x_sub.1.ι
    have hready :
        Fintype.card (Classical.choice hySlice).γ <
          Fintype.card y_sub.1.ι :=
      jordan_block_slice_card_lt (Classical.choice hySlice).ready
    simpa [y_sub, JordanBlockDriverStepData.target] using hready

/-- Proof hooks for the dependent Jordan block driver. -/
noncomputable def jordan_block_proofData
    (K : Type u) [Field K] :
    SquareProofData Jordan_P (jordan_block_sliceData K) where
  transport_sub := by
    intro x_sub y_sub hrel hPy hsplitX
    rcases hrel with ⟨data, hy⟩
    have hsplitB :
        data.B.charpoly.Splits (RingHom.id K) := by
      have hchar : data.B.charpoly = x_sub.1.A.charpoly := by
        rw [data.B_eq]
        exact jordan_similarity_charpoly data.invertible_P
      simpa [hchar] using hsplitX
    have hJordanB : HasJordanMatrix data.B := by
      have hPy' : Jordan_P (SquareUniverse.ofMatrix data.B) := by
        simpa [hy, JordanBlockDriverStepData.target] using hPy
      exact hPy' hsplitB
    exact jordan_transport_similarity data.invertible_P data.B_eq hJordanB
  lift_from_slice_sub := by
    intro y_sub hy hSlice hsplitY
    let w := Classical.choice hy
    have hTail :
        w.slice.A.charpoly.Splits (RingHom.id K) →
          HasJordanMatrix w.slice.A := hSlice
    exact jordanLiftReady_of_blockStepReady w.ready hTail hsplitY

/-- Dependent block-driver Jordan induction instance. -/
noncomputable def jordan_block_framework_inst
    (K : Type u) [Field K]
    (oracle : JordanBlockDriverOracle K) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstance
    Jordan_P
    jordan_base_univ
    (jordan_block_sliceData K)
    (jordan_block_reach K oracle)
    (jordan_block_proofData K)

noncomputable def jordan_strategy_data
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        JordanStepOracle K ι) :
    SquareStrategyData K Jordan_P :=
  mkSquareStrategyData
    (jordan_strategy_core K oracle)
    (jordan_strategy_proof K oracle)

noncomputable def jordan_framework_inst
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        JordanStepOracle K ι) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstanceFromStrategy
    Jordan_P
    jordan_base_univ
    (jordan_strategy_data K oracle)

/--
Framework-routed Jordan theorem, conditional on the one-step Jordan oracle.
-/
theorem exists_jordan_matrix_framework
    {K : Type u} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        JordanStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  have hP :
      (jordan_framework_inst K oracle).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := jordan_framework_inst K oracle) A
  exact hP hsplit

/--
Framework-routed Jordan theorem, conditional on the concrete one-step oracle.

The unsuffixed `exists_jordan_matrix_of_splits` name is intentionally reserved
for the later theorem where this oracle is discharged from rational canonical
form, primary decomposition, or nilpotent Jordan chains.
-/
theorem exists_jordan_matrix_framework_oracle
    {K : Type u} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        JordanStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  exact exists_jordan_matrix_framework oracle A hsplit

/--
Framework-routed Jordan theorem, conditional on structured head-tail block
data.  This is the preferred conditional API while the one-step algebra is
being discharged: it exposes concrete block readiness and converts it to the
framework oracle internally.
-/
theorem exists_jordan_matrix_framework_structured_oracle
    {K : Type u} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        JordanStructuredStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  exact exists_jordan_matrix_framework
    (fun {κ} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ] =>
      (oracle (κ := κ)).toStepOracle)
    A hsplit

/--
Framework-routed Jordan theorem through the dependent block driver.  This is
the block-step analogue of `exists_jordan_matrix_framework_oracle`; it still
keeps the oracle explicit, but its oracle payload is concrete block-removal
data and the proof is assembled by `mkSquareSubtypeInductionInstance`.
-/
theorem exists_jordan_matrix_framework_block_oracle
    {K : Type u} [Field K]
    (oracle : JordanBlockDriverOracle K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A := by
  have hP :
      (jordan_block_framework_inst K oracle).P (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := jordan_block_framework_inst K oracle) A
  exact hP hsplit

end MatDecompFormal.Instances
