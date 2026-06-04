import MatDecompFormal.Components.Lifting.LowLevel
import MatDecompFormal.Components.Properties.Reindex
import MatDecompFormal.Components.Reductions.Submatrix
import MatDecompFormal.Instances.Schur.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Components
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Components.Properties
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework

/-!
# Schur Direct Hooks

This file packages the proof-side hooks for the Schur strategy. Similarity
transport is concrete; the block lift hook is kept explicit while the block
algebra is developed.
-/

/-- Transport a Schur witness backward across an invertible similarity. -/
theorem schur_transport_similarity
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {P A B : Matrix ι ι K}
    (hP : InvertibleMatrix P)
    (hB : B = P⁻¹ * A * P)
    (hSchurB : HasSchur B) :
    HasSchur A := by
  rcases hSchurB with ⟨S, T, hS, hT, hBT⟩
  refine ⟨P * S, T, ?_, hT, ?_⟩
  · exact hP.mul hS
  · haveI : Invertible P := hP.invertible
    haveI : Invertible S := hS.invertible
    calc
      A = P * B * P⁻¹ := by
        rw [hB]
        simp [Matrix.mul_assoc]
      _ = P * (S * T * S⁻¹) * P⁻¹ := by
        rw [hBT]
      _ = (P * S) * T * (P * S)⁻¹ := by
        rw [Matrix.mul_inv_rev]
        simp [Matrix.mul_assoc]

lemma invertibleMatrix_reindex
    {K α β : Type*} [Field K]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {P : Matrix α α K} (hP : InvertibleMatrix P) :
    InvertibleMatrix (Matrix.reindex e e P) := by
  haveI : Invertible P := hP.invertible
  let Q : Matrix β β K := Matrix.reindex e e P⁻¹
  have hmul : Matrix.reindex e e P * Q = 1 := by
    have h := congrArg (Matrix.reindex e e) (Matrix.mul_inv_of_invertible P)
    simpa [Q, Matrix.submatrix_mul_equiv] using h
  have hmul' : Q * Matrix.reindex e e P = 1 := by
    have h := congrArg (Matrix.reindex e e) (Matrix.inv_mul_of_invertible P)
    simpa [Q, Matrix.submatrix_mul_equiv] using h
  exact ⟨⟨Matrix.reindex e e P, Q, hmul, hmul'⟩, rfl⟩

lemma invertibleMatrix_blockDiag_one_plain
    {K β : Type*} [Field K] [Fintype β] [DecidableEq β]
    {P : Matrix β β K} (hP : InvertibleMatrix P) :
    InvertibleMatrix
      (fromBlocks (1 : Matrix Unit Unit K) 0 0 P :
        Matrix (Unit ⊕ β) (Unit ⊕ β) K) := by
  haveI : Invertible P := hP.invertible
  let Pblk : Matrix (Unit ⊕ β) (Unit ⊕ β) K :=
    fromBlocks (1 : Matrix Unit Unit K) 0 0 P
  let Qblk : Matrix (Unit ⊕ β) (Unit ⊕ β) K :=
    fromBlocks (1 : Matrix Unit Unit K) 0 0 P⁻¹
  have hmul : Pblk * Qblk = 1 := by
    simp [Pblk, Qblk, Matrix.fromBlocks_multiply, Matrix.mul_inv_of_invertible]
  have hmul' : Qblk * Pblk = 1 := by
    simp [Pblk, Qblk, Matrix.fromBlocks_multiply, Matrix.inv_mul_of_invertible]
  exact ⟨⟨Pblk, Qblk, hmul, hmul'⟩, rfl⟩

lemma invertibleMatrix_blockDiag_one
    {K β : Type*} [Field K] [Fintype β] [DecidableEq β]
    {P : Matrix β β K} (hP : InvertibleMatrix P) :
    InvertibleMatrix
      (fromBlocks (1 : Matrix Unit Unit K) 0 0 P :
        Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) K) := by
  let s : Unit ⊕ β ≃ Unit ⊕ₗ β := sumToLexEquiv Unit β
  have hplain :
      InvertibleMatrix
        (fromBlocks (1 : Matrix Unit Unit K) 0 0 P :
          Matrix (Unit ⊕ β) (Unit ⊕ β) K) :=
    invertibleMatrix_blockDiag_one_plain hP
  have hreindex :
      Matrix.reindex s s
        (fromBlocks (1 : Matrix Unit Unit K) 0 0 P :
          Matrix (Unit ⊕ β) (Unit ⊕ β) K) =
        (fromBlocks (1 : Matrix Unit Unit K) 0 0 P :
          Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) K) := by
    exact reindex_sumToLex_fromBlocks
      (A₁₁ := (1 : Matrix Unit Unit K)) (A₁₂ := 0) (A₂₁ := 0) (A₂₂ := P)
  rw [← hreindex]
  exact invertibleMatrix_reindex s hplain

lemma isUpperTriangular_schurBlock_plain
    {K β : Type*} [Zero K] [LinearOrder β]
    (A₁₁ : Matrix Unit Unit K) (A₁₂ : Matrix Unit β K)
    {T : Matrix β β K} (hT : IsUpperTriangular T) :
    IsUpperTriangular
      (fromBlocks A₁₁ A₁₂ 0 T : Matrix (Unit ⊕ β) (Unit ⊕ β) K) := by
  dsimp [IsUpperTriangular, BlockTriangular] at hT ⊢
  intro i j hij
  rcases i with (_ | i)
  · rcases j with (_ | j)
    · simpa using hij
    · exfalso
      exact Sum.not_inr_lt_inl hij
  · rcases j with (_ | j)
    · simp
    · exact hT (Sum.inr_lt_inr_iff.mp hij)

theorem schur_lift_from_ready
    {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K)
    (hready : SchurDescentReady K ι A)
    (hTail : HasSchur
      ((Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A).toBlocks₂₂)) :
    HasSchur A := by
  classical
  let e0 : ι ≃ Unit ⊕ SchurTailIdx ι := headTailEquiv (α := ι)
  let s : Unit ⊕ SchurTailIdx ι ≃ Unit ⊕ₗ SchurTailIdx ι :=
    sumToLexEquiv Unit (SchurTailIdx ι)
  let e : ι ≃ Unit ⊕ₗ SchurTailIdx ι := headTailLexEquiv (α := ι)
  let Aplain : Matrix (Unit ⊕ SchurTailIdx ι) (Unit ⊕ SchurTailIdx ι) K :=
    Matrix.reindex e0 e0 A
  let Ablk : Matrix (Unit ⊕ₗ SchurTailIdx ι) (Unit ⊕ₗ SchurTailIdx ι) K :=
    Matrix.reindex e e A
  have hAblk : Matrix.reindex s s Aplain = Ablk := by
    simpa [Aplain, Ablk, e0, e, s, headTailLexEquiv] using
      (reindex_reindex e0 e0 s s A)
  have hA21 : Ablk.toBlocks₂₁ = 0 := by
    have hplain : Aplain.toBlocks₂₁ = 0 := by
      simpa [SchurDescentReady, Aplain, e0] using hready
    have hconv := congrArg Matrix.toBlocks₂₁ hAblk
    rw [← hconv]
    exact hplain
  have hA22blk : Aplain.toBlocks₂₂ = Ablk.toBlocks₂₂ := by
    simpa using congrArg Matrix.toBlocks₂₂ hAblk
  rcases (show HasSchur Ablk.toBlocks₂₂ by
      simpa [Aplain] using hA22blk ▸ hTail) with
    ⟨P', T', hP', hT', hEq'⟩
  let Pblk : Matrix (Unit ⊕ₗ SchurTailIdx ι) (Unit ⊕ₗ SchurTailIdx ι) K :=
    fromBlocks (1 : Matrix Unit Unit K) 0 0 P'
  let Tblk : Matrix (Unit ⊕ₗ SchurTailIdx ι) (Unit ⊕ₗ SchurTailIdx ι) K :=
    fromBlocks Ablk.toBlocks₁₁ (Ablk.toBlocks₁₂ * P') 0 T'
  have hPblk : InvertibleMatrix Pblk := by
    exact invertibleMatrix_blockDiag_one (β := SchurTailIdx ι) hP'
  haveI : Invertible P' := hP'.invertible
  haveI : Invertible Pblk := hPblk.invertible
  have hPblk_inv :
      Pblk⁻¹ =
        (fromBlocks (1 : Matrix Unit Unit K) 0 0 P'⁻¹ :
          Matrix (Unit ⊕ₗ SchurTailIdx ι) (Unit ⊕ₗ SchurTailIdx ι) K) := by
    apply Matrix.inv_eq_right_inv
    simpa [Pblk] using
      (show
        (fromBlocks (1 : Matrix Unit Unit K) 0 0 P' :
            Matrix (Unit ⊕ₗ SchurTailIdx ι) (Unit ⊕ₗ SchurTailIdx ι) K) *
          (fromBlocks (1 : Matrix Unit Unit K) 0 0 P'⁻¹ :
            Matrix (Unit ⊕ₗ SchurTailIdx ι) (Unit ⊕ₗ SchurTailIdx ι) K) = 1 by
          simp [Matrix.fromBlocks_multiply, Matrix.mul_inv_of_invertible])
  have hA22 : Ablk.toBlocks₂₂ = P' * T' * P'⁻¹ := by
    simpa using hEq'
  have hAblkEq : Ablk = Pblk * Tblk * Pblk⁻¹ := by
    have hfrom :
        Ablk =
          (fromBlocks Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ 0 Ablk.toBlocks₂₂ :
            Matrix (Unit ⊕ₗ SchurTailIdx ι) (Unit ⊕ₗ SchurTailIdx ι) K) := by
      calc
        Ablk =
            (fromBlocks Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ Ablk.toBlocks₂₁ Ablk.toBlocks₂₂ :
              Matrix (Unit ⊕ₗ SchurTailIdx ι) (Unit ⊕ₗ SchurTailIdx ι) K) := by
              exact (fromBlocks_toBlocks Ablk).symm
        _ = (fromBlocks Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ 0 Ablk.toBlocks₂₂ :
              Matrix (Unit ⊕ₗ SchurTailIdx ι) (Unit ⊕ₗ SchurTailIdx ι) K) := by
              rw [hA21]
    rw [hfrom, hA22, hPblk_inv]
    have htop : Ablk.toBlocks₁₂ * P' * P'⁻¹ = Ablk.toBlocks₁₂ := by
      simpa using Matrix.mul_invOf_cancel_right Ablk.toBlocks₁₂ P'
    simp [Pblk, Tblk, htop, Matrix.fromBlocks_multiply, Matrix.mul_assoc]
  let P : Matrix ι ι K := Matrix.reindex e.symm e.symm Pblk
  let T : Matrix ι ι K := Matrix.reindex e.symm e.symm Tblk
  refine ⟨P, T, ?_, ?_, ?_⟩
  · exact invertibleMatrix_reindex e.symm hPblk
  · have hTblk : IsUpperTriangular Tblk := by
      dsimp [IsUpperTriangular, BlockTriangular, Tblk] at hT' ⊢
      intro i j hij
      rcases i with (_ | i)
      · rcases j with (_ | j)
        · simpa using hij
        · exfalso
          exact Sum.Lex.not_inr_lt_inl hij
      · rcases j with (_ | j)
        · simp
        · exact hT' (Sum.Lex.inr_lt_inr_iff.mp hij)
    exact
      (isUpperTriangular_reindex
        (e := e)
        (h_mono := headTailLexEquiv_strictMono (α := ι))
        (A := T)).2
        (by simpa [T] using hTblk)
  · have hback := congrArg (Matrix.reindex e.symm e.symm) hAblkEq
    simpa [P, T, Ablk, Matrix.submatrix_mul_equiv, Matrix.inv_reindex, Matrix.mul_assoc] using hback

/--
Proof hooks needed to turn the Schur strategy core into a
`SquareStrategyProofData` instance.
-/
structure SchurDescentHooks
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        SchurStepOracle K ι) where
  lift :
    SquareStrategyLiftType Schur_P (schur_strategy_core K oracle)

noncomputable def schur_lift_hook
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        SchurStepOracle K ι) :
    SquareStrategyLiftType Schur_P (schur_strategy_core K oracle) := by
  intro ι fι dι oι nι A hA hTail
  exact schur_lift_from_ready A hA (by
    simpa [schurHeadTailReduction, SubmatrixMethod, SchurTailIdx] using hTail)

noncomputable def schur_descent_hooks
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        SchurStepOracle K ι) :
    SchurDescentHooks K oracle where
  lift := schur_lift_hook K oracle

noncomputable def schur_transport_hook
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        SchurStepOracle K ι) :
    SquareStrategyTransportType Schur_P (schur_strategy_core K oracle) := by
  intro ι fι dι oι nι A B hrel hPB
  rcases hrel with hBA | hBA
  · subst B
    exact hPB
  · rcases hBA with ⟨t, rfl⟩
    exact schur_transport_similarity t.2 rfl hPB

noncomputable def schur_strategy_proof
    (K : Type u) [Field K]
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        SchurStepOracle K ι)
    (hooks : SchurDescentHooks K oracle) :
    SquareStrategyProofData K Schur_P (schur_strategy_core K oracle) where
  transport := schur_transport_hook K oracle
  lift := hooks.lift

end MatDecompFormal.Instances
