import MatDecompFormal.Components.Lifting.Generic

namespace MatDecompFormal.Components

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Components.Properties

/-!
# Permutation/UnitLower/Upper Lifting Wrappers

This file packages the generic lifting cores for the recurring
permutation-unitLower-upper factor profile used by instance code such as PLU.
-/

section GenericLifting

variable {k : ℕ} {R : Type*} [Field R]

/--
Instance-friendly Schur lifting wrapper for
`IsPermutation × IsUnitLowerTriangular × IsUpperTriangular`.
-/
noncomputable def lift_permutation_unitLower_upper_schur
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (h_pivot_unit : IsUnit (A 0 0))
    (subP subL subU : Matrix (Fin k) (Fin k) R)
    (h_subP : IsPermutation subP)
    (h_subL : IsUnitLowerTriangular subL)
    (h_subU : IsUpperTriangular subU)
    (h_slice_eq : subP * ((Reductions.SchurMethod k R).slice A h_pivot_unit) = subL * subU) :
    { res :
        Matrix (Fin (k + 1)) (Fin (k + 1)) R ×
          Matrix (Fin (k + 1)) (Fin (k + 1)) R ×
          Matrix (Fin (k + 1)) (Fin (k + 1)) R //
      IsPermutation res.1 ∧
        IsUnitLowerTriangular res.2.1 ∧
        IsUpperTriangular res.2.2 ∧
        res.1 * A = res.2.1 * res.2.2 } := by
  classical
  have hP_id : IsPermutation (1 : Matrix (Fin 1) (Fin 1) R) := by
    dsimp [IsPermutation]
    refine ⟨Equiv.refl (Fin 1), ?_⟩
    simp
  have hP_blk_sum :
      IsPermutation
        (fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subP :
          Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R) := by
    exact
      (isPermutation_fromBlocks_blockDiag_iff
        (P₁₁ := (1 : Matrix (Fin 1) (Fin 1) R)) (P₂₂ := subP)).2 ⟨hP_id, h_subP⟩
  have hP_blk :
      @IsPermutation (Fin 1 ⊕ₗ Fin k) R _ (Classical.decEq (Fin 1 ⊕ₗ Fin k))
        ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subP :
          Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex) := by
    have hP_blk_lex :
        IsPermutation
          ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subP :
            Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex) := by
      exact (isPermutation_reindex (e := toLex) (A := _)).1 hP_blk_sum
    exact
      (isPermutation_decEq_irrel
        (d₁ := instDecidableEqLex (Fin 1 ⊕ Fin k))
        (d₂ := Classical.decEq (Fin 1 ⊕ₗ Fin k))
        (A := ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subP :
          Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex))).1 hP_blk_lex
  have hL_blk :
      IsUnitLowerTriangular
        ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0
          (subP *
            (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₂₁ *
              !![(IsUnit.unit h_pivot_unit).inv])
          subL : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex) := by
    simpa using
      (isUnitLowerTriangular_fromBlocks_one_zero_toLex (n₁ := 1) (n₂ := k)
        (L₂₁ := subP *
          (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₂₁ *
            !![(IsUnit.unit h_pivot_unit).inv])
        (L' := subL) h_subL)
  have hA₁₁_ut :
      IsUpperTriangular
        ((Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₁) := by
    simpa using
      (isUpperTriangular_of_subsingleton
        (A := (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₁))
  have hU_blk :
      IsUpperTriangular
        ((fromBlocks
          (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₁
          (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₂
          0 subU : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex) := by
    simpa using
      (isUpperTriangular_fromBlocks_toLex (n₁ := 1) (n₂ := k)
        (A₁₁ := (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₁)
        (A₁₂ := (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₂)
        (A₂₂ := subU) hA₁₁_ut h_subU)
  rcases
      lift_schur_pattern
        (R := R) (k := k)
        (PropF₁ := fun {ι} M => @IsPermutation ι R _ (Classical.decEq ι) M)
        (PropF₂ := fun {ι} [LinearOrder ι] M => IsUnitLowerTriangular M)
        (PropF₃ := fun {ι} [LinearOrder ι] M => IsUpperTriangular M)
        (h_reindexF₁ := by
          intro ι ι' e M
          classical
          exact isPermutation_reindex (e := e) (A := M))
        (h_reindexF₂ := by
          intro ι ι' _ _ e h_mono M
          exact isUnitLowerTriangular_reindex (e := e) (h_mono := h_mono) (A := M))
        (h_reindexF₃ := by
          intro ι ι' _ _ e h_mono M
          exact isUpperTriangular_reindex (e := e) (h_mono := h_mono) (A := M))
        (A := A) (h_pivot_unit := h_pivot_unit)
        (subF₁ := subP) (subF₂ := subL) (subF₃ := subU)
        hP_blk hL_blk hU_blk h_slice_eq with
    ⟨lifted, h_eq⟩
  let hF₁_std : IsPermutation lifted.F₁ :=
    (isPermutation_decEq_irrel
      (d₁ := Classical.decEq (Fin (k + 1)))
      (d₂ := instDecidableEqFin (k + 1))
      (A := lifted.F₁)).1 lifted.hF₁
  exact
    ⟨(lifted.F₁, lifted.F₂, lifted.F₃),
      ⟨hF₁_std, lifted.hF₂, lifted.hF₃, h_eq⟩⟩

/--
Instance-friendly zero-column lifting wrapper for
`IsPermutation × IsUnitLowerTriangular × IsUpperTriangular`.
-/
noncomputable def lift_permutation_unitLower_upper_zero_col
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (h_zero_col : ∀ i, A i 0 = 0)
    (subP subL subU : Matrix (Fin k) (Fin k) R)
    (h_subP : IsPermutation subP)
    (h_subL : IsUnitLowerTriangular subL)
    (h_subU : IsUpperTriangular subU)
    (h_slice_eq : subP * ((Reductions.ZeroColumnMethod k k R).slice A h_zero_col) = subL * subU) :
    { res :
        Matrix (Fin (k + 1)) (Fin (k + 1)) R ×
          Matrix (Fin (k + 1)) (Fin (k + 1)) R ×
          Matrix (Fin (k + 1)) (Fin (k + 1)) R //
      IsPermutation res.1 ∧
        IsUnitLowerTriangular res.2.1 ∧
        IsUpperTriangular res.2.2 ∧
        res.1 * A = res.2.1 * res.2.2 } := by
  classical
  have hP_id : IsPermutation (1 : Matrix (Fin 1) (Fin 1) R) := by
    dsimp [IsPermutation]
    refine ⟨Equiv.refl (Fin 1), ?_⟩
    simp
  have hP_blk_sum :
      IsPermutation
        (fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subP :
          Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R) := by
    exact
      (isPermutation_fromBlocks_blockDiag_iff
        (P₁₁ := (1 : Matrix (Fin 1) (Fin 1) R)) (P₂₂ := subP)).2 ⟨hP_id, h_subP⟩
  have hP_blk :
      @IsPermutation (Fin 1 ⊕ₗ Fin k) R _ (Classical.decEq (Fin 1 ⊕ₗ Fin k))
        ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subP :
          Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex) := by
    have hP_blk_lex :
        IsPermutation
          ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subP :
            Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex) := by
      exact (isPermutation_reindex (e := toLex) (A := _)).1 hP_blk_sum
    exact
      (isPermutation_decEq_irrel
        (d₁ := instDecidableEqLex (Fin 1 ⊕ Fin k))
        (d₂ := Classical.decEq (Fin 1 ⊕ₗ Fin k))
        (A := ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subP :
          Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex))).1 hP_blk_lex
  have hL_blk :
      IsUnitLowerTriangular
        ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subL :
          Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex) := by
    simpa using
      (isUnitLowerTriangular_fromBlocks_one_zero_toLex (n₁ := 1) (n₂ := k)
        (L₂₁ := (0 : Matrix (Fin k) (Fin 1) R)) (L' := subL) h_subL)
  have hU_blk :
      IsUpperTriangular
        ((fromBlocks 0
          (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₂
          0 subU : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex) := by
    simpa using
      (isUpperTriangular_fromBlocks_zero_top_toLex (n₁ := 1) (n₂ := k)
        (A₁₂ := (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₂)
        (A₂₂ := subU) h_subU)
  rcases
      lift_zero_col_pattern
        (R := R) (k := k)
        (PropF₁ := fun {ι} M => @IsPermutation ι R _ (Classical.decEq ι) M)
        (PropF₂ := fun {ι} [LinearOrder ι] M => IsUnitLowerTriangular M)
        (PropF₃ := fun {ι} [LinearOrder ι] M => IsUpperTriangular M)
        (h_reindexF₁ := by
          intro ι ι' e M
          classical
          exact isPermutation_reindex (e := e) (A := M))
        (h_reindexF₂ := by
          intro ι ι' _ _ e h_mono M
          exact isUnitLowerTriangular_reindex (e := e) (h_mono := h_mono) (A := M))
        (h_reindexF₃ := by
          intro ι ι' _ _ e h_mono M
          exact isUpperTriangular_reindex (e := e) (h_mono := h_mono) (A := M))
        (A := A) (h_zero_col := h_zero_col)
        (subF₁ := subP) (subF₂ := subL) (subF₃ := subU)
        hP_blk hL_blk hU_blk h_slice_eq with
    ⟨lifted, h_eq⟩
  let hF₁_std : IsPermutation lifted.F₁ :=
    (isPermutation_decEq_irrel
      (d₁ := Classical.decEq (Fin (k + 1)))
      (d₂ := instDecidableEqFin (k + 1))
      (A := lifted.F₁)).1 lifted.hF₁
  exact
    ⟨(lifted.F₁, lifted.F₂, lifted.F₃),
      ⟨hF₁_std, lifted.hF₂, lifted.hF₃, h_eq⟩⟩

end GenericLifting

end MatDecompFormal.Components
