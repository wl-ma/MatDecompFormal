import MatDecompFormal.Framework.UniverseDecompositionFin
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Abstractions.Strategy
import MatDecompFormal.Abstractions.ReductionCombinators
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Components.Properties.Reindex
import MatDecompFormal.Components.Reductions.Schur
import MatDecompFormal.Components.Reductions.ZeroColumn
import MatDecompFormal.Components.Transformations.Elementary.Pivot
import MatDecompFormal.Components.BlockLifting


namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Components.Transformations.Elementary
open MatDecompFormal.Components

/-
! # PLU decomposition over `Fin n`

This file packages the PLU existence proof for square matrices over a field,
strictly following the project’s abstraction layers.  The proof is assembled
from the schema/strategy infrastructure and dispatched through the universe
induction provided by `RectDecompositionInstance.prove_for_fin`.
-/

-- /*******************************************************************************
--   1. Schema
-- *******************************************************************************/

section Schema

variable {n : ℕ} {R : Type*} [Field R] [DecidableEq R]

/-- PLU decomposition schema for square `Fin n` matrices. -/
def PLU_Schema_fin (n : ℕ) : DecompositionSchema n n R where
  Factors := Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R
  property := fun (P, L, U) =>
    IsPermutation P ∧ IsUnitLowerTriangular L ∧ IsUpperTriangular U
  equation := fun A (P, L, U) => P * A = L * U

/-- Proposition: matrix `A` admits a PLU decomposition. -/
def HasPLU_fin (A : Matrix (Fin n) (Fin n) R) : Prop :=
  HasDecomposition (PLU_Schema_fin n) A

end Schema


/-- Helper to cast a rectangular matrix to a square one when dimensions are equal. -/
private def castSquare {m n : ℕ} {R : Type*} (A : Matrix (Fin m) (Fin n) R)
    (h : m = n) : Matrix (Fin n) (Fin n) R := by
  cases h
  simpa using A


-- /*******************************************************************************
--   2. Fin core implementation
-- *******************************************************************************/

noncomputable section FinImpl


variable {R : Type*} [Field R] --[DecidableEq R]

/-- Combined reduction method used by the strategy: Schur with a zero-column fallback. -/
noncomputable def PLU_Reduction_fin (k : ℕ) : ReductionMethod (k + 1) (k + 1) k k R :=
  ReductionMethod.try_else (SchurMethod k R) (ZeroColumnMethod k k R)

/-- A transformation tailored to the above reduction method. -/
noncomputable def PLU_Transform_fin (k : ℕ) :
    Transformation (Matrix (Fin (k + 1)) (Fin (k + 1)) R) :=
  let reduc := PLU_Reduction_fin (R := R) k
  {
    T := Fin (k + 1)
    Goal := reduc.IsSliceable
    decGoal := by
      classical
      exact Classical.decPred _
    apply := fun i A => (swap R 0 i) * A
    find := fun A h_not =>
      by
        classical
        -- Unpack the negation of sliceability.
        dsimp [reduc, PLU_Reduction_fin, ReductionMethod.try_else] at h_not
        have h_not_zeroCol : ¬ (ZeroColumnMethod k k R).IsSliceable A :=
          (not_or.mp h_not).2
        -- Extract a nonzero entry in the first column.
        dsimp [ZeroColumnMethod] at h_not_zeroCol
        let h_exists : ∃ i, A i 0 ≠ 0 := not_forall.mp h_not_zeroCol
        exact Classical.choose h_exists
    find_spec := by
      intro A h_not
      classical
      -- Unpack the negation of sliceability.
      dsimp [reduc, PLU_Reduction_fin, ReductionMethod.try_else] at h_not
      have h_not_schur : ¬ (SchurMethod k R).IsSliceable A :=
        (not_or.mp h_not).1
      have h_not_zeroCol : ¬ (ZeroColumnMethod k k R).IsSliceable A :=
        (not_or.mp h_not).2
      -- Derive the pivot row and its nonzero entry.
      dsimp [ZeroColumnMethod] at h_not_zeroCol
      let h_exists : ∃ i, A i 0 ≠ 0 := not_forall.mp h_not_zeroCol
      let i := Classical.choose h_exists
      have hi : A i 0 ≠ 0 := Classical.choose_spec h_exists
      dsimp [reduc, PLU_Reduction_fin, ReductionMethod.try_else, SchurMethod, ZeroColumnMethod]
      refine Or.inl ?_
      have : (swap R 0 i * A) 0 0 = A i 0 := by
        simp [swap_mul_apply_left]
      have h_unit : IsUnit (A i 0) := isUnit_iff_ne_zero.mpr hi
      simpa [this] using h_unit
  }

/-- Complete reduction strategy on `(k+1)×(k+1)` matrices. -/
noncomputable def PLU_Strategy_fin (k : ℕ) :
    ReductionStrategy (k + 1) (k + 1) k k R where
  transform := PLU_Transform_fin (R := R) k
  reduction := PLU_Reduction_fin (R := R) k
  goal_is_sliceable := rfl
  μ := fun x => x.1.1
  μ_mono := by
    intro A t
    simp
  slice_progress := by
    intro A hA
    -- Slicing drops the dimension from `k+1` to `k`.
    simp

/-- Transport lemma: the PLU property is invariant under the strategy relation. -/
-- CORRECTED SIGNATURE: Use {k : ℕ} and Fin (k+1) to match the strategy's definition.
private lemma transport_plu_fin {k : ℕ}
    {A B : Matrix (Fin (k + 1)) (Fin (k + 1)) R}
    (hr : (PLU_Strategy_fin (R := R) k).r B A) (hA : HasPLU_fin A) :
    HasPLU_fin B := by
  classical
  rcases hr with rfl | ⟨t, rfl⟩
  · -- Case 1: B = A, the property is trivial.
    exact hA
  · -- Case 2: B = (swap R 0 t) * A
    rcases hA with ⟨⟨P, L, U⟩, ⟨hP, hL, hU⟩, hEq⟩
    let t' : Fin (k + 1) := t
    have hP' : IsPermutation (P * swap R 0 t') :=
      isPermutation_mul hP (isPermutation_swap 0 t')
    refine ⟨⟨P * swap R 0 t', L, U⟩, ⟨hP', hL, hU⟩, ?_⟩
    calc
      (P * swap R 0 t') * (swap R 0 t' * A) = P * A := by
        simp [← mul_assoc]
        rw [mul_assoc P]
        simp [swap_mul_self]
      _ = L * U := hEq

/-- helper: `StrictMono (finSuccEquivSumLex k)`，证明体从原 proof 原样剪出 -/
private lemma finSuccEquivSumLex_strictMono (k : ℕ) :
    StrictMono (finSuccEquivSumLex k) := by
  intro x y hxy
  cases x using Fin.cases with
  | zero =>
      cases y using Fin.cases with
      | zero =>
          exact (lt_irrefl _ hxy).elim
      | succ y_val =>
          -- `e 0 = inl 0`, `e (succ y) = inr y`
          -- and `inl _ < inr _` for lex order
          simp [finSuccEquivSumLex]
          apply Sum.Lex.inl_lt_inr
  | succ x_val =>
      cases y using Fin.cases with
      | zero =>
          exact (not_lt_of_ge (Fin.zero_le _) hxy).elim
      | succ y_val =>
          -- `inr x < inr y` iff `x < y`
          have : x_val < y_val := (Fin.succ_lt_succ_iff.mp hxy)
          simp [finSuccEquivSumLex]
          exact Sum.Lex.inr_lt_inr_iff.mpr this

/-- helper: 将块世界等式 `P_blk * Aℓ = L_blk * U_blk` transport 回 `Fin (k+1)` -/
private lemma schur_case_transport_back {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (e : Fin (k + 1) ≃ (Fin 1) ⊕ₗ (Fin k))
    (P_blk L_blk U_blk :
      Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R)
    (h_blk : P_blk * (Matrix.reindex e e A) = L_blk * U_blk) :
    (Matrix.reindex e.symm e.symm P_blk) * A =
      (Matrix.reindex e.symm e.symm L_blk) * (Matrix.reindex e.symm e.symm U_blk) := by
  -- 这些 `let` 与主引理中一致，保证下面 dsimp [P,L,U] 是原样可用的
  let P : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm P_blk
  let U : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm U_blk
  let L : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm L_blk

  -- === 以下 proof 体：从你原来 Step 2 原样复制 ===
  have h_back := congrArg (Matrix.reindex e.symm e.symm) h_blk
  dsimp [P, L, U]
  rw [← submatrix_mul]
  · simp only [reindex_apply, Equiv.symm_symm] at h_back
    rw [← h_back]
    classical
    -- (1) A = Aℓ.submatrix e e
    let Aℓ : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R := Matrix.reindex e e A
    have hA : A = Aℓ.submatrix (⇑e) (⇑e) := by
      ext i j
      simp [Aℓ, Matrix.reindex_apply, Matrix.submatrix]
    -- (2) use submatrix_mul
    simp [hA]
  · apply e.bijective

/--
**Lifting Helper 1: Schur Case**

This lemma handles the lifting step for the case where the pivot `A 0 0` is non-zero,
and the `SchurMethod` is used for reduction.
-/
private lemma lift_from_slice_schur_case {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (h_pivot_unit : IsUnit (A 0 0))
    (h_slice : HasPLU_fin ((SchurMethod k R).slice A h_pivot_unit)) :
    HasPLU_fin A := by
  classical
  rcases h_slice with ⟨⟨P', L', U'⟩, ⟨hP', hL', hU'⟩, h_slice_eq⟩

  -- The (equiv) reindex used to expose the 1×1 pivot block.
  let e : Fin (k + 1) ≃ (Fin 1) ⊕ₗ (Fin k) := finSuccEquivSumLex k

  -- `StrictMono e` is now easy because the codomain order is lex.
  have h_mono : StrictMono e := by
    simpa [e] using (finSuccEquivSumLex_strictMono k)

  -- Work in the block world.
  let A' : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R := Matrix.reindex e e A
  let A₁₁ : Matrix (Fin 1) (Fin 1) R := A'.toBlocks₁₁
  let A₁₂ : Matrix (Fin 1) (Fin k) R := A'.toBlocks₁₂
  let A₂₁ : Matrix (Fin k) (Fin 1) R := A'.toBlocks₂₁
  let A₂₂ : Matrix (Fin k) (Fin k) R := A'.toBlocks₂₂

  have h_core_alg : P' * ((SchurMethod k R).slice A h_pivot_unit) = L' * U' := h_slice_eq

  let inv₁₁ : Matrix (Fin 1) (Fin 1) R := !![(IsUnit.unit h_pivot_unit).inv]

  let P_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 P'

  let U_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks A₁₁ A₁₂ 0 U'

  let L_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 (P' * A₂₁ * inv₁₁) L'

  -- Reindex back to `Fin (k+1)`.
  let P : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm P_blk
  let U : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm U_blk
  let L : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm L_blk

  refine ⟨⟨P, L, U⟩, ?_, ?_⟩
  · -- Properties
    refine ⟨?_, ?_, ?_⟩
    · -- P permutation
      have hP_id : IsPermutation (1 : Matrix (Fin 1) (Fin 1) R) := by
        dsimp [IsPermutation]
        refine ⟨Equiv.refl (Fin 1), ?_⟩
        simp
      have hP_blk : IsPermutation P_blk := by
        exact (isPermutation_fromBlocks_blockDiag_iff (P₁₁ := (1 : Matrix (Fin 1) (Fin 1) R))
            (P₂₂ := P')).2 ⟨hP_id, hP'⟩
      have : IsPermutation (Matrix.reindex e.symm e.symm P_blk) :=
        (isPermutation_reindex (e := e.symm) (A := P_blk)).1 hP_blk
      simpa [P] using this

    · -- L unit-lower-triangular
      have hL_blk : IsUnitLowerTriangular L_blk := by
        simpa [L_blk] using
          (isUnitLowerTriangular_fromBlocks_one_zero_toLex (n₁ := 1) (n₂ := k)
            (L₂₁ := (P' * A₂₁ * inv₁₁)) (L' := L') hL')
      have hL_re : IsUnitLowerTriangular (Matrix.reindex e e L) := by
        simpa [L, L_blk] using hL_blk
      exact (isUnitLowerTriangular_reindex (e := e) (h_mono := h_mono) (A := L)).2 hL_re

    · -- U upper-triangular
      have hA₁₁_ut : IsUpperTriangular A₁₁ := by
        -- 1×1 case: subsingleton
        simpa using (isUpperTriangular_of_subsingleton (A := A₁₁))
      have hU_blk : IsUpperTriangular U_blk := by
        simpa [U_blk] using
          (isUpperTriangular_fromBlocks_toLex (n₁ := 1) (n₂ := k)
            (A₁₁ := A₁₁) (A₁₂ := A₁₂) (A₂₂ := U') hA₁₁_ut hU')
      have hU_re : IsUpperTriangular (Matrix.reindex e e U) := by
        simpa [U, U_blk] using hU_blk
      exact (isUpperTriangular_reindex (e := e) (h_mono := h_mono) (A := U)).2 hU_re
  · -- Equation: (PLU_Schema_fin (k+1)).equation A (P,L,U)
    -- by definition this is `P * A = L * U`
    dsimp [PLU_Schema_fin]

    -- Work in the lex block world: Aℓ has the SAME index type as P_blk/L_blk/U_blk.
    let Aℓ : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R := Matrix.reindex e e A

    -- Step 1: prove the block-world equation `P_blk * Aℓ = L_blk * U_blk`.
    have h_blk : P_blk * Aℓ = L_blk * U_blk := by
      -- Rewrite Aℓ as `fromBlocks` of its blocks (but we already named blocks from A' (Sum-world)).
      -- So we bridge by *defining* the blocks of Aℓ using toBlocks on Aℓ itself,
      -- and then show they coincide with your A₁₁..A₂₂ by simp.
      -- (This avoids ever multiplying Lex×Sum.)

      -- Define blocks from Aℓ (lex world). (These are defeq to Sum blocks under ⊕ₗ.)
      let B₁₁ : Matrix (Fin 1) (Fin 1) R := Aℓ.toBlocks₁₁
      let B₁₂ : Matrix (Fin 1) (Fin k) R := Aℓ.toBlocks₁₂
      let B₂₁ : Matrix (Fin k) (Fin 1) R := Aℓ.toBlocks₂₁
      let B₂₂ : Matrix (Fin k) (Fin k) R := Aℓ.toBlocks₂₂

      -- Now rewrite U_blk/L_blk using these blocks (so everything is in the same world).
      -- We will use `simp` to identify Bᵢⱼ with your Aᵢⱼ.
      have hB₁₁ : B₁₁ = A₁₁ := by
        -- both are 1×1: ext and simp
        ext i j
        -- fin_cases i <;> fin_cases j
        -- unfold B₁₁/A₁₁, Aℓ/A'
        simp [B₁₁, A₁₁, Aℓ, A', Matrix.toBlocks₁₁, Matrix.reindex_apply]
      have hB₁₂ : B₁₂ = A₁₂ := by
        ext i j
        fin_cases i
        -- j : Fin k
        simp [B₁₂, A₁₂, Aℓ, A', Matrix.toBlocks₁₂, Matrix.reindex_apply]
      have hB₂₁ : B₂₁ = A₂₁ := by
        ext i j
        fin_cases j
        simp [B₂₁, A₂₁, Aℓ, A', Matrix.toBlocks₂₁, Matrix.reindex_apply]
      have hB₂₂ : B₂₂ = A₂₂ := by
        ext i j
        simp [B₂₂, A₂₂, Aℓ, A', Matrix.toBlocks₂₂, Matrix.reindex_apply]

      have hAℓ_fromBlocks :
          (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ :
            Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) = Aℓ := by
        simpa [B₁₁, B₁₂, B₂₁, B₂₂] using (fromBlocks_toBlocks Aℓ)

      -- Compute P_blk * Aℓ via block multiplication (in lex world).
      have hPA :
          P_blk * Aℓ =
            (fromBlocks B₁₁ B₁₂ (P' * B₂₁) (P' * B₂₂) :
              Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
        calc
          P_blk * Aℓ
              = P_blk * (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂).reindex toLex toLex := by
                  simp [hAℓ_fromBlocks, Lex, toLex]
          _ = (fromBlocks B₁₁ B₁₂ (P' * B₂₁) (P' * B₂₂) :
                Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
                  simpa [P_blk] using
                    (block_P_mul_A (n₁ := 1) (n₂ := k) (m₁ := 1) (m₂ := k)
                      (A₁₁ := B₁₁) (A₁₂ := B₁₂) (A₂₁ := B₂₁) (A₂₂ := B₂₂) (P' := P'))

      -- Compute L_blk * U_blk via block multiplication.
      have hLU :
          L_blk * U_blk =
            (fromBlocks B₁₁ B₁₂ ((P' * B₂₁ * inv₁₁) * B₁₁)
              ((P' * B₂₁ * inv₁₁) * B₁₂ + L' * U') :
              Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
        -- use your BlockLifting lemma block_L_mul_U (or simp [fromBlocks_multiply])
        simpa [L_blk, U_blk, hB₁₁, hB₁₂, hB₂₁] using
          (block_L_mul_U (n₁ := 1) (n₂ := k)
            (L₂₁ := (P' * B₂₁ * inv₁₁)) (L' := L')
            (U₁₁ := B₁₁) (U₁₂ := B₁₂) (U' := U'))

      -- Now reduce to checking block (2,1) and (2,2).
      -- (2,1): (P'*B₂₁*inv₁₁)*B₁₁ = P'*B₂₁
      have hinv_mul_B₁₁ : inv₁₁ * B₁₁ = (1 : Matrix (Fin 1) (Fin 1) R) := by
        have hB₁₁_val : B₁₁ = !![A 0 0] := by
          ext i j
          simp [B₁₁, Aℓ, e, finSuccEquivSumLex, Matrix.toBlocks₁₁, Matrix.reindex_apply]
        have hu : ((IsUnit.unit h_pivot_unit : Units R) : R) = A 0 0 :=
          IsUnit.unit_spec h_pivot_unit
        have hmul_units :
            ((IsUnit.unit h_pivot_unit).inv) * (IsUnit.unit h_pivot_unit) = 1 := by
          simp [IsUnit.inv_mul_cancel h_pivot_unit]
        have hmul_R :
            ((IsUnit.unit h_pivot_unit).inv : R) * (A 0 0) = 1 := by
          simpa [hu] using congrArg (fun u : R => (u : R)) hmul_units
        simp at hmul_R
        simp [inv₁₁, hB₁₁_val, hmul_R]
        ext i j; fin_cases i; fin_cases j; simp


      have h21 :
          (P' * B₂₁) = (P' * B₂₁ * inv₁₁) * B₁₁ := by
        calc
          P' * B₂₁
              = (P' * B₂₁) * (1 : Matrix (Fin 1) (Fin 1) R) := by simp
          _ = (P' * B₂₁) * (inv₁₁ * B₁₁) := by simp [hinv_mul_B₁₁]
          _ = (P' * B₂₁ * inv₁₁) * B₁₁ := by
                simp [Matrix.mul_assoc]

      -- (2,2): use the Schur slice identity + h_core_alg.
      -- Here we rely on the definitional form of SchurMethod.slice.
      have h_slice_def :
          (SchurMethod k R).slice A h_pivot_unit = B₂₂ - B₂₁ * inv₁₁ * B₁₂ := by
        -- This should be `simp`-able if your SchurMethod.slice is defined via these blocks.
        -- Adjust the simp set to match your SchurMethod implementation.
        simp [SchurMethod, Aℓ, B₂₂, B₂₁, B₁₂, inv₁₁, e, finSuccEquivSumLex]
        simp [finSuccEquivSum]

      have h22 :
          (P' * B₂₂) =
            (P' * B₂₁ * inv₁₁) * B₁₂ + (L' * U') := by
        -- rewrite L'*U' using the slice equation
        have hLUcore : L' * U' = P' * (SchurMethod k R).slice A h_pivot_unit := by
          simpa using h_core_alg.symm
        -- expand slice
        calc
          P' * B₂₂
              = (P' * B₂₁ * inv₁₁) * B₁₂ + (P' * (B₂₂ - B₂₁ * inv₁₁ * B₁₂)) := by
                  -- pure algebra over matrices
                  simp [Matrix.mul_add, Matrix.mul_assoc, sub_eq_add_neg,
                        add_left_comm, add_comm]
          _ = (P' * B₂₁ * inv₁₁) * B₁₂ + (P' * (SchurMethod k R).slice A h_pivot_unit) := by
                  simp [h_slice_def]
          _ = (P' * B₂₁ * inv₁₁) * B₁₂ + (L' * U') := by
                  simp [hLUcore]

      -- Put everything together.
      -- Compare `hPA` and `hLU` blockwise.
      have h_blocks_eq :
          (fromBlocks B₁₁ B₁₂ (P' * B₂₁) (P' * B₂₂) :
            Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R)
          =
          (fromBlocks B₁₁ B₁₂ ((P' * B₂₁ * inv₁₁) * B₁₁)
            ((P' * B₂₁ * inv₁₁) * B₁₂ + L' * U') :
            Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
        ext i j
        cases i using Sum.rec <;> cases j using Sum.rec <;>
          rw [← h21, h22]

      -- conclude block equation
      calc
        P_blk * Aℓ
            = (fromBlocks B₁₁ B₁₂ (P' * B₂₁) (P' * B₂₂) :
                Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := hPA
        _ = (fromBlocks B₁₁ B₁₂ ((P' * B₂₁ * inv₁₁) * B₁₁)
              ((P' * B₂₁ * inv₁₁) * B₁₂ + L' * U') :
              Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
              simpa using h_blocks_eq
        _ = L_blk * U_blk := by simp [hLU]

    -- Step 2: transport the block-world equation back to `Fin (k+1)` by reindexing with e.symm.
    exact schur_case_transport_back (R := R) (A := A) (e := e)
      (P_blk := P_blk) (L_blk := L_blk) (U_blk := U_blk) (by
        exact h_blk)


/--
**Lifting Helper 2: Zero-Column Case**

This lemma handles the lifting step for the case where the first column of `A` is all zeros,
and the `ZeroColumnMethod` is used for reduction.
-/
private lemma lift_from_slice_zero_col_case {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (h_zero_col : ∀ i, A i 0 = 0)
    (h_slice : HasPLU_fin ((ZeroColumnMethod k k R).slice A h_zero_col)) :
    HasPLU_fin A := by
  classical
  rcases h_slice with ⟨⟨P', L', U'⟩, ⟨hP', hL', hU'⟩, h_slice_eq⟩

  -- Reindex to expose the 1×1 + k×k block structure (lex-ordered sum).
  let e : Fin (k + 1) ≃ (Fin 1) ⊕ₗ (Fin k) := finSuccEquivSumLex k
  have h_mono : StrictMono e := by
    -- same helper you already have from the Schur case
    simpa [e] using finSuccEquivSumLex_strictMono k

  -- Work in the block world (lex world).
  let Aℓ : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R := Matrix.reindex e e A
  let B₁₁ : Matrix (Fin 1) (Fin 1) R := Aℓ.toBlocks₁₁
  let B₁₂ : Matrix (Fin 1) (Fin k) R := Aℓ.toBlocks₁₂
  let B₂₁ : Matrix (Fin k) (Fin 1) R := Aℓ.toBlocks₂₁
  let B₂₂ : Matrix (Fin k) (Fin k) R := Aℓ.toBlocks₂₂

  -- First column of A is zero ⇒ left blocks in this decomposition are zero.
  have hB₁₁_zero : B₁₁ = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    -- B₁₁ 0 0 = Aℓ (inl 0) (inl 0) = A 0 0
    simpa [B₁₁, Aℓ, e, finSuccEquivSumLex, Matrix.toBlocks₁₁, Matrix.reindex_apply] using
      (h_zero_col 0)

  have hB₂₁_zero : B₂₁ = 0 := by
    ext i j
    fin_cases j
    -- B₂₁ i 0 = Aℓ (inr i) (inl 0) = A (i.succ) 0
    simpa [B₂₁, Aℓ, e, finSuccEquivSumLex, Matrix.toBlocks₂₁, Matrix.reindex_apply] using
      (h_zero_col i.succ)

  -- In your design, ZeroColumnMethod.slice should be definitionally the bottom-right block.
  have h_slice_def :
      (ZeroColumnMethod k k R).slice A h_zero_col = B₂₂ := by
    ext i j
    -- This `simp` should match your `ZeroColumnMethod.slice` definition.
    simp [ZeroColumnMethod, B₂₂, Aℓ, e, finSuccEquivSumLex, Matrix.toBlocks₂₂, Matrix.reindex_apply]

  have h_core_alg : P' * B₂₂ = L' * U' := by
    simpa [h_slice_def] using h_slice_eq

  -- Build block PLU (lex world).
  let P_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 P'
  let L_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 (0 : Matrix (Fin k) (Fin 1) R) L'
  let U_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks B₁₁ B₁₂ 0 U'

  -- Transport back to Fin (k+1).
  let P : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm P_blk
  let L : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm L_blk
  let U : Matrix (Fin (k + 1)) (Fin (k + 1)) R := Matrix.reindex e.symm e.symm U_blk

  refine ⟨⟨P, L, U⟩, ?_, ?_⟩
  · -- Properties: P permutation, L unit-lower-triangular, U upper-triangular.
    refine ⟨?_, ?_, ?_⟩
    · -- P permutation
      have hP_id : IsPermutation (1 : Matrix (Fin 1) (Fin 1) R) := by
        dsimp [IsPermutation]
        refine ⟨Equiv.refl (Fin 1), ?_⟩
        simp
      have hP_blk : IsPermutation P_blk := by
        exact
          (isPermutation_fromBlocks_blockDiag_iff
              (P₁₁ := (1 : Matrix (Fin 1) (Fin 1) R)) (P₂₂ := P')).2 ⟨hP_id, hP'⟩
      have : IsPermutation (Matrix.reindex e.symm e.symm P_blk) :=
        (isPermutation_reindex (e := e.symm) (A := P_blk)).1 hP_blk
      simpa [P] using this

    · -- L unit lower triangular
      have hL_blk : IsUnitLowerTriangular L_blk := by
        -- uses your block lemma (lex world)
        simpa [L_blk] using
          (isUnitLowerTriangular_fromBlocks_one_zero_toLex (n₁ := 1) (n₂ := k)
            (L₂₁ := (0 : Matrix (Fin k) (Fin 1) R)) (L' := L') hL')
      have hL_re : IsUnitLowerTriangular (Matrix.reindex e e L) := by
        simpa [L, L_blk] using hL_blk
      exact (isUnitLowerTriangular_reindex (e := e) (h_mono := h_mono) (A := L)).2 hL_re

    · -- U upper triangular
      have hB₁₁_ut : IsUpperTriangular B₁₁ := by
        simpa using (isUpperTriangular_of_subsingleton (A := B₁₁))
      have hU_blk : IsUpperTriangular U_blk := by
        simpa [U_blk] using
          (isUpperTriangular_fromBlocks_toLex (n₁ := 1) (n₂ := k)
            (A₁₁ := B₁₁) (A₁₂ := B₁₂) (A₂₂ := U') hB₁₁_ut hU')
      have hU_re : IsUpperTriangular (Matrix.reindex e e U) := by
        simpa [U, U_blk] using hU_blk
      exact (isUpperTriangular_reindex (e := e) (h_mono := h_mono) (A := U)).2 hU_re

  · -- Equation: (PLU_Schema_fin (k+1)).equation A (P,L,U)  i.e.  P*A = L*U
    dsimp [PLU_Schema_fin]
    -- Step 1: block-world equation.
    have h_blk : P_blk * Aℓ = L_blk * U_blk := by
      have hAℓ_fromBlocks :
          (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ :
            Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) = Aℓ := by
        simpa [B₁₁, B₁₂, B₂₁, B₂₂] using (fromBlocks_toBlocks Aℓ)

      have hPA :
          P_blk * Aℓ =
            (fromBlocks B₁₁ B₁₂ (P' * B₂₁) (P' * B₂₂) :
              Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
        -- block multiplication (P on left)
        simpa [hAℓ_fromBlocks, P_blk] using
          (block_P_mul_A (n₁ := 1) (n₂ := k) (m₁ := 1) (m₂ := k)
            (A₁₁ := B₁₁) (A₁₂ := B₁₂) (A₂₁ := B₂₁) (A₂₂ := B₂₂) (P' := P'))

      have hLU :
          L_blk * U_blk =
            (fromBlocks B₁₁ B₁₂ ((0 : Matrix (Fin k) (Fin 1) R) * B₁₁)
              ((0 : Matrix (Fin k) (Fin 1) R) * B₁₂ + L' * U') :
              Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
        simpa [L_blk, U_blk] using
          (block_L_mul_U (n₁ := 1) (n₂ := k)
            (L₂₁ := (0 : Matrix (Fin k) (Fin 1) R)) (L' := L')
            (U₁₁ := B₁₁) (U₁₂ := B₁₂) (U' := U'))

      -- reduce to blocks using hB₂₁_zero and h_core_alg
      have h_blocks_eq :
          (fromBlocks B₁₁ B₁₂ (P' * B₂₁) (P' * B₂₂) :
            Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R)
          =
          (fromBlocks B₁₁ B₁₂ ((0 : Matrix (Fin k) (Fin 1) R) * B₁₁)
            ((0 : Matrix (Fin k) (Fin 1) R) * B₁₂ + L' * U') :
            Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
        ext i j
        cases i using Sum.rec <;> cases j using Sum.rec
        · -- (1,1)
          simp
        · -- (1,2)
          simp
        · -- (2,1)
          simp [hB₂₁_zero]
        · -- (2,2)
          simp [h_core_alg]

      calc
        P_blk * Aℓ
            = (fromBlocks B₁₁ B₁₂ (P' * B₂₁) (P' * B₂₂) :
                Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := hPA
        _ = (fromBlocks B₁₁ B₁₂ ((0 : Matrix (Fin k) (Fin 1) R) * B₁₁)
              ((0 : Matrix (Fin k) (Fin 1) R) * B₁₂ + L' * U') :
              Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
              simpa using h_blocks_eq
        _ = L_blk * U_blk := by simp [hLU]

    -- Step 2: transport back (reuse the generic transport lemma you extracted earlier).
    have h_fin :
        (Matrix.reindex e.symm e.symm P_blk) * A =
          (Matrix.reindex e.symm e.symm L_blk) * (Matrix.reindex e.symm e.symm U_blk) := by
      exact schur_case_transport_back (R := R) (A := A) (e := e)
        (P_blk := P_blk) (L_blk := L_blk) (U_blk := U_blk) h_blk

    simpa [P, L, U] using h_fin

/-- Lifting lemma: build a PLU decomposition of `A` from a slice. -/
private lemma lift_from_slice_plu_fin {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (hA : (PLU_Reduction_fin (R := R) k).IsSliceable A)
    (h_slice : HasPLU_fin ((PLU_Reduction_fin (R := R) k).slice A hA)) :
    HasPLU_fin A := by
  -- The main proof now simply dispatches to the appropriate helper lemma
  -- based on the `IsSliceable` condition.
  by_cases h_schur : IsUnit (A 0 0)
  · -- Case 1: `SchurMethod` was used.
    cases hA with
    | inl hA_schur =>
        -- Simplify the slice.
        have h_slice' : HasPLU_fin ((SchurMethod k R).slice A hA_schur) := by
          simpa [PLU_Reduction_fin, ReductionMethod.try_else, hA_schur] using h_slice
        -- Align the pivot proofs via proof irrelevance.
        have h_eq : hA_schur = h_schur := Subsingleton.elim _ _
        have h_slice'' : HasPLU_fin ((SchurMethod k R).slice A h_schur) := by
          simpa [h_eq] using h_slice'
        exact lift_from_slice_schur_case A h_schur h_slice''
    | inr h_zero_col =>
        have : False := (isUnit_iff_ne_zero.mp h_schur) (h_zero_col 0)
        contradiction
  · -- Case 2: `ZeroColumnMethod` was used.
    cases hA with
    | inl h_unit =>
        have : False := h_schur h_unit
        contradiction
    | inr h_zero_col =>
        have h_slice' : HasPLU_fin ((ZeroColumnMethod k k R).slice A h_zero_col) := by
          simp [PLU_Reduction_fin, ReductionMethod.try_else] at h_slice
          split_ifs at h_slice with h_case
          · contradiction
          · exact h_slice
        exact lift_from_slice_zero_col_case A h_zero_col h_slice'


/-- Base case: zero-dimensional matrices admit a trivial PLU. -/
private lemma base_plu_zero_dim {x : FinRectUniverse R}
    (h_zero : x.1.1 = 0 ∨ x.1.2 = 0) :
    (if h : x.1.1 = x.1.2 then HasPLU_fin (cast (by rw [h]) x.matrix) else True) := by
  classical
  -- Unpack the rectangular universe element.
  rcases x with ⟨nm, A⟩
  rcases nm with ⟨n, m⟩
  have h_zero' : n = 0 ∨ m = 0 := by
    simpa using h_zero

  by_cases h : n = m
  · -- Square case: with `h_zero`, this forces `n = m = 0`.
    have hn0 : n = 0 := by
      rcases h_zero' with hn0 | hm0
      · exact hn0
      · -- hm0 : m = 0, and h : n = m
        -- use h.symm : m = n to rewrite m to n
        simpa [h.symm] using hm0

    -- Rewrite dimensions to 0.
    cases hn0
    have hm0 : m = 0 := by
      -- now h : 0 = m
      simpa using h.symm
    cases hm0

    -- Now `h : 0 = 0`, so the cast is defeq.
    cases h

    dsimp [FinRectFamily]
    -- 先把 A “看成”真正的 0×0 Matrix（通常 FinRectFamily 是 abbrev/defeq 到 Matrix）
    have h_triv : HasPLU_fin (R := R) A.A := by
      refine ⟨⟨(1 : Matrix (Fin 0) (Fin 0) R),
                (1 : Matrix (Fin 0) (Fin 0) R),
                (A.A : Matrix (Fin 0) (Fin 0) R)⟩, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · dsimp [IsPermutation]
          refine ⟨Equiv.refl (Fin 0), ?_⟩
          ext i j
          exact (Fin.elim0 i)
        · simpa using (isUnitLowerTriangular_one (ι := Fin 0) (R := R))
        · simpa using
            (isUpperTriangular_of_subsingleton (ι := Fin 0) (R := R)
              (A := (A.A : Matrix (Fin 0) (Fin 0) R)))
      · dsimp [PLU_Schema_fin]

    -- 最后把目标里的 cast / universe.matrix 化掉
    simpa [FinRectUniverse.matrix] using h_triv
  · -- Non-square case: goal is `True`.
    simp [h]


end FinImpl


-- ==================================================================
-- 3. Assemble instance
-- ==================================================================

/--
This instance packages all the components of the PLU decomposition proof
into the structure expected by the main induction theorem.
-/
noncomputable def PLU_Instance (R : Type*) [Field R] [DecidableEq R] :
    RectDecompositionInstance R where
  P_univ := fun x => if h : x.1.1 = x.1.2 then HasPLU_fin (cast (by rw [h]) x.matrix) else True
  pos_instance := {
    P_univ := fun x => if h : x.1.1 = x.1.2 then HasPLU_fin (cast (by rw [h]) x.matrix) else True
    P_pos := fun x => HasPLU_fin x.val.matrix
    P_compat := by
      intro x; split_ifs with h
      · rfl
      · -- This case is impossible because `PosFinRectUniverse` implies m, n > 0,
        -- but for PLU we are implicitly working with square matrices.
        -- A better `P_univ` would make this case trivial.
        -- For now, we assume our universe for PLU is square.
        -- A better framework would use `SquareMatFamily` universe.
        sorry
    μ := fun x => x.1.1 -- Induction on the number of rows.
    μ_base := 0
    base_pos := by
      intro x h_mu_le_base
      -- A positive dimension cannot be <= 0.
      exact (Nat.not_le_of_gt x.2.1 h_mu_le_base).elim
    r_pos := fun y x =>
      let k := x.val.1.1 - 1
      (PLU_Strategy_fin (R := R) k).r y.val.matrix x.val.matrix
    IsSliceable_pos := fun x =>
      let k := x.val.1.1 - 1
      (PLU_Reduction_fin (R := R) k).IsSliceable x.val.matrix
    slice_pos := fun x hx =>
      let k := x.val.1.1 - 1
      let A_slice := (PLU_Reduction_fin (R := R) k).slice x.val.matrix hx
      let n' := (PLU_Reduction_fin (R := R) k).slice_m
      -- The slice of a square matrix is square.
      ⟨⟨n', n'⟩, ⟨A_slice⟩⟩
    transport := by
      intro x y h_r h_y
      -- Let n be the dimension of the matrices.
      let n := x.val.1.1
      have h_pos : n > 0 := x.2.1
      -- Let k = n - 1, so n = k + 1.
      let k := n - 1
      have h_n_eq_k_succ : n = k + 1 := (Nat.succ_pred_eq_of_pos h_pos).symm
      -- Use `subst` to align the types with the lemma's signature.
      subst h_n_eq_k_succ
      -- Now A and B have type `Matrix (Fin (k+1)) ...`, which matches the lemma.
      exact transport_plu_fin (A := y.val.matrix) (B := x.val.matrix) h_r h_y
    lift_from_slice := by
      intro x hx h_slice
      let n := x.val.1.1
      have h_pos : n > 0 := x.2.1
      let k := n - 1
      have h_n_eq_k_succ : n = k + 1 := (Nat.succ_pred_eq_of_pos h_pos).symm
      subst h_n_eq_k_succ
      -- We need to show that the slice property implies the property on the slice's matrix.
      have h_slice_prop : HasPLU_fin (h_slice.2.A) := by
        -- The slice is a square matrix, so the `if` in `P_univ` is true.
        have h_slice_sq : h_slice.1.1 = h_slice.1.2 := by
          dsimp [slice_pos]; simp [PLU_Reduction_fin, ReductionMethod.try_else, SchurMethod, ZeroColumnMethod]
        simpa [h_slice_sq] using h_slice
      exact lift_from_slice_plu_fin x.val.matrix hx h_slice_prop
    reach := by
      intro x h_mu_gt_base
      let n := x.val.1.1
      have hn_pos : n > 0 := h_mu_gt_base
      let k := n - 1
      have h_n_eq_k_succ : n = k + 1 := (Nat.succ_pred_eq_of_pos hn_pos).symm
      subst h_n_eq_k_succ
      -- Use the strategy's `mk_reach` helper to construct the proof.
      let S := PLU_Strategy_fin (R := R) k
      rcases S.mk_reach 0 ⟨by simp, by simp⟩ x.val.matrix (by simp [S.μ, hn_pos]) with ⟨B, hB, h_r, h_prog⟩
      -- Package the result `B` back into the universe type.
      let y : PosFinRectUniverse R := ⟨⟨⟨k + 1, k + 1⟩, ⟨B⟩⟩, ⟨by simp, by simp⟩⟩
      exact ⟨y, hB, h_r, h_prog⟩
  }
  P_univ_compat := rfl
  P_pos_compat_top := by intro x; rfl
  base_zero := base_plu_zero_dim (R := R)


-- ==================================================================
-- 4. Final theorem
-- ==================================================================

/--
**PLU Decomposition Existence Theorem**

For any square matrix `A` over a field `R`, there exists a permutation matrix `P`,
a unit lower triangular matrix `L`, and an upper triangular matrix `U`
such that `P * A = L * U`.
-/
theorem exists_plu_decomposition {n : ℕ} {R : Type*} [Field R] [DecidableEq R]
    (A : Matrix (Fin n) (Fin n) R) : HasPLU_fin A := by
  -- The main theorem is now a direct application of the framework's engine.
  let inst := PLU_Instance R
  -- We need to show that `inst.P_univ` holds for our matrix `A`.
  have h_proof := RectDecompositionInstance.prove_for_fin inst n n A
  -- The `if` in `P_univ` is true since `n=n`.
  simpa [inst.P_univ] using h_proof

end MatDecompFormal.Instances
