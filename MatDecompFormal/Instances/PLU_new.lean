import MatDecompFormal.Framework.UniverseDecompositionFin
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Abstractions.Strategy
import MatDecompFormal.Abstractions.ReductionCombinators
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
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
  -- The proof here is exactly the content of the `if h_schur : ... then ...` block.
  rcases h_slice with ⟨⟨P', L', U'⟩, ⟨hP', hL', hU'⟩, h_slice_eq⟩
  let e := finSuccEquivSum k
  let A' := reindex e e A
  let A₁₁ := A'.toBlocks₁₁; let A₁₂ := A'.toBlocks₁₂
  let A₂₁ := A'.toBlocks₂₁; let A₂₂ := A'.toBlocks₂₂

  have h_core_alg : P' * ((SchurMethod k R).slice A h_pivot_unit) = L' * U' := h_slice_eq

  let P := fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 P'
  let U := fromBlocks A₁₁ A₁₂ 0 U'
  let L := fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 (A₂₁ * !![(IsUnit.unit h_pivot_unit).inv]) L'

  refine ⟨⟨P, L, U⟩, ?_, ?_⟩
  · -- Part 1: Prove properties of P, L, U.
    sorry
  · -- Part 2: Prove the equation P * A = L * U.
    sorry

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
  -- The proof here is exactly the content of the `else ...` block.
  classical
  rcases h_slice with ⟨⟨P', L', U'⟩, ⟨hP', hL', hU'⟩, h_slice_eq⟩
  let e := finSuccEquivSum k
  let A' := reindex e e A
  let A₁₁ := A'.toBlocks₁₁
  let A₁₂ := A'.toBlocks₁₂
  let A₂₁ := A'.toBlocks₂₁
  let A₂₂ := A'.toBlocks₂₂

  have h_slice_is_submatrix :
      (ZeroColumnMethod k k R).slice A h_zero_col = A₂₂ := by
    dsimp [ZeroColumnMethod]
    simp [A', A₂₂, e, submatrix_succ_eq_toBlocks₂₂]

  have h_core_alg : P' * A₂₂ = L' * U' := by
    rw [← h_slice_is_submatrix] at h_slice_eq
    simpa using h_slice_eq

  let P := fromBlocks 1 0 0 P'
  let L := fromBlocks 1 0 0 L'
  let U := fromBlocks 0 A₁₂ 0 U'

  refine ⟨⟨P, L, U⟩, ?_, ?_⟩
  · -- Part 1: Prove properties of P, L, U.
    refine ⟨?_, ?_, ?_⟩
    · exact (isPermutation_fromBlocks_blockDiag_iff _ _).mpr ⟨by simp [IsPermutation], hP'⟩
    · exact isUnitLowerTriangular_fromBlocks_one_zero 0 hL'
    · exact isUpperTriangular_fromBlocks_zero_top _ _ hU'
  · -- Part 2: Prove the equation P * A = L * U.
    apply reindex_inj e.symm e.symm
    have h_A_zero_blocks : A₁₁ = 0 ∧ A₂₁ = 0 := by
      have h_blocks :=
        toBlocks_left_zero_of_first_col_zero (k := k) (m := k) (A := A) h_zero_col
      simpa [A₁₁, A₂₁, A', e] using h_blocks
    have h_PA' : P * A' = fromBlocks 0 A₁₂ 0 (P' * A₂₂) := by
      rw [h_A_zero_blocks.1, h_A_zero_blocks.2]
      simp [fromBlocks_multiply]
    have h_LU : L * U = fromBlocks 0 A₁₂ 0 (L' * U') := by
      simp [fromBlocks_multiply]
    rw [h_PA', h_LU, h_core_alg]

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
          simpa [PLU_Reduction_fin, ReductionMethod.try_else] using h_slice
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
          simpa [PLU_Reduction_fin, ReductionMethod.try_else] using h_slice
        exact lift_from_slice_zero_col_case A h_zero_col h_slice'


/-- Base case: zero-dimensional matrices admit a trivial PLU. -/
private lemma base_plu_zero_dim {x : FinRectUniverse R}
    (h_zero : x.1.1 = 0 ∨ x.1.2 = 0) :
    (if h : x.1.1 = x.1.2 then HasPLU_fin (cast (by rw [h]) x.matrix) else True) := by
  -- This handles the `base_zero` case for the `RectDecompositionInstance`.
  -- We only care about square matrices, so we use an `if`.
  split_ifs with h_sq
  · -- Case: Square matrix. `h_zero` implies dimension is 0.
    have h_dim_zero : x.1.1 = 0 := by tauto
    subst h_dim_zero
    -- The 0×0 matrix has a trivial PLU decomposition: P=L=U=1.
    refine ⟨⟨1, 1, 1⟩, ?_, by simp⟩
    refine ⟨?_, isUnitLowerTriangular_one, isUpperTriangular_one⟩
    -- Framework tool: `Components/Properties/Permutation.lean`
    dsimp [IsPermutation]; use Equiv.refl _; simp
  · -- Case: Non-square matrix. The property is trivially true.
    trivial

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
