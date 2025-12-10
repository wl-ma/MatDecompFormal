-- file: Components/BlockLifting.lean

import MatDecompFormal.Framework.FinEnum
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Components.Properties.Permutation
import Mathlib.Data.Sum.Order
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace MatDecompFormal.Components

open Matrix MatDecompFormal.Components.Properties MatDecompFormal.Framework

/-!
# 分块矩阵代数库 (Block Matrix Algebra Library)

本文件提供了一套纯粹的代数引理，用于处理已被分块的矩阵
（即索引为 `Sum (Fin n₁) (Fin n₂)` 类型的矩阵）。
-/

-- ==================================================================
-- Section 1: Property-Preserving Lemmas for `fromBlocks`
-- ==================================================================

variable {n₁ n₂ m₁ m₂ : ℕ} {R : Type*} [CommRing R] --[DecidableEq R]

/--
**核心工具**: `fromBlocks` 保持上三角性。
-/
theorem fromBlocks_isUpperTriangular_iff
    (M₁₁ : Matrix (Fin n₁) (Fin n₁) R) (M₁₂ : Matrix (Fin n₁) (Fin n₂) R)
    (M₂₁ : Matrix (Fin n₂) (Fin n₁) R) (M₂₂ : Matrix (Fin n₂) (Fin n₂) R) :
    IsUpperTriangular (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) ↔
    IsUpperTriangular M₁₁ ∧ IsUpperTriangular M₂₂ ∧ M₂₁ = 0 := by
  let e₁ := orderIsoOfFinEnum (Fin n₁)
  let e₂ := orderIsoOfFinEnum (Fin n₂)
  simp_rw [IsUpperTriangular, BlockTriangular]
  constructor
  · -- (→)
    intro h
    refine ⟨?_, ?_, ?_⟩
    · -- 证明 M₁₁ 是上三角
      intro i j hij
      -- hij : equiv j < equiv i
      -- have h_lt_base : j < i := (e₁.lt_iff_lt).mp hij
      exact h hij
    · -- 证明 M₂₂ 是上三角
      intro i j hij
      have h_lt_base : j < i := (e₂.lt_iff_lt).mp hij
      exact h (equiv_sum_inr_lt_inr_of_lt h_lt_base)
    · -- 证明 M₂₁ = 0
      ext i j
      -- **直接使用我们的新引理！**
      exact h (equiv_sum_inl_lt_inr j i)
  · -- (←)
    rintro ⟨h₁₁, h₂₂, h₂₁_zero⟩ i' j' hij'
    -- hij' : equiv j' < equiv i'
    rcases i' with (i | i) <;> rcases j' with (j | j)
    · -- Case Sum.inl, Sum.inl
      exact h₁₁ (equiv_lt_of_equiv_sum_inl_lt hij')
    · -- Case Sum.inl, Sum.inr (j' < i' 不可能)
      -- **直接使用我们的新引理来制造矛盾！**
      exfalso
      have h_contra := equiv_sum_inl_lt_inr i j
      exact not_lt.mpr (le_of_lt h_contra) hij'
    · -- Case Sum.inr, Sum.inl
      rw [h₂₁_zero]; rfl
    · -- Case Sum.inr, Sum.inr
      exact h₂₂ (equiv_lt_of_equiv_sum_inr_lt hij')


/-- `fromBlocks` 构造的单位下三角矩阵的性质。 -/
lemma fromBlocks_isUnitLowerTriangular
    (L₂₁ : Matrix (Fin n₂) (Fin n₁) R)
    (L' : Matrix (Fin n₂) (Fin n₂) R) (hL' : IsUnitLowerTriangular L') :
    IsUnitLowerTriangular (fromBlocks 1 0 L₂₁ L') := by
  constructor
  · dsimp [IsLowerTriangular]
    rw [fromBlocks_transpose, fromBlocks_isUpperTriangular_iff]
    simp [isUpperTriangular_one]
    exact hL'.1
  · funext i
    rcases i with (i₁ | i₂)
    · simp [diag_apply, fromBlocks_apply₁₁]
    · rw [diag_apply, fromBlocks_apply₂₂, ← diag_apply L' i₂, hL'.2]
      simp


/-- `fromBlocks` 构造的块对角置换矩阵的性质。 -/
lemma fromBlocks_isPermutation_iff_of_block_diag
    (P₁₁ : Matrix (Fin n₁) (Fin n₁) R) (P₂₂ : Matrix (Fin n₂) (Fin n₂) R) :
    IsPermutation (fromBlocks P₁₁ 0 0 P₂₂) ↔ IsPermutation P₁₁ ∧ IsPermutation P₂₂ := by
  simp [IsPermutation, toMatrix_fromBlocks_diagonal]
  constructor
  · rintro ⟨σ, hσ⟩
    -- 这个证明需要构造从 sum perm 到 component perms 的映射，比较复杂
    -- 我们可以暂时接受它，或者之后再详细证明
    sorry
  · rintro ⟨⟨σ₁, h₁⟩, ⟨σ₂, h₂⟩⟩
    use Equiv.Perm.sumCongr σ₁ σ₂
    rw [h₁, h₂]

-- ==================================================================
-- Section 2: Algebraic Computation Lemmas for `fromBlocks`
-- ==================================================================

/--
**代数积木**: `(P_block * A_block)` 的分块形式。
-/
lemma block_P_mul_A
    (A₁₁ : Matrix (Fin n₁) (Fin m₁) R) (A₁₂ : Matrix (Fin n₁) (Fin m₂) R)
    (A₂₁ : Matrix (Fin n₂) (Fin m₁) R) (A₂₂ : Matrix (Fin n₂) (Fin m₂) R)
    (P' : Matrix (Fin n₂) (Fin n₂) R) :
    (fromBlocks 1 0 0 P') * (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) =
    fromBlocks A₁₁ A₁₂ (P' * A₂₁) (P' * A₂₂) := by
  simp [fromBlocks_multiply]

/--
**代数积木**: `(L_block * U_block)` 的分块形式。
-/
lemma block_L_mul_U
    (L₂₁ : Matrix (Fin n₂) (Fin n₁) R) (L' : Matrix (Fin n₂) (Fin n₂) R)
    (U₁₁ : Matrix (Fin n₁) (Fin n₁) R) (U₁₂ : Matrix (Fin n₁) (Fin n₂) R)
    (U' : Matrix (Fin n₂) (Fin n₂) R) :
    (fromBlocks 1 0 L₂₁ L') * (fromBlocks U₁₁ U₁₂ 0 U') =
    fromBlocks U₁₁ U₁₂ (L₂₁ * U₁₁) (L₂₁ * U₁₂ + L' * U') := by
  simp [fromBlocks_multiply]

/--
**代数积木**: `(L_diag_block * U_block)` 的分块形式。
-/
lemma block_diag_L_mul_block_U
    (L' : Matrix (Fin n₂) (Fin n₂) R)
    (U₁₂ : Matrix (Fin n₁) (Fin n₂) R)
    (U' : Matrix (Fin n₂) (Fin n₂) R) :
    (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 0 L') *
        (fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) U₁₂ (0 : Matrix (Fin n₂) (Fin n₁) R) U') =
    fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) U₁₂ (0 : Matrix (Fin n₂) (Fin n₁) R) (L' * U') := by
  simp [fromBlocks_multiply]

end MatDecompFormal.Components
