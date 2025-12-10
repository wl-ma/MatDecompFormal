import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Framework.FinEnum -- For Preorder.ofFinEnum
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace MatDecompFormal.Components

open Matrix FinEnum MatDecompFormal.Components.Properties MatDecompFormal.Framework

/-!
# 分块矩阵提升引理 (Block Matrix Lifting Lemmas) - v3.0 (完整版)

本文件提供了一套用于处理分块矩阵“提升”操作的通用代数工具。
“提升”指的是从子问题的解（通常是右下角的分块）来构造原问题的解。

这个文件将所有关于 `reindex` 和 `fromBlocks` 的复杂细节完全封装起来，
为上层证明（如 `lift_from_slice_plu`）提供了一个干净、高层次的代数接口。

### 文件结构
1.  **Lifting Constructors**: 定义了两个核心的构造器 `lift_block` 和 `lift_diag`。
2.  **Property-Preserving Lemmas**: 证明了这些构造器如何保持关键的矩阵属性
    （如置换、三角性）。
3.  **Algebraic Computation Lemmas**: 提供了用于验证分解方程（如 `P*A = L*U`）
    所需的核心代数计算引理。
-/

-- ==================================================================
-- Section 1: Lifting Constructors
-- ==================================================================

section LiftingConstructors

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [CommRing R]
variable {p_ι : ι → Prop} {p_κ : κ → Prop} [DecidablePred p_ι] [DecidablePred p_κ]
variable (e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}))
variable (e_κ : κ ≃ ({j // p_κ j} ⊕ {j // ¬p_κ j}))

/--
`lift_block` 将四个任意的分块矩阵 `M₁₁`, `M₁₂`, `M₂₁`, `M₂₂` 组装成一个
与原始矩阵 `A` 尺寸相同的完整矩阵。

这是最通用的分块构造器。
-/
def lift_block
    (M₁₁ : Matrix {i // p_ι i} {j // p_κ j} R) (M₁₂ : Matrix {i // p_ι i} {j // ¬p_κ j} R)
    (M₂₁ : Matrix {i // ¬p_ι i} {j // p_κ j} R) (M₂₂ : Matrix {i // ¬p_ι i} {j // ¬p_κ j} R) :
    Matrix ι κ R :=
  (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).reindex e_ι.symm e_κ.symm

/--
`lift_diag` 是 `lift_block` 的一个特例，用于构造块对角矩阵。
它将一个主块 `M₁₁` 放置在左上角，一个子矩阵 `M'` 放置在右下角，
其余非对角块填充为零。

这在构造置换矩阵 `P` 和单位下三角矩阵 `L` 时非常常用。
-/
def lift_diag [Zero R]
    (M₁₁ : Matrix {i // p_ι i} {j // p_κ j} R)
    (M' : Matrix {i // ¬p_ι i} {j // ¬p_κ j} R) : Matrix ι κ R :=
  lift_block e_ι e_κ M₁₁ 0 0 M'

end LiftingConstructors


-- ==================================================================
-- Section 2: Property-Preserving Lemmas
-- ==================================================================

section PropertyPreserving

variable {ι R : Type*} [CommRing R] [DecidableEq ι]
variable {p_ι : ι → Prop}
variable (e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}))



/--
**核心工具**: `lift_block` 保持上三角性。
一个通过 `lift_block` 构造的方阵是上三角的，当且仅当它的左下块 `M₂₁` 为零，
且对角块 `M₁₁` 和 `M₂₂` 都是上三角的。
-/
theorem lift_block_isUpperTriangular_iff [FinEnum ι] [DecidablePred p_ι]
    (M₁₁ : Matrix {i // p_ι i} {i // p_ι i} R)
    (M₁₂ : Matrix {i // p_ι i} {i // ¬p_ι i} R)
    (M₂₁ : Matrix {i // ¬p_ι i} {i // p_ι i} R)
    (M₂₂ : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) :
    IsUpperTriangular (lift_block e_ι e_ι M₁₁ M₁₂ M₂₁ M₂₂) ↔
    IsUpperTriangular M₁₁ ∧ IsUpperTriangular M₂₂ ∧ M₂₁ = 0 := by
  -- 明确使用由 FinEnum 诱导的线性序
  letI : LinearOrder ι := LinearOrder.ofFinEnum ι
  letI : LinearOrder {i // p_ι i} := LinearOrder.ofFinEnum {i // p_ι i}
  letI : LinearOrder {i // ¬p_ι i} := LinearOrder.ofFinEnum {i // ¬p_ι i}

  dsimp [IsUpperTriangular, lift_block]
  constructor
  · -- (→) 假设提升后的矩阵是上三角的
    intro h
    split_ands
    · -- 证明 M₁₁ 是上三角的
      intro i j hij
      specialize h (e_ι.symm (Sum.inl i)) (e_ι.symm (Sum.inl j))
      have h_order : e_ι.symm (Sum.inl j) < e_ι.symm (Sum.inl i) := by
        rw [e_ι.symm.lt_iff_lt]; exact hij
      specialize h h_order
      simpa [reindex_apply, Equiv.symm_apply_eq, fromBlocks_apply₁₁] using h
    · -- 证明 M₂₂ 是上三角的
      intro i j hij
      specialize h (e_ι.symm (Sum.inr i)) (e_ι.symm (Sum.inr j))
      have h_order : e_ι.symm (Sum.inr j) < e_ι.symm (Sum.inr i) := by
        rw [e_ι.symm.lt_iff_lt]; exact hij
      specialize h h_order
      simpa [reindex_apply, Equiv.symm_apply_eq, fromBlocks_apply₂₂] using h
    · -- 证明 M₂₁ = 0
      ext i j
      specialize h (e_ι.symm (Sum.inr i)) (e_ι.symm (Sum.inl j))
      have h_order : e_ι.symm (Sum.inl j) < e_ι.symm (Sum.inr i) := by
        rw [e_ι.symm.lt_iff_lt]
        -- 关键步骤：使用 equiv_sum_inl_lt_inr
        exact equiv_sum_inl_lt_inr j i
      specialize h h_order
      simpa [reindex_apply, Equiv.symm_apply_eq, fromBlocks_apply₂₁] using h
  · -- (←) 假设分块满足条件
    intro ⟨h₁₁, h₂₂, h₂₁_zero⟩
    intro i j hij
    simp_rw [reindex_apply, Equiv.symm_apply_eq]
    rcases e_ι i with (i₁ | i₂)
    rcases e_ι j with (j₁ | j₂)
    · -- Case 1: i, j 都在左上块
      simpa [fromBlocks_apply₁₁] using h₁₁ ((e_ι.lt_iff_lt).mpr hij)
    · -- Case 2: i 在左上块, j 在右下块
      -- 此时 j < i 不可能成立
      exfalso
      have h_contra := equiv_sum_inl_lt_inr i₁ j₂
      rw [← e_ι.symm.lt_iff_lt] at h_contra
      exact (not_le_of_lt hij) (le_of_lt h_contra)
    · -- Case 3: i 在右下块, j 在左上块
      -- 这是 M₂₁ 块, 假设为 0
      simp [fromBlocks_apply₂₁, h₂₁_zero]
    · -- Case 4: i, j 都在右下块
      simpa [fromBlocks_apply₂₂] using h₂₂ ((e_ι.lt_iff_lt).mpr hij)

/-- 分块提升保持 `IsUpperTriangular` 属性。 -/
lemma lift_block_preserves_IsUpperTriangular [FinEnum ι] [DecidablePred p_ι]
    (U₁₁ : Matrix {i // p_ι i} {i // p_ι i} R) (hU₁₁ : IsUpperTriangular U₁₁)
    (U₁₂ : Matrix {i // p_ι i} {i // ¬p_ι i} R)
    (U' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) (hU' : IsUpperTriangular U') :
    IsUpperTriangular (lift_block e_ι e_ι U₁₁ U₁₂ 0 U') := by
  rw [lift_block_isUpperTriangular_iff]
  exact ⟨hU₁₁, hU', rfl⟩


/-- 分块提升保持 `IsUnitLowerTriangular` 属性。 -/
lemma lift_block_preserves_IsUnitLowerTriangular [FinEnum ι] [DecidablePred p_ι]
    (L' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) (hL' : IsUnitLowerTriangular L')
    (L₂₁ : Matrix {i // ¬p_ι i} {i // p_ι i} R) :
    IsUnitLowerTriangular (lift_block e_ι e_ι 1 0 L₂₁ L') := by
  letI : LinearOrder ι := LinearOrder.ofFinEnum ι
  constructor
  · dsimp [IsLowerTriangular]
    rw [lift_block, transpose_reindex, fromBlocks_transpose]
    rw [← lift_block, lift_block_isUpperTriangular_iff]
    simp [isUpperTriangular_one]
    simp [IsUnitLowerTriangular, IsLowerTriangular] at hL'
    exact hL'.1
  · funext i
    rw [diag_apply, lift_block, reindex_apply, Equiv.symm_apply_eq]
    rcases e_ι i with (i₁ | i₂)
    · simp [fromBlocks_apply₁₁, diag_one]
    · simp [fromBlocks_apply₂₂, hL'.2]

/-- 对角提升保持 `IsPermutation` 属性。 -/
lemma lift_diag_preserves_IsPermutation
    (P' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) (hP' : IsPermutation P') :
    IsPermutation (lift_diag e_ι e_ι 1 P') := by
  rcases hP' with ⟨σ', h_eq⟩
  dsimp [IsPermutation]
  let σ_block := Equiv.Perm.sumCongr (Equiv.refl { i // p_ι i }) σ'
  let σ := e_ι.symm.permCongr σ_block
  use σ
  dsimp [lift_diag, lift_block, h_eq]
  have h_block_perm_matrix : (Equiv.toPEquiv σ_block).toMatrix = fromBlocks 1 0 0 P' := by
    ext i j
    rcases i with (i₁ | i₂) <;> rcases j with (j₁ | j₂) <;> simp [σ_block]
    · rfl
    · rw [h_eq]; simp
  rw [← h_block_perm_matrix]
  ext i j
  simp [PEquiv.toMatrix_apply, σ, Equiv.permCongr_apply, Equiv.symm_apply_eq]

/-- 对角提升保持 `IsUpperTriangular` 属性。 -/
lemma lift_diag_preserves_IsUpperTriangular [FinEnum ι] [DecidablePred p_ι]
    (U₁₁ : Matrix {i // p_ι i} {i // p_ι i} R) (hU₁₁ : IsUpperTriangular U₁₁)
    (U' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) (hU' : IsUpperTriangular U') :
    IsUpperTriangular (lift_diag e_ι e_ι U₁₁ U') := by
  rw [lift_diag, lift_block_isUpperTriangular_iff]
  exact ⟨hU₁₁, hU', rfl⟩

/-- 对角提升保持 `IsUnitLowerTriangular` 属性。 -/
lemma lift_diag_preserves_IsUnitLowerTriangular [FinEnum ι] [DecidablePred p_ι]
    (L₁₁ : Matrix {i // p_ι i} {i // p_ι i} R) (hL₁₁ : IsUnitLowerTriangular L₁₁)
    (L' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) (hL' : IsUnitLowerTriangular L') :
    IsUnitLowerTriangular (lift_diag e_ι e_ι L₁₁ L') := by
  letI : LinearOrder ι := LinearOrder.ofFinEnum ι
  constructor
  · dsimp [IsLowerTriangular]
    rw [lift_diag, lift_block, transpose_reindex, fromBlocks_transpose]
    rw [← lift_block, lift_block_isUpperTriangular_iff]
    exact ⟨hL₁₁.1, by simpa [IsLowerTriangular] using hL'.1⟩
  · funext i
    rw [diag_apply, lift_diag, lift_block, reindex_apply, Equiv.symm_apply_eq]
    rcases e_ι i with (i₁ | i₂)
    · simp [fromBlocks_apply₁₁, hL₁₁.2]
    · simp [fromBlocks_apply₂₂, hL'.2]

end PropertyPreserving


-- ==================================================================
-- Section 3: Algebraic Computation Lemmas
-- ==================================================================

section AlgebraicComputation

variable {ι κ R : Type*} [FinEnum ι] [Field R] [DecidableEq ι]
variable {p_ι : ι → Prop} {p_κ : κ → Prop} [DecidablePred p_ι]
variable (e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}))
variable (e_κ : κ ≃ ({j // p_κ j} ⊕ {j // ¬p_κ j}))

/--
**代数积木 1**: `(lift P) * A` 的分块形式。
用于计算 `P * A`。
-/
lemma lift_diag_P_mul_A
    (A : Matrix ι κ R)
    (P' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) :
    let P_lifted := lift_diag e_ι e_ι 1 P'
    let A_reindexed := reindex e_ι e_κ A
    P_lifted * A = lift_block e_ι e_κ
      A_reindexed.toBlocks₁₁
      A_reindexed.toBlocks₁₂
      (P' * A_reindexed.toBlocks₂₁)
      (P' * A_reindexed.toBlocks₂₂) := by
  classical
  intro P_lifted A_reindexed
  -- Expand the local definitions.
  dsimp [P_lifted, A_reindexed, lift_diag, lift_block]
  -- Work with a shorter name for the reindexed matrix.
  set A' := reindex e_ι e_κ A
  have hA : A = reindex e_ι.symm e_κ.symm A' := by
    subst A'
    ext i j
    simp
  -- Push the reindexing across the multiplication.
  calc
    (reindex e_ι.symm e_ι.symm (fromBlocks 1 0 0 P')) * A =
        (reindex e_ι.symm e_ι.symm (fromBlocks 1 0 0 P')) *
          (reindex e_ι.symm e_κ.symm A') := by simp [hA]
    _ = reindex e_ι.symm e_κ.symm ((fromBlocks 1 0 0 P') * A') := by simp
    _ = reindex e_ι.symm e_κ.symm
          (fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ (P' * A'.toBlocks₂₁) (P' * A'.toBlocks₂₂)) := by
          -- Rewrite the right factor as a block matrix and simplify the block multiplication.
          have h_mul_blocks :
              (fromBlocks 1 0 0 P') * A' = fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂
                (P' * A'.toBlocks₂₁) (P' * A'.toBlocks₂₂) := by
            -- First, express `A'` itself as a block matrix.
            have h_toBlocks :
                fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁ A'.toBlocks₂₂ = A' := by
              simpa using (fromBlocks_toBlocks A')
            calc
              (fromBlocks 1 0 0 P') * A'
                  = (fromBlocks 1 0 0 P') *
                    fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁ A'.toBlocks₂₂ := by
                      simp [h_toBlocks]
              _ = fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ (P' * A'.toBlocks₂₁)
                (P' * A'.toBlocks₂₂) := by
                simp [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul,
                  zero_add, add_zero]
          simp [h_mul_blocks]
    _ = lift_block e_ι e_κ A'.toBlocks₁₁ A'.toBlocks₁₂ (P' * A'.toBlocks₂₁)
      (P' * A'.toBlocks₂₂) := by simp [lift_block]
    _ = lift_block e_ι e_κ
          (reindex e_ι e_κ A).toBlocks₁₁
          (reindex e_ι e_κ A).toBlocks₁₂
          (P' * (reindex e_ι e_κ A).toBlocks₂₁)
          (P' * (reindex e_ι e_κ A).toBlocks₂₂) := by
          subst A'
          rfl

/--
**代数积木 2**: `(lift L) * (lift U)` 的分块形式。
用于计算 `L * U`。
-/
lemma lift_L_mul_lift_U
    (L₂₁ : Matrix {i // ¬p_ι i} {i // p_ι i} R)
    (L' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R)
    (U₁₁ : Matrix {i // p_ι i} {i // p_ι i} R)
    (U₁₂ : Matrix {i // p_ι i} {i // ¬p_ι i} R)
    (U' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) :
    let L_lifted := lift_block e_ι e_ι 1 0 L₂₁ L'
    let U_lifted := lift_block e_ι e_ι U₁₁ U₁₂ 0 U'
    L_lifted * U_lifted = lift_block e_ι e_ι
      U₁₁
      U₁₂
      (L₂₁ * U₁₁)
      (L₂₁ * U₁₂ + L' * U') := by
  classical
  intro L_lifted U_lifted
  -- Expand definitions.
  dsimp [L_lifted, U_lifted, lift_block]
  -- Push reindexing across the multiplication.
  have h_mul :
      reindex e_ι.symm e_ι.symm (fromBlocks 1 0 L₂₁ L') *
        reindex e_ι.symm e_ι.symm (fromBlocks U₁₁ U₁₂ 0 U') =
          reindex e_ι.symm e_ι.symm
            ((fromBlocks 1 0 L₂₁ L') * (fromBlocks U₁₁ U₁₂ 0 U')) := by simp
  calc
    reindex e_ι.symm e_ι.symm (fromBlocks 1 0 L₂₁ L') *
        reindex e_ι.symm e_ι.symm (fromBlocks U₁₁ U₁₂ 0 U') =
        reindex e_ι.symm e_ι.symm
          ((fromBlocks 1 0 L₂₁ L') * (fromBlocks U₁₁ U₁₂ 0 U')) := h_mul
    _ =
        reindex e_ι.symm e_ι.symm
          (fromBlocks U₁₁ U₁₂ (L₂₁ * U₁₁) (L₂₁ * U₁₂ + L' * U')) := by
        simp [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_zero,
          Matrix.zero_mul, add_zero]
    _ =
        lift_block e_ι e_ι U₁₁ U₁₂ (L₂₁ * U₁₁) (L₂₁ * U₁₂ + L' * U') := by
        simp [lift_block]

/--
**代数积木 3**: `(lift_diag L) * (lift_block U)` 的分块形式。
用于 `ZeroColumn` 情况下的 `L * U` 计算。
-/
lemma lift_diag_L_mul_lift_block_U
    (L' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R)
    (U₁₂ : Matrix {i // p_ι i} {i // ¬p_ι i} R)
    (U' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) :
    let L_lifted := lift_diag e_ι e_ι 1 L'
    let U_lifted := lift_block e_ι e_ι 0 U₁₂ 0 U'
    L_lifted * U_lifted = lift_block e_ι e_ι
      0
      U₁₂
      0
      (L' * U') := by
  classical
  intro L_lifted U_lifted
  -- Expand definitions.
  dsimp [L_lifted, U_lifted, lift_diag, lift_block]
  -- Push reindexing through the multiplication.
  have h_mul :
      reindex e_ι.symm e_ι.symm (fromBlocks 1 0 0 L') *
        reindex e_ι.symm e_ι.symm (fromBlocks 0 U₁₂ 0 U') =
          reindex e_ι.symm e_ι.symm
            ((fromBlocks 1 0 0 L') * (fromBlocks 0 U₁₂ 0 U')) := by simp
  calc
    reindex e_ι.symm e_ι.symm (fromBlocks 1 0 0 L') *
        reindex e_ι.symm e_ι.symm (fromBlocks 0 U₁₂ 0 U') =
        reindex e_ι.symm e_ι.symm
          ((fromBlocks 1 0 0 L') * (fromBlocks 0 U₁₂ 0 U')) := h_mul
    _ =
        reindex e_ι.symm e_ι.symm
          (fromBlocks 0 U₁₂ 0 (L' * U')) := by
        simp [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_zero,
          Matrix.zero_mul, zero_add, add_zero]
    _ =
        lift_block e_ι e_ι 0 U₁₂ 0 (L' * U') := by
        simp [lift_block]

end AlgebraicComputation

end MatDecompFormal.Components
