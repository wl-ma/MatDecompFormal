import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Defs.PartialOrder

set_option maxHeartbeats 2000000

namespace FinEnum

variable {α β : Type*} [FinEnum α] [FinEnum β]
#check FinEnum.sum
/--
`FinEnum.equiv_sum_inl_lt_inr` 证明了在 `FinEnum` 为 `Sum` 类型 `α ⊕ β`
构造的双射 `equiv` 中，任何来自左侧 `α` 的元素，其枚举顺序总是严格小于
任何来自右侧 `β` 的元素。
-/
lemma equiv_sum_inl_lt_inr (a : α) (b : β) :
    equiv (Sum.inl a) < equiv (Sum.inr b) := by
  classical
  -- 使用 `DecidableEq` 提供的默认 `BEq` 实例，避免 `Sum.instBEq` 带来的冲突
  letI : BEq (α ⊕ β) := instBEqOfDecidableEq (α := α ⊕ β)
  letI : LawfulBEq (α ⊕ β) := inferInstance
  -- `FinEnum.sum` 的枚举列表：先 `α` 后 `β`
  let xs : List (α ⊕ β) := (toList α).map Sum.inl
  let ys : List (α ⊕ β) := (toList β).map Sum.inr

  have hxs : xs.Nodup := by
    dsimp [xs]
    simpa using
      (List.nodup_map_iff (f := Sum.inl) (l := toList α) (hf := Sum.inl_injective)).2
        (nodup_toList (α := α))
  have hys : ys.Nodup := by
    dsimp [ys]
    simpa using
      (List.nodup_map_iff (f := Sum.inr) (l := toList β) (hf := Sum.inr_injective)).2
        (nodup_toList (α := β))
  have hdisj : List.Disjoint xs ys := by
    refine List.disjoint_left.mpr ?_
    intro x hx hy
    cases x <;> simp [xs, ys] at hx hy
  have hnodup : (xs ++ ys).Nodup := hxs.append hys hdisj

  -- 将不等式转化为索引比较
  change (equiv (Sum.inl a)).val < (equiv (Sum.inr b)).val
  simp [FinEnum.sum, FinEnum.ofList, FinEnum.ofNodupList, xs, ys,
    List.dedup_eq_self.mpr hnodup]
  -- 目标化为 `idxOf` 上的简单算术
  have h_inl_mem : Sum.inl a ∈ xs := by dsimp [xs]; simp
  have h_inr_not_mem : Sum.inr b ∉ xs := by dsimp [xs]; simp
  have h_inl_idx :
      (xs ++ ys).idxOf (Sum.inl a) = xs.idxOf (Sum.inl a) :=
    List.idxOf_append_of_mem (a := Sum.inl a) (l₁ := xs) (l₂ := ys) h_inl_mem
  have h_inr_idx :
      (xs ++ ys).idxOf (Sum.inr b) = xs.length + ys.idxOf (Sum.inr b) :=
    List.idxOf_append_of_notMem (a := Sum.inr b) (l₁ := xs) (l₂ := ys) h_inr_not_mem
  have h_inl_lt : xs.idxOf (Sum.inl a) < xs.length :=
    List.idxOf_lt_length_iff.mpr h_inl_mem
  have h_goal : xs.idxOf (Sum.inl a) < xs.length + ys.idxOf (Sum.inr b) :=
    Nat.lt_of_lt_of_le h_inl_lt (Nat.le_add_right _ _)
  have h_idx :
      (xs ++ ys).idxOf (Sum.inl a) < (xs ++ ys).idxOf (Sum.inr b) := by
    simpa [h_inl_idx, h_inr_idx] using h_goal
  simpa [xs, ys] using h_idx

/-- 这是一个方便的推论，用于在证明中制造矛盾 -/
lemma not_equiv_sum_inr_lt_inl (a : α) (b : β) :
    ¬ (equiv (Sum.inr b) < equiv (Sum.inl a)) :=
  not_lt.mpr (le_of_lt (equiv_sum_inl_lt_inr a b))

instance instPreorderFromFinEnum {ι : Type*} [FinEnum ι] : Preorder ι where
  le i j := (equiv i).val ≤ (equiv j).val
  le_refl i := le_rfl
  le_trans i j k := Nat.le_trans

-- lemma sum_inl_lt_inr (a : α) (b : β) : Sum.inl a < Sum.inr b := by
--   -- 这现在直接来自于 Mathlib 为 Sum 类型定义的 Preorder 实例
--   -- rw [toLex]
--   change toLex (Sum.inl a) < toLex (Sum.inr b)
--   exact Sum.Lex.inl_lt_inr a b

end FinEnum

#check Matrix.BlockTriangular.submatrix
namespace MatDecompFormal.Components

open Matrix FinEnum MatDecompFormal.Components.Properties

/-!
# 分块矩阵提升引理 (Block Matrix Lifting Lemmas) - v2.1 (重构版)

本文件提供了一套用于处理分块矩阵“提升”操作的通用代数工具。
这个版本的设计哲学是**提供直接、高层次的引理**，将所有关于 `reindex`
和 `Equiv` 的复杂细节完全封装起来，为上层证明提供一个干净的接口。
-/

-- ==================================================================
-- Section 1: Lifting Constructors
-- ==================================================================

section LiftingConstructors

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [CommRing R]
variable {p_ι : ι → Prop} {p_κ : κ → Prop} [DecidablePred p_ι] [DecidablePred p_κ]
variable (e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}))
variable (e_κ : κ ≃ ({j // p_κ j} ⊕ {j // ¬p_κ j}))

/-- `lift_block`: 将四个分块矩阵组装成一个原始尺寸的矩阵。 -/
def lift_block
    (M₁₁ : Matrix {i // p_ι i} {j // p_κ j} R) (M₁₂ : Matrix {i // p_ι i} {j // ¬p_κ j} R)
    (M₂₁ : Matrix {i // ¬p_ι i} {j // p_κ j} R) (M₂₂ : Matrix {i // ¬p_ι i} {j // ¬p_κ j} R) :
    Matrix ι κ R :=
  (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).reindex e_ι.symm e_κ.symm

/-- `lift_diag`: 将一个子矩阵 `M'` 放置在右下角，一个主块 `M₁₁` 放置在左上角。 -/
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

/-- 对角提升保持 `IsPermutation` 属性。 -/
lemma lift_diag_preserves_IsPermutation (M' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R)
    (hM' : IsPermutation M') :
    IsPermutation (lift_diag e_ι e_ι 1 M') := by
  rcases hM' with ⟨σ', h_eq⟩
  dsimp [IsPermutation]
  let σ_block := Equiv.Perm.sumCongr (Equiv.refl { i // p_ι i }) σ'
  let σ := e_ι.symm.permCongr σ_block
  use σ
  dsimp [lift_diag, lift_block, h_eq]
  have h_block_perm_matrix : (Equiv.toPEquiv σ_block).toMatrix = fromBlocks 1 0 0 M' := by
    simp [σ_block]
    rw [h_eq]
    funext i j
    rcases i with (i₁ | i₂) <;> rcases j with (j₁ | j₂) <;> simp
    rfl
  funext i j
  rw [submatrix_apply, PEquiv.toMatrix_apply]
  dsimp [σ, Equiv.permCongr_apply]
  simp [e_ι.symm_apply_eq]
  rw [← h_block_perm_matrix]
  simp

/-!
**核心工具**: `lift_block` 保持上三角性。
一个通过 `lift_block` 构造的方阵是上三角的，当且仅当它的右下块为零，
且对角块 `M₁₁` 和 `M₂₂` 都是上三角的。
-/
theorem lift_block_isUpperTriangular_iff [FinEnum ι] [DecidablePred p_ι]
    (M₁₁ : Matrix {i // p_ι i} {i // p_ι i} R)
    (M₁₂ : Matrix {i // p_ι i} {i // ¬p_ι i} R)
    (M₂₁ : Matrix {i // ¬p_ι i} {i // p_ι i} R)
    (M₂₂ : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) :
    IsUpperTriangular (lift_block e_ι e_ι M₁₁ M₁₂ M₂₁ M₂₂) ↔
    IsUpperTriangular M₁₁ ∧ IsUpperTriangular M₂₂ ∧ M₂₁ = 0 := by
  classical
  -- Transport the `FinEnum` structure on `ι` so that the enumeration order matches the block split.
  letI : FinEnum ι := FinEnum.ofEquiv ({i // p_ι i} ⊕ {i // ¬p_ι i}) e_ι
  -- Handy rewrites for the various `equiv` applications we will encounter.
  have h_equiv_ι :
      (equiv (α := ι)) =
        e_ι.trans (equiv (α := ({i // p_ι i} ⊕ {i // ¬p_ι i}))) := rfl
  have h_equiv_inl (x : {i // p_ι i}) :
      (equiv (α := {i // p_ι i})) x =
        (equiv (α := ({i // p_ι i} ⊕ {i // ¬p_ι i}))) (Sum.inl x) := by
    simp [FinEnum.sum]
  have h_equiv_inr (x : {i // ¬p_ι i}) :
      (equiv (α := {i // ¬p_ι i})) x =
        (equiv (α := ({i // p_ι i} ⊕ {i // ¬p_ι i}))) (Sum.inr x) := by
    simp [FinEnum.sum]
  -- Reindex the triangular condition to the sum index.
  have h_reindex :
      IsUpperTriangular (lift_block e_ι e_ι M₁₁ M₁₂ M₂₁ M₂₂) ↔
        BlockTriangular (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂)
          (equiv (α := ({i // p_ι i} ⊕ {i // ¬p_ι i}))) := by
    dsimp [IsUpperTriangular, lift_block]
    simpa [BlockTriangular, h_equiv_ι, Equiv.trans_apply] using
      (blockTriangular_reindex_iff
        (M := fromBlocks M₁₁ M₁₂ M₂₁ M₂₂)
        (b := (equiv (α := ι)))
        (e := e_ι.symm))
  constructor
  · -- (→) 假设提升后的矩阵是上三角的
    intro h
    have h_sum := (h_reindex.mp h)
    -- 下左块必须为零
    have h_M21_zero : M₂₁ = 0 := by
      funext i j; exact h_sum (FinEnum.equiv_sum_inl_lt_inr j i)
    -- 子矩阵的上三角性由 `Matrix.BlockTriangular.submatrix` 获得
    have h₁₁' :
        BlockTriangular M₁₁
          ((equiv (α := ({i // p_ι i} ⊕ {i // ¬p_ι i}))) ∘ Sum.inl) :=
      (Matrix.BlockTriangular.submatrix (f := Sum.inl) h_sum)
    have h₂₂' :
        BlockTriangular M₂₂
          ((equiv (α := ({i // p_ι i} ⊕ {i // ¬p_ι i}))) ∘ Sum.inr) :=
      (Matrix.BlockTriangular.submatrix (f := Sum.inr) h_sum)
    refine ⟨?_, ?_, h_M21_zero⟩
    · -- 左上块上三角
      intro i j hij
      have hij' :
          (equiv (α := ({i // p_ι i} ⊕ {i // ¬p_ι i}))) (Sum.inl j) <
            (equiv (α := ({i // p_ι i} ⊕ {i // ¬p_ι i}))) (Sum.inl i) := by
        simpa [h_equiv_inl] using hij
      simpa using h₁₁' hij'
    · -- 右下块上三角
      intro i j hij
      have hij' :
          (equiv (α := ({i // p_ι i} ⊕ {i // ¬p_ι i}))) (Sum.inr j) <
            (equiv (α := ({i // p_ι i} ⊕ {i // ¬p_ι i}))) (Sum.inr i) := by
        simpa [h_equiv_inr] using hij
      simpa using h₂₂' hij'
  · -- (←) 假设分块满足条件
    intro ⟨h₁₁, h₂₂, h₂₁⟩
    -- 先在 sum 索引下拼装出上三角性
    have h_sum : BlockTriangular (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂)
        (equiv (α := ({i // p_ι i} ⊕ {i // ¬p_ι i}))) := by
      intro i j hlt
      cases i <;> cases j
      · -- 左上块
        exact h₁₁ (by simpa [h_equiv_inl] using hlt)
      · -- 右上块：无约束
        simp
      · -- 左下块：被假设为零，与顺序矛盾
        have : False := FinEnum.not_equiv_sum_inr_lt_inl _ _ hlt
        simpa [h₂₁] using this.elim
      · -- 右下块
        exact h₂₂ (by simpa [h_equiv_inr] using hlt)
    -- 再用 reindex 还原到原索引
    exact h_reindex.mpr h_sum

/-- 分块提升保持 `IsUnitLowerTriangular` 属性。 -/
lemma lift_block_preserves_IsUnitLowerTriangular [FinEnum ι] [DecidablePred p_ι]
    (L' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R)
    (L₂₁ : Matrix {i // ¬p_ι i} {i // p_ι i} R)
    (hL' : IsUnitLowerTriangular L') :
    IsUnitLowerTriangular (lift_block e_ι e_ι 1 0 L₂₁ L') := by
  constructor
  · -- 证明下三角性
    dsimp [IsLowerTriangular]
    rw [lift_block, transpose_reindex, fromBlocks_transpose]
    -- 转置后，目标是证明它是上三角的
    rw [lift_block_isUpperTriangular_iff]
    simp [hL'.1]
  · -- 证明对角线为 1
    funext i
    rw [diag_apply, lift_block, reindex_apply, Equiv.symm_apply_eq]
    rcases e_ι i with (i₁ | i₂)
    · simp [fromBlocks_apply₁₁]
    · simp [fromBlocks_apply₂₂, hL'.2]

/-- 分块提升保持 `IsUpperTriangular` 属性。 -/
lemma lift_block_preserves_IsUpperTriangular [FinEnum ι] [DecidablePred p_ι]
    (U' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R)
    (U₁₁ : Matrix {i // p_ι i} {i // p_ι i} R) (hU₁₁ : IsUpperTriangular U₁₁)
    (U₁₂ : Matrix {i // p_ι i} {i // ¬p_ι i} R)
    (hU' : IsUpperTriangular U') :
    IsUpperTriangular (lift_block e_ι e_ι U₁₁ U₁₂ 0 U') := by
  rw [lift_block_isUpperTriangular_iff]
  exact ⟨hU₁₁, hU', rfl⟩

end PropertyPreserving


-- ==================================================================
-- Section 3: Algebraic Computation Lemmas (通用代数积木)
-- ==================================================================

section AlgebraicComputation

variable {ι R : Type*} [FinEnum ι] [Field R] [DecidableEq ι]
variable {p_ι : ι → Prop} [DecidablePred p_ι]
variable (e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}))

/--
**代数积木 1**: `(lift P) * A` 的分块形式。
-/
lemma lift_P_mul_A
    (A : Matrix ι ι R)
    (P' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) :
    let P_lifted := lift_diag e_ι e_ι 1 P'
    let A_reindexed := reindex e_ι e_ι A
    P_lifted * A = lift_block e_ι e_ι
      A_reindexed.toBlocks₁₁
      A_reindexed.toBlocks₁₂
      (P' * A_reindexed.toBlocks₂₁)
      (P' * A_reindexed.toBlocks₂₂) := by
  intro P_lifted A_reindexed
  rw [P_lifted, lift_diag, lift_block, ← reindex_mul, fromBlocks_multiply]
  simp

/--
**代数积木 2**: `(lift L) * (lift U)` 的分块形式。
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
      (L₂₁ * U₁₁ + L' * 0)
      (L₂₁ * U₁₂ + L' * U') := by
  intro L_lifted U_lifted
  rw [L_lifted, U_lifted, lift_block, lift_block, ← reindex_mul, fromBlocks_multiply]
  rfl

end AlgebraicComputation

end MatDecompFormal.Components














-- import MatDecompFormal.Components.Properties.Permutation
-- import MatDecompFormal.Components.Properties.Triangular
-- import Mathlib.LinearAlgebra.Matrix.Block
-- import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


-- namespace FinEnum

-- variable {α β : Type*} [FinEnum α] [FinEnum β]
-- #check FinEnum.sum
-- #check Sum.Lex.inl_lt_inr
-- #check List.Disjoint
-- /--
-- `FinEnum.equiv_sum_inl_lt_inr` 证明了在 `FinEnum` 为 `Sum` 类型 `α ⊕ β`
-- 构造的双射 `equiv` 中，任何来自左侧 `α` 的元素，其枚举顺序总是严格小于
-- 任何来自右侧 `β` 的元素。

-- 这个序关系来自于 `Mathlib` 为 `Sum` 类型的 `FinEnum` 实例提供的规范化构造。
-- 该构造通过 `finSumFinEquiv` 实现，它总是先将 `α` 的 `card α` 个元素映射到
-- `Fin (card α + card β)` 的前 `card α` 个索引，然后再将 `β` 的 `card β` 个
-- 元素映射到后面的 `card β` 个索引。

-- 这个引理是证明分块矩阵三角性保持的关键。
-- -/
-- lemma equiv_sum_inl_lt_inr (a : α) (b : β) :
--     equiv (Sum.inl a) < equiv (Sum.inr b) := by
--   -- 目标：`equiv (Sum.inl a) < equiv (Sum.inr b)`

--   -- 步骤 1: 将对 `Fin n` 类型的比较，转化为对其底层自然数值 `.val` 的比较。
--   -- 这是处理 `Fin` 类型不等式的标准做法。
--   have h_target_iff_val_lt : equiv (Sum.inl a) < equiv (Sum.inr b) ↔
--       (equiv (@Sum.inl α β a)).val < (equiv (@Sum.inr α β b)).val := by
--     exact Fin.lt_def.symm
--   rw [h_target_iff_val_lt]
--   -- 新目标：`(equiv (Sum.inl a)).val < (equiv (Sum.inr b)).val`

--   -- 步骤 2: 计算不等式左侧 `(equiv (Sum.inl a)).val` 的值。
--   -- Mathlib 提供了 `FinEnum.equiv_sum_inl` 引理，它精确地描述了 `equiv` 如何作用于 `Sum.inl`。
--   -- `equiv (Sum.inl a)` 被映射为 `Fin.castAdd (card β) (equiv a)`，其 `.val` 就是 `(equiv a).val`。
--   have h_lhs_val : (equiv (@Sum.inl α β a)).val = (equiv a).val := by
--     sorry
--   rw [h_lhs_val]
--   -- 新目标：`(equiv a).val < (equiv (Sum.inr b)).val`

--   -- 步骤 3: 计算不等式右侧 `(equiv (Sum.inr b)).val` 的值。
--   -- 同样，`FinEnum.equiv_sum_inr` 描述了 `equiv` 如何作用于 `Sum.inr`。
--   -- `equiv (Sum.inr b)` 被映射为 `Fin.natAdd (card α) (equiv b)`，其 `.val` 就是 `card α + (equiv b).val`。
--   have h_rhs_val : (equiv (@Sum.inr α β b)).val = card α + (equiv b).val := by
--     sorry
--   rw [h_rhs_val]
--   -- 新目标：`(equiv a).val < card α + (equiv b).val`

--   -- 步骤 4: 证明最终的自然数不等式。
--   -- 我们知道 `equiv a` 是 `Fin (card α)` 类型的一个元素，所以它的值 `.val` 必然小于 `card α`。
--   have h_a_val_lt_card : (equiv a).val < card α := by
--     exact (equiv a).isLt

--   -- 因为 `(equiv a).val < card α`，且 `card α ≤ card α + (equiv b).val` (因为 `.val` 是自然数，非负)。
--   -- 通过不等式的传递性，即可得证。
--   have h_final_inequality : (equiv a).val < card α + (equiv b).val := by
--     apply Nat.lt_of_lt_of_le
--     · exact h_a_val_lt_card
--     · exact Nat.le_add_right (card α) (equiv b).val

--   exact h_final_inequality

-- -- 这是一个方便的推论，用于在证明中制造矛盾
-- lemma not_equiv_sum_inr_lt_inl (a : α) (b : β) :
--     ¬ (equiv (Sum.inr b) < equiv (Sum.inl a)) :=
--   not_lt.mpr (le_of_lt (equiv_sum_inl_lt_inr a b))

-- end FinEnum


-- namespace MatDecompFormal.Components

-- open Matrix FinEnum MatDecompFormal.Components.Properties

-- /-!
-- # 分块矩阵提升引理 (Block Matrix Lifting Lemmas) - v2.0 (通用版)

-- 本文件提供了一套用于处理分块矩阵“提升”操作的通用代数工具。
-- 这个版本的设计哲学是**提供纯粹的构造块，而不是预设的完整方程**。
-- 它将具体的分解逻辑（如 `P*A = L*U`）完全留给最终的实例文件去组装。

-- ### 核心功能
-- 1.  **提升构造器 (`lift_block`, `lift_diag`)**:
--     提供了从分块矩阵组装回原始尺寸矩阵的便捷定义。

-- 2.  **属性保持引理 (`..._preserves_...`)**:
--     证明了如果子矩阵具有某些代数属性（如 `IsPermutation`），
--     那么通过提升操作构造出的完整矩阵也会保持这些属性。

-- 3.  **代数计算引理 (`lift_mul_lift_eq_...`)**:
--     提供了关于“提升后的矩阵相乘”等于“提升另一个组合矩阵”的引理。
--     这些是用于在实例文件中组装最终方程的“代数积木”。
-- -/

-- -- ==================================================================
-- -- Section 1: Lifting Constructors (保持不变)
-- -- ==================================================================

-- section LiftingConstructors

-- variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [CommRing R]
-- variable {p_ι : ι → Prop} {p_κ : κ → Prop} [DecidablePred p_ι] [DecidablePred p_κ]
-- variable (e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}))
-- variable (e_κ : κ ≃ ({j // p_κ j} ⊕ {j // ¬p_κ j}))

-- /-- `lift_block`: 将四个分块矩阵组装成一个原始尺寸的矩阵。 -/
-- def lift_block
--     (M₁₁ : Matrix {i // p_ι i} {j // p_κ j} R) (M₁₂ : Matrix {i // p_ι i} {j // ¬p_κ j} R)
--     (M₂₁ : Matrix {i // ¬p_ι i} {j // p_κ j} R) (M₂₂ : Matrix {i // ¬p_ι i} {j // ¬p_κ j} R) :
--     Matrix ι κ R :=
--   (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).reindex e_ι.symm e_κ.symm

-- /-- `lift_diag`: 将一个子矩阵 `M'` 放置在右下角，一个主块 `M₁₁` 放置在左上角。 -/
-- def lift_diag [Zero R]
--     (M₁₁ : Matrix {i // p_ι i} {j // p_κ j} R)
--     (M' : Matrix {i // ¬p_ι i} {j // ¬p_κ j} R) : Matrix ι κ R :=
--   lift_block e_ι e_κ M₁₁ 0 0 M'

-- end LiftingConstructors


-- -- ==================================================================
-- -- Section 2: Property-Preserving Lemmas (保持不变)
-- -- ==================================================================

-- section PropertyPreserving

-- variable {ι R : Type*} [CommRing R] [DecidableEq ι]
-- variable {p_ι : ι → Prop} --[DecidablePred p_ι]
-- variable (e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}))

-- /-- 对角提升保持 `IsPermutation` 属性。 -/
-- lemma lift_diag_preserves_IsPermutation (M' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R)
--     (hM' : IsPermutation M') :
--     IsPermutation (lift_diag e_ι e_ι 1 M') := by
--   rcases hM' with ⟨σ', h_eq⟩
--   dsimp [IsPermutation]
--   let σ_block := Equiv.Perm.sumCongr (Equiv.refl { i // p_ι i }) σ'
--   let σ := e_ι.symm.permCongr σ_block
--   use σ
--   dsimp [lift_diag, lift_block, h_eq]
--   have h_block_perm_matrix : (Equiv.toPEquiv σ_block).toMatrix = fromBlocks 1 0 0 M' := by
--     simp [σ_block]
--     rw [h_eq]
--     funext i j
--     rcases i with (i₁ | i₂) <;> rcases j with (j₁ | j₂) <;> simp
--     rfl
--   funext i j
--   rw [submatrix_apply, PEquiv.toMatrix_apply]
--   dsimp [σ, Equiv.permCongr_apply]
--   simp [e_ι.symm_apply_eq]
--   rw [← h_block_perm_matrix]
--   simp


-- -- /--
-- -- `sumCompl_inl_lt_inr` 证明了通过 `Equiv.sumCompl` 映射后，
-- -- 来自第一个集合（满足 `p`）的任何元素，在 `FinEnum.equiv` 的顺序下，
-- -- 总是位于来自第二个集合（不满足 `p`）的任何元素之前。

-- -- 这个序关系并非来自 `ι` 上的任何固有顺序，而是来自于 `Mathlib`
-- -- 为 `Sum` 类型 (`⊕`) 的 `FinEnum` 实例提供的规范化构造。该构造
-- -- 通过 `finSumFinEquiv` 实现，它总是先枚举 `Sum.inl` 的所有元素，
-- -- 然后再枚举 `Sum.inr` 的所有元素。
-- -- -/
-- -- lemma sumCompl_inl_lt_inr [FinEnum ι] [DecidablePred p_ι]
-- --     (x : {i // p_ι i}) (y : {i // ¬p_ι i}) :
-- --     (equiv ∘ (Equiv.sumCompl p_ι)) (Sum.inl x) < (equiv ∘ (Equiv.sumCompl p_ι)) (Sum.inr y) := by
-- --   -- 展开函数组合
-- --   dsimp only [Function.comp_apply]
-- --   -- `FinEnum (A ⊕ B)` 的 `equiv` 是通过 `finSumFinEquiv` 和各个部分的 `equiv` 组合而成的。
-- --   -- 我们需要展开这个定义。`equiv_sum_congr` 引理可以帮助我们。
-- --   rw [equiv_sum_congr (finEnum (p := p)).equiv (finEnum (p := ¬p)).equiv]
-- --   -- `Equiv.sumCompl p` 作用于 `Sum.inl x` 和 `Sum.inr y`
-- --   simp only [Sum.map_inl, Sum.map_inr]
-- --   -- 现在目标是 `finSumFinEquiv (Sum.inl (equiv x)) < finSumFinEquiv (Sum.inr (equiv y))`
-- --   -- 展开 `finSumFinEquiv` 的定义
-- --   dsimp [finSumFinEquiv]
-- --   -- 目标变为 `Fin.castAdd (card { i // ¬p i }) (equiv x) < Fin.natAdd (card { i // p i }) (equiv y)`
-- --   -- 比较 `Fin` 类型的值需要比较它们的 `.val`
-- --   rw [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
-- --   -- 目标是 `(equiv x).val < card { i // p i } + (equiv y).val`
-- --   -- `equiv x` 是 `Fin (card {i // p i})` 类型, 所以 `(equiv x).val < card {i // p i}`
-- --   have h_x_lt_card : (equiv x).val < card { i // p i } := (equiv x).isLt
-- --   -- 因为 `(equiv y).val` 是非负的, 所以 `card {i // p i} ≤ card {i // p i} + (equiv y).val`
-- --   have h_le_add := Nat.le_add_right (card { i // p i }) (equiv y).val
-- --   -- 将两个不等式串联起来
-- --   exact lt_of_lt_of_le h_x_lt_card h_le_add

-- -- -- 这是一个方便的推论，用于在证明中制造矛盾
-- -- lemma not_sumCompl_inr_lt_inl [FinEnum ι] [DecidablePred p_ι]
-- --     (x : {i // p_ι i}) (y : {i // ¬p_ι i}) :
-- --     ¬ ((equiv ∘ (Equiv.sumCompl p_ι)) (Sum.inr y) <
-- --         (equiv ∘ (Equiv.sumCompl p_ι)) (Sum.inl x)) :=
-- --   not_lt.mpr (le_of_lt (sumCompl_inl_lt_inr x y))


-- /--
-- 一个通过 `(Equiv.sumCompl p).symm` 从分块矩阵构造的方阵是上三角的，当且仅当
-- 它的各个分块满足相应的三角性或为零条件。

-- 这个定理是证明 `lift_..._preserves_...` 引理的核心。它将一个在 `reindex` 后的
-- 矩阵的 `BlockTriangular` 性质，与原始分块的性质直接关联起来。
-- -/
-- theorem blockTriangular_reindex_fromBlocks_iff [FinEnum ι] [DecidablePred p_ι]
--     (M₁₁ : Matrix {i // p_ι i} {i // p_ι i} R)
--     (M₁₂ : Matrix {i // p_ι i} {i // ¬p_ι i} R)
--     (M₂₁ : Matrix {i // ¬p_ι i} {i // p_ι i} R)
--     (M₂₂ : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) :
--     BlockTriangular ((fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).reindex
--       (Equiv.sumCompl p_ι) (Equiv.sumCompl p_ι)) equiv ↔
--     BlockTriangular M₁₁ (equiv ∘ Subtype.val) ∧
--     BlockTriangular M₂₂ (equiv ∘ Subtype.val) ∧
--     M₂₁ = 0 := by
--     -- 使用 `blockTriangular_reindex_iff` 将问题转移到 reindex 之前
--   rw [blockTriangular_reindex_iff]
--   -- 现在的分块函数是 `equiv ∘ Equiv.sumCompl p_ι`
--   let b := equiv ∘ Equiv.sumCompl p_ι
--   dsimp [BlockTriangular]
--   constructor
--   · -- 方向 1: (→) 假设大矩阵是块上三角的
--     intro h_triangular
--     -- 1.1 证明 M₂₁ = 0
--     have h_M21_zero : M₂₁ = 0 := by
--       funext i j
--       -- M₂₁ i j 是大矩阵在 (Sum.inr i, Sum.inl j) 的元素
--       -- 我们需要证明前提 `b (Sum.inl j) < b (Sum.inr i)`
--       have h_order_ij : b (Sum.inl j) < b (Sum.inr i) := by
--         simp [b]
--         convert FinEnum.equiv_sum_inl_lt_inr j i
--         all_goals sorry
--       -- 应用大矩阵的上三角性
--       exact h_triangular h_order_ij
--     -- 1.2 证明 M₁₁ 是块上三角的
--     have h_M11_triangular : BlockTriangular M₁₁ (equiv ∘ Subtype.val) := by
--       intro i j h_order_ij
--       -- M₁₁ i j 是大矩阵在 (Sum.inl i, Sum.inl j) 的元素
--       have h_order_lifted : b (Sum.inl j) < b (Sum.inl i) := by
--         dsimp [b]
--         exact h_order_ij
--       exact h_triangular h_order_lifted
--     -- 1.3 证明 M₂₂ 是块上三角的
--     have h_M22_triangular : BlockTriangular M₂₂ (equiv ∘ Subtype.val) := by
--       intro i j h_order_ij
--       have h_order_lifted : b (Sum.inr j) < b (Sum.inr i) := by
--         dsimp [b]
--         exact h_order_ij
--       exact h_triangular h_order_lifted
--     -- 组装结果
--     exact ⟨h_M11_triangular, h_M22_triangular, h_M21_zero⟩

--   · -- 方向 2: (←) 假设分块满足条件
--     intro ⟨h_M11, h_M22, h_M21_zero⟩ i j h_order_ij
--     -- 对 i 和 j 的类型进行分情况讨论
--     rcases i with (i₁ | i₂)
--     · rcases j with (j₁ | j₂)
--       · -- Case 1.1: i, j 都在左上块
--         -- 目标是 M₁₁ i₁ j₁ = 0
--         apply h_M11
--         -- 将 h_order_ij 转换回 M₁₁ 需要的前提
--         dsimp [b] at h_order_ij
--         exact h_order_ij
--       · -- Case 1.2: i 在左上块, j 在右下块
--         -- h_order_ij 是 `b (Sum.inr j₂) < b (Sum.inl i₁)`
--         exfalso
--         apply FinEnum.not_equiv_sum_inr_lt_inl i₁ j₂
--         convert h_order_ij
--         all_goals sorry
--     · rcases j with (j₁ | j₂)
--       · -- Case 2.1: i 在右下块, j 在左上块
--         -- 目标是 M₂₁ i₂ j₁ = 0
--         rw [h_M21_zero]; rfl
--       · -- Case 2.2: i, j 都在右下块
--         -- 目标是 M₂₂ i₂ j₂ = 0
--         apply h_M22
--         dsimp [b] at h_order_ij
--         exact h_order_ij


-- /-- 分块提升保持 `IsUnitLowerTriangular` 属性。 -/
-- lemma lift_block_preserves_IsUnitLowerTriangular [FinEnum ι] [DecidablePred p_ι]
--     (L' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R)
--     (L₂₁ : Matrix {i // ¬p_ι i} {i // p_ι i} R)
--     (hL' : IsUnitLowerTriangular L') :
--     IsUnitLowerTriangular (lift_block e_ι e_ι 1 0 L₂₁ L') := by
--   dsimp [IsUnitLowerTriangular, IsLowerTriangular, IsUpperTriangular]
--   rw [lift_block, transpose_reindex, fromBlocks_transpose, blockTriangular_reindex_iff]
--   -- simp only [transpose_zero]
--   constructor
--   · -- 目标 1: 证明三角性
--     sorry

--   · -- 目标 2: 证明对角线为 1
--     funext i
--     rw [diag_apply, reindex_apply, Equiv.symm_symm, submatrix_apply]
--     rcases e_ι i with (i₁ | i₂)
--     · simp
--     · have h_elem_eq : L'.diag i₂ = (1 : { i // ¬p_ι i } → R) i₂ := by
--         rw [hL'.2]
--       simp [diag] at h_elem_eq
--       exact h_elem_eq

-- /-- 分块提升保持 `IsUpperTriangular` 属性。 -/
-- lemma lift_block_preserves_IsUpperTriangular [FinEnum ι]
--     [FinEnum { i // p_ι i }] [FinEnum { i // ¬p_ι i }]
--     (U' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R)
--     (U₁₁ : Matrix {i // p_ι i} {i // p_ι i} R) (hU₁₁ : IsUpperTriangular U₁₁)
--     (U₁₂ : Matrix {i // p_ι i} {i // ¬p_ι i} R)
--     (hU' : IsUpperTriangular U') :
--     IsUpperTriangular (lift_block e_ι e_ι U₁₁ U₁₂ 0 U') := by
--   dsimp [IsUpperTriangular]
--   rw [lift_block]
--   rw [blockTriangular_reindex_fromBlocks_iff]
--   -- refine ⟨hU₁₁, hU', by simp⟩

-- end PropertyPreserving


-- -- ==================================================================
-- -- Section 3: Algebraic Computation Lemmas (通用代数积木)
-- -- ==================================================================

-- section AlgebraicComputation

-- variable {ι R : Type*} [FinEnum ι] [Field R] [DecidableEq ι]
-- variable {p_ι : ι → Prop} [DecidablePred p_ι]
-- variable (e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}))

-- /--
-- **代数积木 1**: `(lift P) * A` 的分块形式。

-- 这个引理计算了“提升后的置换矩阵 `P`”与“原始矩阵 `A`”的乘积。
-- 结果是一个新的分块矩阵。
-- -/
-- lemma lift_P_mul_A
--     (A : Matrix ι ι R)
--     (P' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) :
--     let P_lifted := lift_diag e_ι e_ι 1 P'
--     let A_reindexed := reindex e_ι e_ι A
--     P_lifted * A = lift_block e_ι e_ι
--       A_reindexed.toBlocks₁₁
--       A_reindexed.toBlocks₁₂
--       (P' * A_reindexed.toBlocks₂₁)
--       (P' * A_reindexed.toBlocks₂₂) := by
--   intro P_lifted A_reindexed
--   simp [P_lifted, A_reindexed, lift_diag, lift_block]
--   sorry


-- /--
-- **代数积木 2**: `(lift L) * (lift U)` 的分块形式。

-- 这个引理计算了“提升后的下三角矩阵 `L`”与“提升后的上三角矩阵 `U`”的乘积。
-- 结果也是一个分块矩阵。
-- -/
-- lemma lift_L_mul_lift_U
--     (L₂₁ : Matrix {i // ¬p_ι i} {i // p_ι i} R)
--     (L' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R)
--     (U₁₁ : Matrix {i // p_ι i} {i // p_ι i} R)
--     (U₁₂ : Matrix {i // p_ι i} {i // ¬p_ι i} R)
--     (U' : Matrix {i // ¬p_ι i} {i // ¬p_ι i} R) :
--     let L_lifted := lift_block e_ι e_ι 1 0 L₂₁ L'
--     let U_lifted := lift_block e_ι e_ι U₁₁ U₁₂ 0 U'
--     L_lifted * U_lifted = lift_block e_ι e_ι
--       U₁₁
--       U₁₂
--       (L₂₁ * U₁₁ + L' * (0 : Matrix {i // ¬p_ι i} {i // p_ι i} R)) -- Simplified to L₂₁ * U₁₁
--       (L₂₁ * U₁₂ + L' * U') := by
--   intro L_lifted U_lifted
--   simp_rw [L_lifted, U_lifted, lift_block]
--   sorry
--   -- rw [fromBlocks_multiply]
--   -- congr

-- end AlgebraicComputation

-- end MatDecompFormal.Components
