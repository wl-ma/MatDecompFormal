import Mathlib.LinearAlgebra.Matrix.Block
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Framework.FinEnum -- 导入新的 Fin 工具

namespace MatDecompFormal.Components.Reductions

open Matrix MatDecompFormal.Framework

/-!
# 零列规约方法 (Zero-Column Reduction Method) - v2.3 (逻辑修正最终版)

本文件提供了 `ZeroColumnMethod`，这是一个在 `Fin n` 世界中实现的
`ReductionMethod` 实例，专门用于处理矩阵第一列全为零的特殊情况。

### 设计 (v2.3)
- **逻辑修正**: 当第一列全为零时，第一行（除了 A 0 0 = 0）也失去了
  作为主元行的意义。因此，最有效的规约是**同时移除第一行和第一列**，
  将问题规约到右下角的 `(n × m)` 子矩阵。
- **限定**: 本方法被限定于处理 `Fin (n+1) × Fin (m+1)` 类型的矩阵。
- **使用计算性等价**: 利用 `finSuccEquivSum` 来进行分块。

### 工作原理
1.  **可切片条件 (`IsSliceable`)**: 检查矩阵的第一列 `0` 是否所有元素都为零。
2.  **切片 (`slice`)**: 直接通过 `Matrix.submatrix Fin.succ Fin.succ` 提取
    右下角的 `(n × m)` 子矩阵。
3.  **重构 (`reconstruct`)**: 将一个 `(n+1) × 1` 的零列向量、一个 `1 × m` 的
    零行向量，以及子问题的解 `slice_sol` 组装成一个左侧和上侧为零的
    分块矩阵。
-/

/--
`ZeroColumnMethod` 是一个 `ReductionMethod` 的实例，它实现了在第一列为零时，
同时移除第一行和第一列的规约策略。
-/
noncomputable def ZeroColumnMethod (n m : ℕ) (R : Type*) [CommRing R] :
    Abstractions.ReductionMethod (n + 1) (m + 1) R where
  slice_m := n
  slice_n := m
  IsSliceable := fun A ↦ ∀ i, A i 0 = 0

  slice := fun A _hA ↦ A.submatrix Fin.succ Fin.succ

  reconstruct := fun A hA slice_sol ↦
    -- 引入计算性等价关系
    let e_ι := finSuccEquivSum n
    let e_κ := finSuccEquivSum m
    -- 从原始矩阵中提取右上角块 A₁₂
    let A₁₂ := (reindex e_ι e_κ A).toBlocks₁₂
    -- 构造零块
    let zero_block₁₁ : Matrix (Fin 1) (Fin 1) R := 0
    let zero_block₂₁ : Matrix (Fin n) (Fin 1) R := 0
    -- 使用 fromBlocks 将零块和子问题的解重新组装
    let blocks := fromBlocks zero_block₁₁ A₁₂ zero_block₂₁ slice_sol
    -- reindex 回原始类型
    blocks.reindex e_ι.symm e_κ.symm

  reconstruct_slice_eq := by
    intro A hA
    -- 展开 reconstruct 和 slice 的定义
    dsimp only
    -- 引入计算性等价关系
    let e_ι := finSuccEquivSum n
    let e_κ := finSuccEquivSum m
    let A' := reindex e_ι e_κ A
    -- 关键步骤：使用 submatrix_succ_eq_toBlocks₂₂ 将 slice 与 toBlocks₂₂ 联系起来
    change (reindex (finSuccEquivSum n).symm (finSuccEquivSum m).symm)
      (fromBlocks 0 A'.toBlocks₁₂ 0 (A.submatrix Fin.succ Fin.succ)) = A
    have h_slice_eq_A₂₂ : A.submatrix Fin.succ Fin.succ = A'.toBlocks₂₂ := by
      rw [submatrix_succ_eq_toBlocks₂₂ A, ← submatrix_succ_eq_toBlocks₂₂ A]
    rw [h_slice_eq_A₂₂]
    -- 证明 A' 的左侧分块 A₁₁ 和 A₂₁ 都是零
    have h_zero_blocks : A'.toBlocks₁₁ = 0 ∧ A'.toBlocks₂₁ = 0 := by
      constructor
      · ext i j; simp [A', finSuccEquivSum, toBlocks₁₁, e_ι, e_κ, hA]
      · ext i j; simp [A', finSuccEquivSum, toBlocks₂₁, e_ι, e_κ, hA]
    -- 将零块代入
    rw [← h_zero_blocks.1, ← h_zero_blocks.2]
    -- 证明重构后的分块矩阵等于原始的分块矩阵
    have h_reconstructed_eq_A' :
        fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁ A'.toBlocks₂₂ = A' :=
      fromBlocks_toBlocks A'
    rw [h_reconstructed_eq_A']
    -- 证明 reindex 再 reindex.symm 会得到原始矩阵
    simp [A', e_ι, e_κ]

end MatDecompFormal.Components.Reductions







-- import Mathlib.Data.FinEnum
-- import Mathlib.LinearAlgebra.Matrix.Block
-- import MatDecompFormal.Abstractions.ReductionMethod

-- namespace MatDecompFormal.Components.Reductions

-- open Matrix FinEnum MatDecompFormal.Abstractions

-- /-!
-- # 零列规约方法 (Zero-Column Reduction Method)

-- 本文件提供了 `ZeroColumnMethod`，这是一个 `ReductionMethod` 的具体实例。
-- 它专门用于处理一个非常特殊的场景：当矩阵的第一列全为零时。

-- ### 工作原理
-- 在这种特殊情况下，矩阵的结构非常简单，可以被看作一个左侧为零的块矩阵。
-- `[0, A₁₂; 0, A₂₂]`

-- 1.  **可切片条件 (`IsSliceable`)**: 检查矩阵的第一列 `j₀` 是否所有元素都为零。
-- 2.  **切片 (`slice`)**: 直接提取右下角的子矩阵 `A₂₂`。
-- 3.  **重构 (`reconstruct`)**: 从原始矩阵的右上角分块 `A₁₂` 和一个已解决的
--     子问题 (`slice_sol`) 重新组装出完整的矩阵。由于第一列为零，重构过程
--     非常直接，不需要像舒尔补那样进行复杂的代数运算。

-- 这个组件是 `PLU` 分解在处理不可逆矩阵时，遇到奇异主元列的回退 (fallback)
-- 策略。
-- -/

-- section ZeroColumnMethod

-- -- 声明所有定义共享的类型和类型类实例。
-- variable (ι κ R : Type*) [FinEnum ι] [FinEnum κ] [CommRing R] [DecidableEq R]

-- /--
-- `ZeroColumnMethod` 是一个 `ReductionMethod` 的实例，它实现了在第一列为零时，
-- 直接处理右下角子矩阵的规约策略。

-- 为了方便，我们固定 `j₀` 为通过 `FinEnum.equiv` 映射到的 `Fin 0`，
-- 这要求 `κ` 必须是非空类型。
-- -/
-- noncomputable def ZeroColumnMethod (hι : card ι > 0) (hκ : card κ > 0) :
--     ReductionMethod ι κ R :=
--   let i₀ := (@equiv ι).symm ⟨0, hι⟩
--   let j₀ := (@equiv κ).symm ⟨0, hκ⟩
--   -- 1. 定义划分谓词。
--   let p_ι : ι → Prop := fun i ↦ i = i₀
--   let p_κ : κ → Prop := fun j ↦ j = j₀
--   -- 2. 构造索引类型的等价关系。
--   let e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}) := (Equiv.sumCompl p_ι).symm
--   let e_κ : κ ≃ ({j // p_κ j} ⊕ {j // ¬p_κ j}) := (Equiv.sumCompl p_κ).symm
--   {
--     -- `Sliceι` 是完整的行索引类型，因为我们没有移除任何行。
--     Sliceι := {i : ι // i ≠ i₀},
--     -- `Sliceκ` 是排除了第一列 `j₀` 后的剩余列索引。
--     Sliceκ := {j : κ // j ≠ j₀},
--     finEnum_slice_ι := inferInstance,
--     finEnum_slice_κ := inferInstance,

--     -- 可切片条件：第一列 `j₀` 的所有元素都为零。
--     IsSliceable := fun A ↦ ∀ i, A i j₀ = 0,

--     -- 切片操作：提取右下角子矩阵 A₂₂
--     slice := fun A _hA ↦ A.submatrix (fun i ↦ i.val) (fun j ↦ j.val),

--     -- 重构操作：重组一个块下三角矩阵
--     reconstruct := fun A _hA slice_sol ↦
--       let A_reindexed := reindex e_ι e_κ A
--       let A₁₂ := A_reindexed.toBlocks₁₂
--       -- 关键：左上角和左下角都是零
--       let A₁₁_zero : Matrix {i // i = i₀} {j // j = j₀} R := 0
--       let A₂₁_zero : Matrix {i // i ≠ i₀} {j // j = j₀} R := 0
--       let new_block_matrix := fromBlocks A₁₁_zero A₁₂ A₂₁_zero slice_sol
--       new_block_matrix.reindex e_ι.symm e_κ.symm,

--     -- 健全性检查：证明 `reconstruct` 和 `slice` 是配对的。
--     reconstruct_slice_eq := by
--       intro A hA
--       dsimp only
--       ext i j
--       -- 对行索引 `i` 进行分情况讨论：`i` 是不是第一行 `i₀`。
--       by_cases hi : i = i₀
--       · subst hi
--         have h_i_inl : e_ι i₀ = Sum.inl ⟨i₀, rfl⟩ := by
--             simp [e_ι, Equiv.sumCompl, p_ι]
--         -- 对列索引 `j` 进行分情况讨论：`j` 是不是第一列 `j₀`。
--         by_cases hj : j = j₀
--         · subst hj -- 将 `j` 替换为 `j₀`
--           simp [reindex_apply]
--           have h_j_inl : e_κ j₀ = Sum.inl ⟨j₀, rfl⟩ := by
--             simp [e_κ, Equiv.sumCompl, p_κ]
--           rw [h_i_inl, h_j_inl]
--           rw [fromBlocks_apply₁₁]
--           simp
--           exact (hA i₀).symm
--         · simp [reindex_apply]
--           have h_j_inr : e_κ j = Sum.inr ⟨j, hj⟩ := by
--             simp [e_κ, Equiv.sumCompl, p_κ, hj]
--           rw [h_i_inl, h_j_inr]
--           rw [fromBlocks_apply₁₂]
--           rfl
--       · have h_i_inr : e_ι i = Sum.inr ⟨i, hi⟩ := by
--             simp [e_ι, Equiv.sumCompl, p_ι, hi]
--         -- 对列索引 `j` 进行分情况讨论：`j` 是不是第一列 `j₀`。
--         by_cases hj : j = j₀
--         · subst hj -- 将 `j` 替换为 `j₀`
--           simp [reindex_apply]
--           have h_j_inl : e_κ j₀ = Sum.inl ⟨j₀, rfl⟩ := by
--             simp [e_κ, Equiv.sumCompl, p_κ]
--           rw [h_i_inr, h_j_inl]
--           rw [fromBlocks_apply₂₁]
--           simp
--           exact (hA i).symm
--         · simp [reindex_apply]
--           have h_j_inr : e_κ j = Sum.inr ⟨j, hj⟩ := by
--             simp [e_κ, Equiv.sumCompl, p_κ, hj]
--           rw [h_i_inr, h_j_inr]
--           rw [fromBlocks_apply₂₂]
--           rfl
--   }

-- end ZeroColumnMethod

-- end MatDecompFormal.Components.Reductions
