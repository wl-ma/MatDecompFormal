import Mathlib.LinearAlgebra.Matrix.Block
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Framework.Fin
import MatDecompFormal.Framework.FinEnum

namespace MatDecompFormal.Components.Reductions

open Matrix MatDecompFormal.Framework

/-!
# 零列规约方法

`ZeroColumnMethod` handles the degenerate case where the first column already
vanishes. The recursive problem is the lower-right submatrix, and reconstruction
reinstates the zero leading column together with the original top row.
-/

/--
`ZeroColumnMethod` 是一个 `ReductionMethod` 的实例，它实现了在第一列为零时，
同时移除第一行和第一列的规约策略。
-/
noncomputable def ZeroColumnMethod (n m : ℕ) (R : Type*) [CommRing R] :
    Abstractions.ReductionMethod (n + 1) (m + 1) n m R where
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
