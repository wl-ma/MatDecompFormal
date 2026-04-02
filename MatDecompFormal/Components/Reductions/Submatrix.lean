import Mathlib.LinearAlgebra.Matrix.Block
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Framework.Fin
import MatDecompFormal.Framework.FinEnum

namespace MatDecompFormal.Components.Reductions

open Matrix MatDecompFormal.Framework

/-!
# 基于子矩阵的规约方法

`SubmatrixMethod` packages the standard lower-right submatrix reduction on
`Fin (n + 1) × Fin (m + 1)` matrices. The recursive slice is obtained by
dropping the first row and column, and reconstruction restores the original
boundary blocks around the recursive solution.
-/

/--
`SubmatrixMethod` 是一个 `ReductionMethod` 的实例，它实现了直接处理右下角
子矩阵的规约策略。它被定义在 `Fin (n+1)` 和 `Fin (m+1)` 类型的矩阵上。

*   `IsSliceable_def`: 一个由用户提供的谓词，用于定义何时可以进行切片。
-/
noncomputable def SubmatrixMethod (n m : ℕ) (R : Type*) [CommRing R]
    (IsSliceable_def : Matrix (Fin (n + 1)) (Fin (m + 1)) R → Prop) :
    Abstractions.ReductionMethod (n + 1) (m + 1) n m R where
  IsSliceable := IsSliceable_def

  slice := fun A _hA ↦ A.submatrix Fin.succ Fin.succ

  reconstruct := fun A _hA slice_sol ↦
    -- 引入计算性等价关系
    let e_ι := finSuccEquivSum n
    let e_κ := finSuccEquivSum m
    -- 将原始矩阵转换到分块世界，以提取边角料
    let A' := reindex e_ι e_κ A
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    -- 使用 fromBlocks 将边角料和子问题的解重新组装
    let blocks := fromBlocks A₁₁ A₁₂ A₂₁ slice_sol
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
    have h_slice_eq_A₂₂ : A.submatrix Fin.succ Fin.succ = A'.toBlocks₂₂ := by
      rw [submatrix_succ_eq_toBlocks₂₂ A, ← submatrix_succ_eq_toBlocks₂₂ A]
    rw [h_slice_eq_A₂₂]
    -- 证明重构后的分块矩阵等于原始的分块矩阵
    have h_reconstructed_eq_A' :
        fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁ A'.toBlocks₂₂ = A' :=
      fromBlocks_toBlocks A'
    rw [h_reconstructed_eq_A']
    -- 证明 reindex 再 reindex.symm 会得到原始矩阵
    simp [A', e_ι, e_κ]


end MatDecompFormal.Components.Reductions
