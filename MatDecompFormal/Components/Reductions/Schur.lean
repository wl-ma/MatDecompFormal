import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Framework.Fin
import MatDecompFormal.Framework.FinEnum

namespace MatDecompFormal.Components.Reductions

open Matrix MatDecompFormal.Framework

/-!
# 基于舒尔补的规约方法

`SchurMethod` implements the square-matrix reduction that cuts off the leading
row and column by taking the Schur complement of the top-left scalar block.
Reconstruction restores the original matrix by adding back the correction term.
-/

/--
`SchurMethod` 是一个 `ReductionMethod` 的实例，它为**方阵**实现了基于舒尔补的规约策略。
它被定义在 `Fin (n+1)` 类型的方阵上。
-/
noncomputable def SchurMethod (n : ℕ) (R : Type*) [Field R] :
    Abstractions.ReductionMethod (n + 1) (n + 1) n n R where
  IsSliceable := fun A ↦ IsUnit (A 0 0)

  slice := fun A hA ↦
    -- 利用新的计算性等价关系进行 reindex
    let A' := reindex (finSuccEquivSum n) (finSuccEquivSum n) A
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    let A₂₂ := A'.toBlocks₂₂
    -- A 0 0 的逆就是标量 (A 0 0)⁻¹
    let inv_A₀₀ : R := (IsUnit.unit hA).inv
    -- 手动计算舒尔补
    A₂₂ - A₂₁ * (!![inv_A₀₀]) * A₁₂

  reconstruct := fun A hA slice_sol ↦
    -- 同样使用计算性等价关系
    let e := finSuccEquivSum n
    let A' := reindex e e A
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    let inv_A₀₀ : R := (IsUnit.unit hA).inv
    -- 从子问题的解重构 A₂₂ 块
    let A₂₂_reconstructed := slice_sol + A₂₁ * (!![inv_A₀₀]) * A₁₂
    -- 使用 fromBlocks 重新组装
    let blocks := fromBlocks A₁₁ A₁₂ A₂₁ A₂₂_reconstructed
    -- reindex 回原始类型
    blocks.reindex e.symm e.symm

  reconstruct_slice_eq := by
    intro A hA
    -- 展开 reconstruct 和 slice 的定义
    dsimp only
    -- 引入计算性等价关系
    let e := finSuccEquivSum n
    let A' := reindex e e A
    -- 提取分块
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    let A₂₂ := A'.toBlocks₂₂
    -- 构造重构后的矩阵
    let reconstructed_blocks :=
      fromBlocks A₁₁ A₁₂ A₂₁ (A₂₂ - A₂₁ * (!![(IsUnit.unit hA).inv]) * A₁₂ +
          A₂₁ * (!![(IsUnit.unit hA).inv]) * A₁₂)
    -- 证明重构后的分块矩阵等于原始的分块矩阵
    have h_reconstructed_eq_A' : reconstructed_blocks = A' := by
      simp [reconstructed_blocks, sub_add_cancel]
      rw [fromBlocks_toBlocks]
    -- 将等式应用到 reindex 后的结果上
    change (reindex (finSuccEquivSum n).symm (finSuccEquivSum n).symm) reconstructed_blocks = A
    rw [h_reconstructed_eq_A']
    -- 证明 reindex 再 reindex.symm 会得到原始矩阵
    simp [A', e]


end MatDecompFormal.Components.Reductions
