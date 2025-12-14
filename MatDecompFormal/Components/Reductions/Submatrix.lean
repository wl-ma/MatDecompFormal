import Mathlib.LinearAlgebra.Matrix.Block
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Framework.FinEnum -- 导入新的 Fin 工具

namespace MatDecompFormal.Components.Reductions

open Matrix MatDecompFormal.Framework

/-!
# 基于子矩阵的规约方法 (Submatrix-based Reduction Method) - v2.2 (最终版)

本文件提供了 `SubmatrixMethod`，这是一个在 `Fin n` 世界中实现的
`ReductionMethod` 实例。它封装了直接处理右下角子矩阵的规约策略。

### 设计 (v2.2)
- **限定于 `Fin (n+1)`**: 为了与 `SchurMethod` 等保持一致，并简化归纳，
  本方法被明确限定于处理 `Matrix (Fin (n+1)) (Fin (m+1)) R` 类型的矩阵。
- **使用计算性等价**: 利用 `Framework/FinEnum.lean` 中新定义的、对 `simp`
  友好的 `finSuccEquivSum` 来进行分块，使得证明更加自动化。
- **通用 `IsSliceable`**: `IsSliceable` 条件由用户在实例化时提供，这使得
  `SubmatrixMethod` 可以被多种分解算法（如 QR, Hessenberg）复用。

### 工作原理
1.  **可切片条件 (`IsSliceable`)**: 由用户定义，通常是检查矩阵是否处于一种
    “准标准型”，例如第一列的特定元素为零。
2.  **切片 (`slice`)**: 直接通过 `Matrix.submatrix Fin.succ Fin.succ` 提取
    右下角的子矩阵。
3.  **重构 (`reconstruct`)**: 从原始矩阵的边角料（左上角、右上角、左下角分块）
    和一个**已解决的**子问题 (`slice_sol`) 重新组装出完整的矩阵。
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








-- import Mathlib.Data.FinEnum
-- import Mathlib.LinearAlgebra.Matrix.Block
-- import MatDecompFormal.Abstractions.ReductionMethod

-- namespace MatDecompFormal.Components.Reductions

-- open Matrix FinEnum

-- /-!
-- # 基于子矩阵的规约方法 (Submatrix-based Reduction Method)

-- 本文件提供了 `SubmatrixMethod`，这是 `ReductionMethod` 的一个具体实例。
-- 它封装了直接处理右下角子矩阵的规约策略。这种方法适用于那些在变换步骤
-- （例如，通过 Householder 变换）后，矩阵的左上角部分已经形成了一个可以与
-- 右下角解耦的块状结构（例如，块下三角矩阵）的分解算法。

-- ### 工作原理
-- 1.  **可切片条件 (`IsSliceable`)**: 检查矩阵是否处于一种“准标准型”，
--     通常是第一列（或第一行）的特定元素为零。这个条件确保了矩阵可以被
--     安全地分解为块，而不会在重构时产生交叉项。
-- 2.  **切片 (`slice`)**: 提取右下角的子矩阵。这定义了归纳的子问题。
-- 3.  **重构 (`reconstruct`)**: 提供一个代数装置，能从原始矩阵的边角料
--     （左上角、右上角、左下角分块）和一个**已解决的**子问题 (`slice_sol`)
--     重新组装出完整的矩阵。由于 `IsSliceable` 条件的保证，这个重构过程
--     通常比舒尔补的重构要简单得多。

-- 这个组件是 `QR` 分解、`Hessenberg` 分解等算法的核心代数引擎。
-- -/

-- section SubmatrixMethod

-- -- 声明所有定义共享的类型和类型类实例。
-- variable (ι κ R : Type*) [FinEnum ι] [FinEnum κ] [CommRing R]

-- /--
-- `SubmatrixMethod` 是一个 `ReductionMethod` 的实例，它实现了直接处理右下角
-- 子矩阵的规约策略。

-- 为了方便，我们同样固定 `i₀` 和 `j₀` 为通过 `FinEnum.equiv` 映射到的 `Fin 0`，
-- 这要求 `ι` 和 `κ` 必须是非空类型。
-- -/
-- noncomputable def SubmatrixMethod
--     (IsSliceable_def : Matrix ι κ R → Prop)
--     (hι : FinEnum.card ι > 0) (hκ : FinEnum.card κ > 0) :
--     Abstractions.ReductionMethod ι κ R :=
--   -- 使用 let 语句来帮助类型检查器，明确地获取类型类实例和相关定义。
--   let finEnum_ι : FinEnum ι := inferInstance
--   let finEnum_κ : FinEnum κ := inferInstance
--   let equiv_ι : ι ≃ Fin (FinEnum.card ι) := finEnum_ι.equiv
--   let equiv_κ : κ ≃ Fin (FinEnum.card κ) := finEnum_κ.equiv
--   -- i₀ 和 j₀ 是我们选定的主元索引，即 ι 和 κ 中的“第一个”元素。
--   let i₀ := (equiv_ι).symm ⟨0, hι⟩
--   let j₀ := (equiv_κ).symm ⟨0, hκ⟩
--   -- 1. 定义行和列的划分谓词，用于将索引类型分为“主元索引”和“其他索引”。
--   let p_ι : ι → Prop := fun i ↦ i = i₀
--   let p_κ : κ → Prop := fun j ↦ j = j₀
--   -- 2. 构造索引类型的等价关系。
--   let e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}) := (Equiv.sumCompl p_ι).symm
--   let e_κ : κ ≃ ({j // p_κ j} ⊕ {j // ¬p_κ j}) := (Equiv.sumCompl p_κ).symm
--   {
--     -- `Sliceι` 和 `Sliceκ` 定义了子问题的索引类型，即排除了主元索引后的剩余部分。
--     Sliceι := {i : ι // i ≠ i₀},
--     Sliceκ := {j : κ // j ≠ j₀},
--     finEnum_slice_ι := inferInstance,
--     finEnum_slice_κ := inferInstance,

--     -- 可切片条件由用户传入，因为它依赖于具体的分解算法。
--     -- 例如，对于QR分解，它会是 `∀ i ≠ i₀, A i j₀ = 0`。
--     IsSliceable := IsSliceable_def,

--     -- 切片操作：提取右下角的子矩阵。
--     slice := fun A _hA ↦ A.submatrix (fun i ↦ i.val) (fun j ↦ j.val),

--     -- 重构操作：从分块和子问题的解 `slice_sol` 重建完整矩阵。
--     reconstruct := fun A _hA slice_sol ↦
--       -- 3. 使用 `reindex` 将原始矩阵 A 的索引类型转换为分块形式。
--       let A_reindexed := reindex e_ι e_κ A
--       --    从这个 reindex 后的矩阵中提取出除右下角外的三个分块。
--       let A₁₁ := A_reindexed.toBlocks₁₁
--       let A₁₂ := A_reindexed.toBlocks₁₂
--       let A₂₁ := A_reindexed.toBlocks₂₁
--       -- 4. 使用 `fromBlocks` 将分块重新组装。注意，右下角使用的是 `slice_sol`。
--       let new_block_matrix := fromBlocks A₁₁ A₁₂ A₂₁ slice_sol
--       -- 5. 使用 `reindex` 和等价关系的逆，将组装好的分块矩阵安全地转换回原始矩阵类型。
--       new_block_matrix.reindex e_ι.symm e_κ.symm,

--     -- 健全性检查：证明 `reconstruct` 和 `slice` 是配对的。
--     -- 这个证明与 `SchurMethod` 中的证明完全相同，因为它只依赖于分块矩阵的代数。
--     reconstruct_slice_eq := by
--       intro A hA
--       dsimp only
--       have h_slice_eq_block₂₂ : A.submatrix (fun i ↦ @Subtype.val ι (fun i ↦ i ≠ i₀) i)
--           (fun j ↦ @Subtype.val κ (fun j ↦ j ≠ j₀) j) = (reindex e_ι e_κ A).toBlocks₂₂ := by
--         rfl
--       rw [h_slice_eq_block₂₂]
--       let A_reindexed := reindex e_ι e_κ A
--       simp only [e_ι, e_κ, p_ι, p_κ]
--       rw [fromBlocks_toBlocks A_reindexed]
--       simp [A_reindexed, e_ι, e_κ, p_ι, p_κ]
--   }

-- end SubmatrixMethod

-- end MatDecompFormal.Components.Reductions
























-- import Mathlib

-- section aux
-- --补充些 Mathlib的api
-- @[inline] def Fin.natSub {n} (m) (i : Fin (n + m)) (h : n ≤ i) : Fin m :=
--   ⟨i - n,  Nat.sub_lt_left_of_lt_add h i.2⟩

-- lemma finSumFinEquiv_symm_apply_right {i : Fin (n + o)} (hi : n ≤ i) :
--   (finSumFinEquiv.symm i) = Sum.inr (Fin.natSub o i hi) := by
--     simp [finSumFinEquiv, Fin.natSub, Fin.addCases, Nat.not_lt.mpr hi, Fin.subNat]

-- lemma finSumFinEquiv_symm_apply_left
--    {i : Fin (n + o)} (hi : i < n) : finSumFinEquiv.symm i = Sum.inl ⟨i, hi⟩ := by
--   simp [finSumFinEquiv, Fin.addCases, hi, Fin.castLT]

-- lemma find_pivot_col {α n} [NeZero n] [Zero α] {M : Fin n → α} (h : M ≠ 0) :
--   ∃ i : Fin n, M i ≠ 0 := by
--   by_contra! ha
--   apply h
--   funext i
--   apply ha

-- lemma WithTop.map_lt_of_lt {α β : Type*} {x y : WithTop α} [LT α] [LT β] (h : α → β)
--     (hh : ∀ x y, x < y → h x < h y) (hxy : x < y) :
--     WithTop.map h x < WithTop.map h y := by
--   rw [lt_def] at *
--   have ⟨a, ⟨ha, hb⟩⟩ := hxy
--   use h a
--   simp only [ha, map_coe, true_and]
--   intro b hbm
--   rw [map_eq_some_iff] at hbm
--   have ⟨b', ⟨hby, hb'⟩⟩ := hbm
--   rw [← hb']
--   apply hh _ _ (hb _ hby)

-- lemma WithTop.equiv_lt {α β : Type*} {x y : WithTop α}
--   [PartialOrder α] [PartialOrder β] (h : α ≃o β) (hxy : x < y) :
--   WithTop.map h x < WithTop.map h y := by
--   simpa only [← OrderIso.withTopCongr_apply, OrderIso.lt_iff_lt]

-- /--
-- Given invertible matrices `x ∈ GL l R` and `y ∈ GL o R`, constructs their direct sum
-- as an invertible block-diagonal matrix in `GL (l ⊕ o) R`.

-- This is the group homomorphism sending `(x, y)` to `[x 0; 0 y]`.
-- -/
-- noncomputable def Matrix.GeneralLinearGroup.glDirectSum {R} {l o} [CommRing R]
--     [Fintype l] [DecidableEq l] [Fintype o] [DecidableEq o]
--     (x : GL l R) (y : GL o R) : GL (l ⊕ o) R where
--   val:= fromBlocks x.1 0 0 y.1
--   inv:= fromBlocks x.2 0 0 y.2
--   val_inv:= by simp [fromBlocks_multiply]
--   inv_val:= by simp [fromBlocks_multiply]

-- lemma matrix_mul_distrib_submatrix_fromBlocks_zero_top [AddCommMonoid F] [Mul F] [Fintype r]
--   [Fintype l] [Fintype o]
--   (P : Matrix l l F) (a : Matrix l r F) (b : Matrix l o F)
--   (f : s → r ⊕ o) :
--   P * ((fromBlocks 0 0 a b : Matrix ((Fin 0) ⊕ l) (r ⊕ o) F).submatrix Sum.inr f)  =
--   (fromBlocks 0 0 (P * a) (P * b) : Matrix ((Fin 0) ⊕ l) (r ⊕ o) F ).submatrix Sum.inr f := by
--   funext i j
--   simp only [submatrix_apply]
--   match hf : f j with
--   | Sum.inl k => simp [HMul.hMul, hf];
--   | Sum.inr k => simp [HMul.hMul, hf];

-- end aux
