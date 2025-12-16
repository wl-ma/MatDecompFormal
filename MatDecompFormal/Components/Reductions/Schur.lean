import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Framework.Fin
import MatDecompFormal.Framework.FinEnum -- 导入新的 Fin 工具

namespace MatDecompFormal.Components.Reductions

open Matrix MatDecompFormal.Framework

/-!
# 基于舒尔补的规约方法 (Schur-Complement-based Reduction Method) - v2.4 (最终版)

本文件提供了 `SchurMethod`，这是一个 `ReductionMethod` 的具体实例，
它在具体的 `Fin n` 世界中为**方阵**实现了通过舒尔补进行规约的策略。

### 设计 (v2.4)
- **限定为方阵**: 为了确保 `A⁻¹` 和 `fromBlocks` 的类型正确性，本方法
  被明确限定于处理 `Matrix (Fin (n+1)) (Fin (n+1)) R` 类型的方阵。
- **使用计算性等价**: 利用 `Framework/FinEnum.lean` 中新定义的、对 `simp`
  友好的 `finSuccEquivSum` 来进行分块，使得证明更加自动化。
- **手动构造**: 由于 `Mathlib` 没有为通用域上的矩阵提供 `schurComplement`
  的直接定义，本文件从 `submatrix` 和分块矩阵乘法的基础上手动构造了该操作。

### 工作原理
1.  **可切片条件 (`IsSliceable`)**: 检查左上角 `A 0 0` 元素是否为域中的单位（即非零）。
2.  **切片 (`slice`)**: 手动计算舒尔补 `S = A₂₂ - A₂₁ * A₁₁⁻¹ * A₁₂`。
    其中 `A₁₁` 是 `1x1` 的左上角块，其逆 `A₁₁⁻¹` 通过 `Matrix.inv_singleton` 计算。
3.  **重构 (`reconstruct`)**: 从子问题的解 `slice_sol` 和原始矩阵的
    分块中重构出完整的矩阵。
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












-- import Mathlib.Data.FinEnum
-- import Mathlib.LinearAlgebra.Matrix.Block
-- import Mathlib.LinearAlgebra.Matrix.NonsingularInverse -- for IsUnit and inv

-- import MatDecompFormal.Abstractions.ReductionMethod

-- namespace MatDecompFormal.Components.Reductions

-- open Matrix FinEnum

-- /-!
-- # 基于舒尔补的规约方法 (Schur-Complement-based Reduction Method) - v2.2 (最终修正版)

-- 本文件提供了 `SchurMethod`，这是一个 `ReductionMethod` 的具体实例。
-- 它封装了通过分离出左上角主元并处理其舒尔补的规约策略。
-- 这个版本通过引入明确的类型等价关系 (Equiv)，解决了在泛型索引类型上
-- 进行 `1x1` 矩阵求逆时遇到的类型不匹配和实例缺失问题。

-- ### 工作原理 (v2.2)
-- 1.  **可切片条件 (`IsSliceable`)**: 检查 `A i₀ j₀` 是否可逆。
-- 2.  **切片 (`slice`)**:
--     a. 构造 `1x1` 分块索引 `{i // p_ι i}` 与 `Fin 1` 之间的等价关系 `e_ι₁`。
--     b. 使用 `reindex` 将 `A₁₁` 块安全地转换为 `Matrix (Fin 1) (Fin 1) R` 类型。
--     c. 在 `Fin 1` 空间中证明其可逆性并计算逆。
--     d. 计算舒尔补 `S = A₂₂ - A₂₁ * (A₁₁ 的逆) * A₁₂`。
-- 3.  **重构 (`reconstruct`)**: 同样，在 `Fin 1` 空间中计算逆，然后用它来重构 `A₂₂` 块。

-- 这个版本是健壮且类型安全的，能够正确地为 `PLU` 等分解提供代数支持。
-- -/

-- section SchurHelpers

-- variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Field R]

-- /--
-- 一个 `1x1` 矩阵是可逆的，当且仅当其唯一的元素是可逆的。
-- -/
-- lemma isUnit_singleton_iff {a : R} : IsUnit (!![a] : Matrix (Fin 1) (Fin 1) R) ↔ IsUnit a := by
--   rw [isUnit_iff_isUnit_det]
--   simp

-- end SchurHelpers


-- section SchurMethod

-- variable (ι κ R : Type*) [FinEnum ι] [FinEnum κ] [Field R] [DecidableEq R]
-- #check FinEnum.Subtype.finEnum
-- /--
-- `SchurMethod` 是一个 `ReductionMethod` 的实例，它实现了基于舒尔补的规约策略。
-- -/
-- noncomputable def SchurMethod (hι : FinEnum.card ι > 0) (hκ : FinEnum.card κ > 0) :
--     Abstractions.ReductionMethod ι κ R :=
--   let i₀ := (@equiv ι).symm ⟨0, hι⟩
--   let j₀ := (@equiv κ).symm ⟨0, hκ⟩
--   let p_ι : ι → Prop := fun i ↦ i = i₀
--   let p_κ : κ → Prop := fun j ↦ j = j₀
--   let e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}) := (Equiv.sumCompl p_ι).symm
--   let e_κ : κ ≃ ({j // p_κ j} ⊕ {j // ¬p_κ j}) := (Equiv.sumCompl p_κ).symm

--   -- **核心修正**: 手动为单例类型 {x // p x} 构造 FinEnum 实例。
--   let finEnum_p_ι : FinEnum {i // p_ι i} := {
--     card := 1,
--     equiv := {
--       toFun := fun _ ↦ 0,
--       invFun := fun _ ↦ ⟨i₀, rfl⟩,
--       left_inv := by intro ⟨i, hi⟩; simp [p_ι] at hi; simp [hi],
--       right_inv := by intro ⟨i, hi⟩; simp [Fin.fin_one_eq_zero]
--     },
--     decEq := by infer_instance
--   }
--   let finEnum_p_κ : FinEnum {j // p_κ j} := {
--     card := 1,
--     equiv := {
--       toFun := fun _ ↦ 0,
--       invFun := fun _ ↦ ⟨j₀, rfl⟩,
--       left_inv := by intro ⟨j, hj⟩; simp [p_κ] at hj; simp [hj],
--       right_inv := by intro ⟨j, hj⟩; simp [Fin.fin_one_eq_zero]
--     },
--     decEq := by infer_instance
--   }

--   let e_ι₁ : {i // p_ι i} ≃ Fin 1 := finEnum_p_ι.equiv
--   let e_κ₁ : {j // p_κ j} ≃ Fin 1 := finEnum_p_κ.equiv
--   {
--     Sliceι := {i : ι // ¬p_ι i},
--     Sliceκ := {j : κ // ¬p_κ j},
--     finEnum_slice_ι := inferInstance,
--     finEnum_slice_κ := inferInstance,

--     IsSliceable := fun A ↦ IsUnit (A i₀ j₀),

--     slice := fun A hA ↦
--       let A_reindexed := reindex e_ι e_κ A
--       let A₁₁ := A_reindexed.toBlocks₁₁
--       let A₁₂ := A_reindexed.toBlocks₁₂
--       let A₂₁ := A_reindexed.toBlocks₂₁
--       let A₂₂ := A_reindexed.toBlocks₂₂
--       -- **修正点**: 在 Fin 1 空间中进行求逆操作。
--       let A₁₁_fin1 := reindex e_ι₁ e_κ₁ A₁₁
--       have h_A₁₁_fin1_eq : A₁₁_fin1 = !![A i₀ j₀] := by
--         ext i j; simp [A₁₁_fin1]; rfl
--       have h_unit_A₁₁_fin1 : IsUnit A₁₁_fin1 := by
--         rw [h_A₁₁_fin1_eq]; exact isUnit_singleton_iff.mpr hA
--       let inv_A₁₁_fin1 := (IsUnit.unit h_unit_A₁₁_fin1).inv
--       -- 将计算出的逆 reindex 回原始的 1x1 块索引类型。
--       let inv_A₁₁ := (reindex e_ι₁.symm e_κ₁.symm inv_A₁₁_fin1)ᵀ
--       A₂₂ - A₂₁ * inv_A₁₁ * A₁₂,

--     reconstruct := fun A hA slice_sol ↦
--       let A_reindexed := reindex e_ι e_κ A
--       let A₁₁ := A_reindexed.toBlocks₁₁
--       let A₁₂ := A_reindexed.toBlocks₁₂
--       let A₂₁ := A_reindexed.toBlocks₂₁
--       -- **修正点**: 同样，在 Fin 1 空间中计算逆。
--       let A₁₁_fin1 := reindex e_ι₁ e_κ₁ A₁₁
--       have h_A₁₁_fin1_eq : A₁₁_fin1 = !![A i₀ j₀] := by
--         ext i j; simp [A₁₁_fin1]; rfl
--       have h_unit_A₁₁_fin1 : IsUnit A₁₁_fin1 := by
--         rw [h_A₁₁_fin1_eq]; exact isUnit_singleton_iff.mpr hA
--       let inv_A₁₁_fin1 := (IsUnit.unit h_unit_A₁₁_fin1).inv
--       let inv_A₁₁ := (reindex e_ι₁.symm e_κ₁.symm inv_A₁₁_fin1)ᵀ
--       let reconstructed_A₂₂ := slice_sol + A₂₁ * inv_A₁₁ * A₁₂
--       let new_block_matrix := fromBlocks A₁₁ A₁₂ A₂₁ reconstructed_A₂₂
--       new_block_matrix.reindex e_ι.symm e_κ.symm,

--     reconstruct_slice_eq := by
--       intro A hA
--       dsimp only
--       let A_reindexed := reindex e_ι e_κ A
--       let A₁₁ := A_reindexed.toBlocks₁₁
--       let A₁₂ := A_reindexed.toBlocks₁₂
--       let A₂₁ := A_reindexed.toBlocks₂₁
--       let A₂₂ := A_reindexed.toBlocks₂₂
--       -- **修正点**: 在证明中也使用同样的方式处理逆。
--       let A₁₁_fin1 := reindex e_ι₁ e_κ₁ A₁₁
--       have h_A₁₁_fin1_eq : A₁₁_fin1 = !![A i₀ j₀] := by
--         ext i j; simp [A₁₁_fin1]; rfl
--       have h_unit_A₁₁_fin1 : IsUnit A₁₁_fin1 := by
--         rw [h_A₁₁_fin1_eq]; exact isUnit_singleton_iff.mpr hA
--       let inv_A₁₁_fin1 := (IsUnit.unit h_unit_A₁₁_fin1).inv
--       let inv_A₁₁ := (reindex e_ι₁.symm e_κ₁.symm inv_A₁₁_fin1)ᵀ
--       let schur_complement := A₂₂ - A₂₁ * inv_A₁₁ * A₁₂
--       let reconstructed_A₂₂ := schur_complement + A₂₁ * inv_A₁₁ * A₁₂
--       have h_reconstruct_A₂₂ : reconstructed_A₂₂ = A₂₂ := by
--         simp [reconstructed_A₂₂, schur_complement, sub_add_cancel]
--       simp [fromBlocks_toBlocks]
--   }

-- end SchurMethod

-- end MatDecompFormal.Components.Reductions








-- import Mathlib.Data.FinEnum
-- import Mathlib.LinearAlgebra.Matrix.Block
-- import Mathlib.LinearAlgebra.Matrix.NonsingularInverse -- for IsUnit
-- import MatDecompFormal.Abstractions.ReductionMethod

-- namespace MatDecompFormal.Components.Reductions

-- open Matrix FinEnum

-- /-!
-- # 基于舒尔补思想的规约方法 (Schur-Complement-based Reduction Method)

-- 本文件提供了 `SchurMethod`，这是一个 `ReductionMethod` 的具体实例。
-- 它封装了通过分离出左上角主元并处理剩余右下角子矩阵的规约策略。
-- 这种策略的代数核心是舒尔补的概念，常见于高斯消元类的分解算法。

-- ### 工作原理
-- 1.  **可切片条件 (`IsSliceable`)**: 检查矩阵的左上角元素 `A i₀ j₀` 是否可逆。
--     这是进行消元操作（例如，乘以 `A₁₁⁻¹`）的前提。
-- 2.  **切片 (`slice`)**: 提取右下角的子矩阵 `A₂₂`。这定义了归纳的子问题。
--     注意，这**不是**直接计算舒尔补，而只是提取子矩阵。舒尔补的概念
--     体现在 `lift_from_slice` 引理的代数证明中。
-- 3.  **重构 (`reconstruct`)**: 提供一个代数“装置”，能从原始矩阵的边角料
--     （`A₁₁`, `A₁₂`, `A₂₁`）和一个**已解决的**子问题 (`slice_sol`)
--     重新组装出完整的矩阵解。

-- 这个组件是 `PLU` 分解、`Cholesky` 分解等算法的核心代数引擎。
-- -/

-- -- 使用 section 和 variables 来提供共享的上下文，确保类型类实例能被正确推断。
-- section SchurMethod

-- -- 声明所有定义共享的类型和类型类实例。
-- variable (ι κ R : Type*) [FinEnum ι] [FinEnum κ] [CommRing R]

-- /--
-- `SchurMethod` 是一个 `ReductionMethod` 的实例，它实现了基于分离主元和处理
-- 右下角子矩阵的规约策略。其代数正确性由舒尔补理论保证。

-- 为了方便，我们固定 `i₀` 和 `j₀` 为通过 `FinEnum.equiv` 映射到的 `Fin 0`。
-- 这要求 `ι` 和 `κ` 必须是非空类型。
-- -/
-- noncomputable def SchurMethod (hι : FinEnum.card ι > 0) (hκ : FinEnum.card κ > 0) :
--     Abstractions.ReductionMethod ι κ R :=
--   -- i₀ 和 j₀ 是我们选定的主元索引，即 ι 和 κ 中的“第一个”元素。
--   let i₀ := (@equiv ι).symm ⟨0, hι⟩
--   let j₀ := (@equiv κ).symm ⟨0, hκ⟩
--   -- 1. 定义行和列的划分谓词，用于将索引类型分为“主元索引”和“其他索引”。
--   let p_ι : ι → Prop := fun i ↦ i = i₀
--   let p_κ : κ → Prop := fun j ↦ j = j₀
--   -- 2. 构造索引类型的等价关系。`Equiv.sumCompl` 是 Mathlib 的标准工具，
--   --    它证明了任何类型 `α` 都等价于其子集 `p` 与补集 `¬p` 的不交并。
--   let e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}) := (Equiv.sumCompl p_ι).symm
--   let e_κ : κ ≃ ({j // p_κ j} ⊕ {j // ¬p_κ j}) := (Equiv.sumCompl p_κ).symm
--   {
--     -- `Sliceι` 和 `Sliceκ` 定义了子问题的索引类型，即排除了主元索引后的剩余部分。
--     Sliceι := {i : ι // i ≠ i₀},
--     Sliceκ := {j : κ // j ≠ j₀},
--     finEnum_slice_ι := inferInstance,
--     finEnum_slice_κ := inferInstance,

--     -- 可切片条件：左上角主元必须是可逆的。
--     IsSliceable := fun A ↦ IsUnit (A i₀ j₀),

--     -- 切片操作：提取右下角的子矩阵。
--     slice := fun A _hA ↦ A.submatrix (fun i ↦ i.val) (fun j ↦ j.val),

--     -- 重构操作：这是一个纯代数构造，用于从子问题的解 `slice_sol` 重建完整矩阵。
--     reconstruct := fun A hA slice_sol ↦
--       -- 3. 使用 `reindex` 将原始矩阵 A 的索引类型转换为分块形式，以便提取分块。
--       let A_reindexed := reindex e_ι e_κ A
--       --    `toBlocks` 系列函数从这个 reindex 后的矩阵中提取出四个分块。
--       let A₁₁ := A_reindexed.toBlocks₁₁
--       let A₁₂ := A_reindexed.toBlocks₁₂
--       let A₂₁ := A_reindexed.toBlocks₂₁
--       -- 4. 使用 `fromBlocks` 将分块重新组装。注意，右下角使用的是 `slice_sol`。
--       let new_block_matrix := fromBlocks A₁₁ A₁₂ A₂₁ slice_sol
--       -- 5. 使用 `reindex` 和等价关系的逆，将组装好的分块矩阵的类型安全地转换回原始矩阵类型。
--       new_block_matrix.reindex e_ι.symm e_κ.symm,

--     -- 健全性检查：证明 `reconstruct` 和 `slice` 是配对的。
--     -- 即，用一个矩阵自己的切片去重构它，会得到它自己。
--     reconstruct_slice_eq := by
--       intro A hA
--       -- `dsimp only` 展开定义，使目标清晰化。
--       dsimp only

--       -- 步骤 1: 证明 `slice A hA` (即 `A.submatrix ...`) 等于 `A` 经过 `reindex` 后的右下角分块。
--       -- `toBlocks₂₂` 的定义就是通过 `submatrix` 实现的，因此它们在定义上是相等的 (`rfl`)。
--       have h_slice_eq_block₂₂ : A.submatrix (fun i ↦ @Subtype.val ι (fun i ↦ i ≠ i₀) i)
--           (fun j ↦ @Subtype.val κ (fun j ↦ j ≠ j₀) j) = (reindex e_ι e_κ A).toBlocks₂₂ := by
--         rfl

--       -- 步骤 2: 将 `fromBlocks` 的最后一个参数（即 `slice_sol`）替换为 `A` 对应的右下角分块。
--       rw [h_slice_eq_block₂₂]

--       -- 步骤 3: 证明用一个分块矩阵的四个部分去调用 `fromBlocks`，会得到这个分块矩阵本身。
--       -- `fromBlocks_toBlocks` 引理正是为此设计的。
--       let A_reindexed := reindex e_ι e_κ A
--       -- `simp` 在这里用于简化由 `let` 引入的局部定义，使 `rw` 能够匹配。
--       simp only [e_ι, e_κ, p_ι, p_κ]
--       -- 使用反向重写，将 `fromBlocks ...` 的表达式折叠成 `A_reindexed`。
--       rw [fromBlocks_toBlocks A_reindexed]

--       -- 步骤 4: 证明连续两次 `reindex` (一次正向，一次反向) 会回到原始矩阵。
--       -- `reindex_reindex` 引理保证了这一点。
--       simp [A_reindexed, e_ι, e_κ, p_ι, p_κ]
--   }

-- end SchurMethod
-- end MatDecompFormal.Components.Reductions
