import Mathlib.LinearAlgebra.Matrix.Permutation
import MatDecompFormal.Abstractions.Transformation
import Mathlib.LinearAlgebra.Matrix.Swap

namespace MatDecompFormal.Components.Transformations.Elementary

open Matrix

/-!
# 主元变换 (Pivoting Transformation) - v2.0 (NeZero 修正版)

本文件定义了 `PivotTransform`，这是一个在 `Fin n` 世界中实现的 `Transformation`
实例，其目标是通过行交换确保矩阵的 `A 0 0` 元素非零。

### 设计 (v2.0)
- **NeZero 约束**: 为了解决 `Fin n` 上的 `0` 索引问题，`PivotTransform`
  现在要求 `n` 和 `m` 必须为非零，即 `[NeZero n]` 和 `[NeZero m]`。
  这保证了 `Fin n` 和 `Fin m` 类型是非空的，使得 `0` 成为一个合法的索引。
- **解耦机制与策略**: 保持了原有的设计，将“执行交换”的机制与“找到交换目标”
  的策略（由外部提供）解耦。
-/

/--
`PivotTransform` 是一个 `Transformation` 实例，它通过行交换来确保
主元 `A 0 0` 的元素非零。

*   `[NeZero n]`, `[NeZero m]`: 关键的前提，确保 `0` 是 `Fin n` 和 `Fin m` 的有效索引。
*   `search_for_pivot`: 一个由外部提供的“搜索算法”。
*   `search_spec`: 对 `search_for_pivot` 算法的正确性证明。
-/
noncomputable def PivotTransform (n m : ℕ) (R : Type*)
    -- 添加 NeZero 约束
    [NeZero n] [NeZero m] [Field R] [DecidableEq R]
    (search_for_pivot : (A : Matrix (Fin n) (Fin m) R) → (h : A 0 0 = 0) → Fin n)
    (search_spec : ∀ (A : Matrix (Fin n) (Fin m) R) (h : A 0 0 = 0),
      A (search_for_pivot A h) 0 ≠ 0) :
    Abstractions.Transformation (Matrix (Fin n) (Fin m) R) where
  -- 变换参数就是目标行的索引。
  T := Fin n
  -- 目标是主元非零。
  Goal := fun A ↦ A 0 0 ≠ 0
  -- `Field` 和 `DecidableEq` 保证了 `Goal` 是可判定的。
  decGoal := by infer_instance
  -- 应用变换：左乘一个行交换矩阵 `swap R 0 i₁`。
  -- 这里的 `0` 现在是类型安全的，因为有 `[NeZero n]` 约束。
  apply := fun i₁ A ↦ (swap R 0 i₁) * A
  -- `find` 操作直接委托给外部提供的搜索算法。
  find := fun A h_goal_not_met ↦ search_for_pivot A (not_ne_iff.mp h_goal_not_met)
  -- `find_spec` 的证明直接来自搜索算法的正确性证明 `search_spec`。
  find_spec := by
    intro A h_goal_not_met
    let i₁ := search_for_pivot A (not_ne_iff.mp h_goal_not_met)
    -- `swap_mul_apply_left` 同样需要 `0` 是有效索引，`[NeZero n]` 保证了这一点。
    rw [swap_mul_apply_left]
    exact search_spec A (not_ne_iff.mp h_goal_not_met)

end MatDecompFormal.Components.Transformations.Elementary






-- import Mathlib.Data.FinEnum
-- import Mathlib.LinearAlgebra.Matrix.Permutation -- For isPermutation_swap
-- import MatDecompFormal.Abstractions.Transformation
-- import Mathlib.LinearAlgebra.Matrix.Swap -- For swap and swap_mul_apply_left

-- namespace MatDecompFormal.Components.Transformations.Elementary

-- open Matrix FinEnum

-- /-!
-- # 主元变换 (Pivoting Transformation) - (最终版)

-- 本文件定义了 `PivotTransform`，这是一个 `Transformation` 的具体实例，
-- 其目标是确保矩阵中的一个特定位置（主元）的元素非零。这是通过行交换实现的。

-- ### 设计哲学：解耦“机制”与“策略”

-- 这个组件的设计将“执行交换”的**机制**与“找到交换目标”的**策略**（或算法）
-- 完全解耦。

-- 1.  **机制 (由 `PivotTransform` 提供)**:
--     - **目标 (`Goal`)**: `fun A ↦ A i₀ j₀ ≠ 0`。
--     - **变换类型 (`T`)**: `ι`，即要交换的目标行索引。
--     - **应用 (`apply`)**: `fun i₁ A ↦ (swap R i₀ i₁) * A`，即左乘一个行交换矩阵。

-- 2.  **策略 (由调用者提供)**:
--     - `PivotTransform` 的构造函数要求调用者提供一个**搜索函数** `search_for_pivot`
--       及其**正确性证明** `search_spec`。
--     - `find` 操作直接委托给这个外部提供的搜索函数。

-- 这种设计使得 `PivotTransform` 成为一个纯粹的、无内部假设的代数工具。
-- 它可以被任何需要行交换的分解算法复用，只需在组装 `ReductionStrategy` 时
-- 提供各自的、特有的主元搜索逻辑即可。
-- -/

-- section PivotTransform

-- -- 声明所有定义共享的类型和类型类实例。
-- -- 我们需要一个域 `Field`，因为“非零”的概念在域上最自然，并且
-- -- `DecidableEq` 使得我们可以轻松地判断元素是否为零。
-- variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Field R] [DecidableEq R]

-- /--
-- `PivotTransform` 是一个 `Transformation` 实例，它通过行交换来确保
-- 主元 `(i₀, j₀)` 的元素非零。

-- *   `i₀`, `j₀`: 主元的行和列索引。
-- *   `search_for_pivot`: 一个由外部提供的“搜索算法”。当主元 `A i₀ j₀` 为零时，
--     这个函数负责找到一个合适的行 `i₁` 用于交换。
-- *   `search_spec`: 对 `search_for_pivot` 算法的正确性证明，保证它找到的行 `i₁`
--     在 `j₀` 列上的元素确实非零。
-- -/
-- noncomputable def PivotTransform (i₀ : ι) (j₀ : κ)
--     (search_for_pivot : (A : Matrix ι κ R) → (h : A i₀ j₀ = 0) → ι)
--     (search_spec : ∀ (A : Matrix ι κ R) (h : A i₀ j₀ = 0),
--       A (search_for_pivot A h) j₀ ≠ 0) :
--     Abstractions.Transformation (Matrix ι κ R) where
--   -- 变换参数就是目标行的索引。
--   T := ι
--   -- 目标是主元非零。
--   Goal := fun A ↦ A i₀ j₀ ≠ 0
--   -- `Field` 和 `DecidableEq` 保证了 `Goal` 是可判定的。
--   decGoal := inferInstance
--   -- 应用变换：左乘一个行交换矩阵 `swap R i₀ i₁`。
--   apply := fun i₁ A ↦ (swap R i₀ i₁) * A
--   -- `find` 操作直接委托给外部提供的搜索算法。
--   find := fun A h_goal_not_met ↦ search_for_pivot A (not_ne_iff.mp h_goal_not_met)
--   -- `find_spec` 的证明直接来自搜索算法的正确性证明 `search_spec`。
--   find_spec := by
--     intro A h_goal_not_met
--     let i₁ := search_for_pivot A (not_ne_iff.mp h_goal_not_met)
--     rw [swap_mul_apply_left]
--     exact search_spec A (not_ne_iff.mp h_goal_not_met)

-- end PivotTransform

-- end MatDecompFormal.Components.Transformations.Elementary
