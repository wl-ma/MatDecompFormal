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
