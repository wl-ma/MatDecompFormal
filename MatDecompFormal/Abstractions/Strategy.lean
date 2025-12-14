import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Abstractions.Transformation
import MatDecompFormal.Framework.Universe -- For FinRectUniverse

namespace MatDecompFormal.Abstractions

open MatDecompFormal.Framework

/-!
# 规约策略 (Reduction Strategy) - v3.1 (类型参数化维度)

本文件定义了 `ReductionStrategy`，它将“变换”和“规约”组合成一个
完整的、在 `Fin m × Fin n` 矩阵上可执行的归纳步骤。

v3.1 更新：
- `slice_m` 和 `slice_n` 现在是 `ReductionStrategy` 的类型参数，
  以匹配 `ReductionMethod` v3.1 的新设计。
-/

/--
`ReductionStrategy` (v3.1 版)

*   `m`, `n`: 原始矩阵的维度。
*   `slice_m`, `slice_n`: 子问题矩阵的维度。
*   `R`: 环类型。
-/
structure ReductionStrategy (m n slice_m slice_n : ℕ) (R : Type*) [CommRing R] where
  /-- 用于达到可切片状态的变换。 -/
  transform : Transformation (Matrix (Fin m) (Fin n) R)
  /-- 用于分解问题的规约方法。 -/
  reduction : ReductionMethod m n slice_m slice_n R
  /-- 兼容性断言：变换的目标 `Goal` 必须与规约方法的 `IsSliceable` 条件在逻辑上等价。 -/
  goal_is_sliceable : transform.Goal = reduction.IsSliceable
  /-- 归纳所依赖的度量函数。它作用于通用宇宙对象。 -/
  μ : FinRectUniverse R → ℕ
  /-- 度量单调性证明。 -/
  μ_mono : ∀ (A : Matrix (Fin m) (Fin n) R) (t : transform.T),
             μ ⟨⟨m, n⟩, ⟨transform.apply t A⟩⟩ ≤ μ ⟨⟨m, n⟩, ⟨A⟩⟩
  /-- 切片进展性证明。 -/
  slice_progress : ∀ (A : Matrix (Fin m) (Fin n) R) (hA : reduction.IsSliceable A),
    μ ⟨⟨slice_m, slice_n⟩, ⟨reduction.slice A hA⟩⟩ < μ ⟨⟨m, n⟩, ⟨A⟩⟩

/--
`ReductionStrategy.r` 定义了策略所允许的变换关系。
-/
def ReductionStrategy.r {m n slice_m slice_n R} [CommRing R]
    (S : ReductionStrategy m n slice_m slice_n R) (y x : Matrix (Fin m) (Fin n) R) : Prop :=
  (y = x) ∨ (∃ (t : S.transform.T), y = S.transform.apply t x)

/--
`ReductionStrategy.mk_reach` 从一个策略中自动构造出
`PositiveDecompositionInstance` 所需的 `reach` 证明。
-/
noncomputable def ReductionStrategy.mk_reach {m n slice_m slice_n R} [CommRing R]
    (S : ReductionStrategy m n slice_m slice_n R) (μ_base : ℕ)
    (_h_pos : m > 0 ∧ n > 0)
    (A : Matrix (Fin m) (Fin n) R)
    (_h_mu_gt_base : S.μ ⟨⟨m, n⟩, ⟨A⟩⟩ > μ_base)
    : Σ' (B : Matrix (Fin m) (Fin n) R),
        Σ' (hB : S.reduction.IsSliceable B),
          S.r B A ∧ S.μ ⟨⟨slice_m, slice_n⟩, ⟨S.reduction.slice B hB⟩⟩ < S.μ ⟨⟨m,n⟩,⟨A⟩⟩ := by
  by_cases h_goal : S.transform.Goal A
  · -- Case 1: Goal met. The new matrix is just A.
    refine ⟨A, ?_⟩
    have hA_sliceable : S.reduction.IsSliceable A := by
      rw [← S.goal_is_sliceable]; exact h_goal
    refine ⟨hA_sliceable, ?_⟩
    exact ⟨Or.inl rfl, S.slice_progress A hA_sliceable⟩
  · -- Case 2: Goal not met. The new matrix is B.
    let t := S.transform.find A h_goal
    let B := S.transform.apply t A
    refine ⟨B, ?_⟩
    have hB_sliceable : S.reduction.IsSliceable B := by
      rw [← S.goal_is_sliceable]; exact S.transform.find_spec A h_goal
    refine ⟨hB_sliceable, ?_⟩
    refine ⟨Or.inr ⟨t, rfl⟩, ?_⟩
    calc
      _ < S.μ ⟨⟨m,n⟩,⟨B⟩⟩ := S.slice_progress B hB_sliceable
      _ ≤ S.μ ⟨⟨m,n⟩,⟨A⟩⟩ := S.μ_mono A t

end MatDecompFormal.Abstractions





-- import Mathlib.Data.FinEnum
-- import MatDecompFormal.Abstractions.ReductionMethod
-- import MatDecompFormal.Abstractions.Transformation

-- namespace MatDecompFormal.Abstractions

-- /-!
-- # 规约策略 (Reduction Strategy) - v2.1 (Final)

-- 本文件定义了 `ReductionStrategy` 结构体，它是连接“变换” (`Transformation`)
-- 和“规约” (`ReductionMethod`) 的桥梁，形成一个完整的、可执行的归纳步骤。

-- 它精确地描述了：
-- 1.  **使用哪个变换 (`transform`)**: 为了达到可切片状态，我们应该使用哪个
--     `Transformation` 实例。
-- 2.  **使用哪种规约方法 (`reduction`)**: 一旦达到可切片状态，我们应该使用哪个
--     `ReductionMethod` 来分解问题。
-- 3.  **兼容性 (`goal_is_sliceable`)**: 一个关键的静态断言，确保所选变换的
--     `Goal` 与所选规约方法的 `IsSliceable` 条件是等价的。
-- 4.  **度量 (`μ`)**: 归纳所依赖的、可作用于任意尺寸矩阵的度量函数族。
-- 5.  **单调性 (`μ_mono`)**: 证明度量在变换下是不增的。
-- 6.  **进展性 (`slice_progress`)**: 证明切片操作总是能严格减小度量。
-- -/

-- /--
-- `ReductionStrategy` 结构体封装了驱动归纳证明所需的所有算法组件和性质证明。
-- -/
-- structure ReductionStrategy (ι κ R : Type*) [FinEnum ι] [FinEnum κ] [CommRing R] where
--   /-- 用于达到可切片状态的变换。 -/
--   transform : Transformation (Matrix ι κ R)
--   /-- 用于分解问题的规约方法。 -/
--   reduction : ReductionMethod ι κ R
--   /--
--   兼容性断言：变换的目标 `Goal` 必须与规约方法的 `IsSliceable` 条件在逻辑上等价。
--   -/
--   goal_is_sliceable : transform.Goal = reduction.IsSliceable
--   /--
--   归纳所依赖的度量函数。它被设计为多态的，可以接受任何尺寸的矩阵。
--   -/
--   μ : ∀ {ι' κ'} [FinEnum ι'] [FinEnum κ'], Matrix ι' κ' R → Nat
--   /--
--   度量单调性证明：对于由 `transform` 产生的任何变换，度量 `μ` 是不增的。
--   -/
--   μ_mono : ∀ (A : Matrix ι κ R) (t : transform.T), μ (transform.apply t A) ≤ μ A
--   /--
--   切片进展性证明：在任何可切片的状态下，`reduction` 的 `slice` 操作总是能严格减小度量。
--   -/
--   slice_progress : ∀ (A : Matrix ι κ R) (hA : reduction.IsSliceable A),
--     μ (reduction.slice A hA) < μ A

-- /--
-- `ReductionStrategy.r` 定义了策略所允许的变换关系。
-- `r y x` 成立，意味着 `y` 要么就是 `x`（无需变换），要么是通过对 `x`
-- 应用 `transform` 中的某个变换 `t` 得到的。
-- -/
-- def ReductionStrategy.r {ι κ R} [FinEnum ι] [FinEnum κ] [CommRing R]
--     (S : ReductionStrategy ι κ R) (y x : Matrix ι κ R) : Prop :=
--   (y = x) ∨ (∃ (t : S.transform.T), y = S.transform.apply t x)

-- /--
-- `ReductionStrategy.mk_reach_metric` 从一个策略中自动构造出归纳法所需的 `reach_metric` 证明。
-- -/
-- def ReductionStrategy.mk_reach_metric
--     {ι κ R} [FinEnum ι] [FinEnum κ] [CommRing R]
--     (S : ReductionStrategy ι κ R)
--     : ∀ {A : Matrix ι κ R}, S.μ A > 0 →
--       ∃ (y : Matrix ι κ R),
--       ∃ (hy : S.reduction.IsSliceable y),
--       (S.r y A) ∧ S.μ (S.reduction.slice y hy) < S.μ A := by
--   intro A h_mu_pos
--   -- 直接检查 Goal 是否成立。由于 Goal 有 DecidablePred 实例，我们可以使用 by_cases。
--   by_cases h_goal : S.transform.Goal A
--   · -- Case 1: Goal 已经成立，无需变换，y 就是 A。
--     use A
--     have hA_sliceable : S.reduction.IsSliceable A := by
--       rw [← S.goal_is_sliceable]; exact h_goal
--     use hA_sliceable
--     constructor
--     · -- 证明 r A A 成立。根据 r 的定义，我们选择左边的分支。
--       apply Or.inl; rfl
--     · -- 证明度量进展。
--       exact S.slice_progress A hA_sliceable
--   · -- Case 2: Goal 不成立，先变换，再切片。
--     let t := S.transform.find A h_goal
--     let y := S.transform.apply t A
--     use y
--     have hy_sliceable : S.reduction.IsSliceable y := by
--       rw [← S.goal_is_sliceable]; exact S.transform.find_spec A h_goal
--     use hy_sliceable
--     constructor
--     · -- 证明 r y A 成立。根据 r 的定义，我们选择右边的分支。
--       apply Or.inr; use t
--     · -- 证明度量进展。
--       calc
--         S.μ (S.reduction.slice y hy_sliceable) < S.μ y := S.slice_progress y hy_sliceable
--         _                                      ≤ S.μ A := S.μ_mono A t

-- end MatDecompFormal.Abstractions
