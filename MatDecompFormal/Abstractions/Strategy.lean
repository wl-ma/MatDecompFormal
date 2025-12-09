import Mathlib.Data.FinEnum
import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Abstractions.Transformation

namespace MatDecompFormal.Abstractions

/-!
# 规约策略 (Reduction Strategy)

本文件定义了 `ReductionStrategy` 结构体，它是连接“变换” (`Transformation`)
和“规约” (`ReductionMethod`) 的桥梁，形成一个完整的、可执行的归纳步骤。

一个 `ReductionStrategy` 封装了驱动归纳证明中 `reach_metric` 引理所需的所有
算法组件和相关的性质证明。它将一个算法的“动态”部分——如何通过一系列变换
达到一个理想状态——与算法的“静态”部分——如何对一个理想状态的矩阵进行代数
分解——结合在一起。

它精确地描述了：
1.  **使用哪个变换 (`transform`)**: 为了达到可切片状态，我们应该使用哪个
    `Transformation` 实例。
2.  **使用哪种规约方法 (`reduction`)**: 一旦达到可切片状态，我们应该使用哪个
    `ReductionMethod` 来分解问题。
3.  **兼容性 (`goal_is_sliceable`)**: 一个关键的静态断言，确保所选变换的
    `Goal` 与所选规约方法的 `IsSliceable` 条件是等价的。
4.  **度量 (`μ`)**: 归纳所依赖的、可作用于任意尺寸矩阵的度量函数族。
5.  **单调性 (`μ_mono`)**: 证明度量在变换下是不增的。
6.  **进展性 (`slice_progress`)**: 证明切片操作总是能严格减小度量。

这个结构体是“自包含的”，它提供了构建 `reach_metric` 所需的全部信息。
而 `lift_from_slice` 的证明，因为它依赖于具体的分解模式 `Schema`，
将在最终的实例文件中作为连接 `Strategy` 和 `Schema` 的“胶水”引理来提供。
-/

/--
`ReductionStrategy` 结构体封装了驱动归纳证明所需的所有算法组件和性质证明。
-/
structure ReductionStrategy (ι κ R : Type*) [FinEnum ι] [FinEnum κ] [CommRing R] where
  /-- 用于达到可切片状态的变换。 -/
  transform : Transformation (Matrix ι κ R)
  /-- 用于分解问题的规约方法。 -/
  reduction : ReductionMethod ι κ R
  /--
  兼容性断言：变换的目标 `Goal` 必须与规约方法的 `IsSliceable` 条件在逻辑上等价。
  这是将 `transform` 和 `reduction` 安全地“粘合”在一起的保证。
  -/
  goal_is_sliceable : transform.Goal = reduction.IsSliceable
  /--
  归纳所依赖的度量函数。它被设计为多态的，可以接受任何尺寸 `ι' × κ'` 的矩阵，
  从而能够同时处理原始矩阵和“切片”后的子矩阵。
  -/
  μ : ∀ {ι' κ'} [FinEnum ι'] [FinEnum κ'], Matrix ι' κ' R → Nat
  /--
  度量单调性证明：对于由 `transform` 产生的任何变换，度量 `μ` 是不增的。
  -/
  μ_mono : ∀ {y x t}, y = transform.apply t x → μ y ≤ μ x
  /--
  切片进展性证明：在任何可切片的状态下，`reduction` 的 `slice` 操作总是能严格减小度量。
  这是保证归纳能够终止的核心。
  -/
  slice_progress : ∀ {A} (hA : reduction.IsSliceable A), μ (reduction.slice A hA) < μ A

/--
`ReductionStrategy.r` (v2 - 修正版)
这个版本的变换关系明确包含了“什么都不做”（自反性）的情况。
`r y x` 成立，意味着 y 要么就是 x，要么是通过 `transform` 从 x 得到的。
-/
def ReductionStrategy.r {ι κ R} [FinEnum ι] [FinEnum κ] [CommRing R]
    (S : ReductionStrategy ι κ R) (y x : Matrix ι κ R) : Prop :=
  (y = x) ∨ (∃ (t : S.transform.T), y = S.transform.apply t x)

/--
`ReductionStrategy.mk_reach_metric` (v3 - 最终修正版)
这个版本通过修正签名，彻底解决了宇宙层级问题，并移除了不必要的前提。

关键修改：返回类型是 `∃ (y : Matrix ι κ R), ...`，明确保证了输出矩阵
与输入矩阵 `A` 具有完全相同的索引类型 `ι` 和 `κ`。
-/
def ReductionStrategy.mk_reach_metric
    {ι κ R} [FinEnum ι] [FinEnum κ] [CommRing R]
    (S : ReductionStrategy ι κ R)
    : ∀ {A : Matrix ι κ R}, S.μ A > 0 →
      -- 返回的 y 与 A 具有相同的索引类型！
      ∃ (y : Matrix ι κ R),
      ∃ (hy : S.reduction.IsSliceable y),
      (S.r y A) ∧ S.μ (S.reduction.slice y hy) < S.μ A := by
  intro A h_mu_pos
  -- 直接检查 Goal 是否成立
  by_cases h_goal : S.transform.Goal A
  · -- Case 1: Goal 已经成立，无需变换，y 就是 A。
    use A
    have hA_sliceable : S.reduction.IsSliceable A := by
      rw [← S.goal_is_sliceable]; exact h_goal
    use hA_sliceable
    constructor
    · -- 证明 r A A 成立。根据新的 r 定义，我们选择左边的分支。
      apply Or.inl; rfl
    · -- 证明度量进展。
      exact S.slice_progress hA_sliceable
  · -- Case 2: Goal 不成立，先变换，再切片。
    let t := S.transform.find A h_goal
    let y := S.transform.apply t A
    -- y 的类型是 Matrix ι κ R，与 A 相同，因为 apply 是保维度的。
    use y
    have hy_sliceable : S.reduction.IsSliceable y := by
      rw [← S.goal_is_sliceable]; exact S.transform.find_spec A h_goal
    use hy_sliceable
    constructor
    · -- 证明 r y A 成立。根据新的 r 定义，我们选择右边的分支。
      apply Or.inr; use t
    · -- 证明度量进展。
      calc
        S.μ (S.reduction.slice y hy_sliceable) < S.μ y := S.slice_progress hy_sliceable
        _                                      ≤ S.μ A := S.μ_mono rfl


end MatDecompFormal.Abstractions
