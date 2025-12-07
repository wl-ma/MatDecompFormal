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
`ReductionStrategy.r` 是从一个 `Strategy` 实例派生出的变换关系。

它被定义为一个独立的函数而不是结构体字段，以确保其定义是“透明的”。
这使得 Lean 的战术（如 `use`）可以“看穿”`r` 的定义，并将其展开为 `∃ t, ...`，
从而让存在性证明能够顺利进行。
-/
def ReductionStrategy.r {ι κ R} [FinEnum ι] [FinEnum κ] [CommRing R]
    (S : ReductionStrategy ι κ R) (y x : Matrix ι κ R) : Prop :=
  ∃ (t : S.transform.T), y = S.transform.apply t x

/--
`ReductionStrategy.mk_reach_metric` 是一个辅助函数，它利用一个 `ReductionStrategy`
实例来自动生成 `transformSliceInduction` 所需的 `reach_metric` 参数。

这是该抽象的核心优势：它将一个需要复杂存在性证明的参数 (`reach_metric`)
转化为一个可以通过组合 `Transformation` 和 `ReductionMethod` 自动满足的构造。

**注意**: 这个函数需要一个额外的假设 `h_non_base_implies_not_goal`。
这个假设在实践中总是成立的，因为它形式化了“如果问题还未小到基例的程度，
那么它一定有继续规约的空间”这一直觉。
-/
def ReductionStrategy.mk_reach_metric
    {ι κ R} [FinEnum ι] [FinEnum κ] [CommRing R]
    (S : ReductionStrategy ι κ R)
    (h_non_base_implies_not_goal : ∀ A, S.μ A > 0 → ¬ S.transform.Goal A)
    : ∀ {A : Matrix ι κ R}, S.μ A > 0 →
      ∃ y, ∃ (hy : S.reduction.IsSliceable y),
      (S.r y A) ∧ S.μ (S.reduction.slice y hy) < S.μ A := by
  -- 目标：对于任意度量大于0的矩阵 A，证明存在一个变换后的 y...
  intro A h_μ_pos
  -- 步骤 1: 证明 A 尚未达到变换目标。
  -- 这是由 `h_non_base_implies_not_goal` 假设直接提供的。
  have h_goal_not_met : ¬ S.transform.Goal A := h_non_base_implies_not_goal A h_μ_pos
  -- 步骤 2: 构造性地找到一个变换 `t` 和变换后的矩阵 `y`。
  -- 这是由 `S.transform.find` 保证的。
  let t := S.transform.find A h_goal_not_met
  let y := S.transform.apply t A
  -- 步骤 3: 证明变换后的 `y` 是可切片的。
  -- 这是由 `S.transform.find_spec` 和 `S.goal_is_sliceable` 保证的。
  have hy_sliceable : S.reduction.IsSliceable y := by
    rw [← S.goal_is_sliceable]; exact S.transform.find_spec A h_goal_not_met
  -- 步骤 4: 组装存在性证明。
  use y, hy_sliceable
  constructor
  · -- 证明 `S.r y A` 成立。
    -- `use t` 提供了存在性证明的见证。
    use t
    -- `rfl` 证明了 `y = S.transform.apply t A`，因为 `y` 正是这样定义的。
  · -- 证明度量严格减小。
    -- 使用 `calc` 块来清晰地展示证明链条。
    calc
      -- 首先，根据 `slice_progress`，切片操作会减小 `y` 的度量。
      S.μ (S.reduction.slice y hy_sliceable) < S.μ y := S.slice_progress hy_sliceable
      -- 其次，根据 `μ_mono`，变换不会增加度量，所以 `μ y ≤ μ A`。
      _                                      ≤ S.μ A := S.μ_mono rfl

end MatDecompFormal.Abstractions
