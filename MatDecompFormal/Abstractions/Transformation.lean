import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Tactic.SplitIfs -- 明确导入 `split_ifs`

namespace MatDecompFormal.Abstractions

/-!
# 变换 (Transformation)

本文件定义了 `Transformation` 结构体，它为矩阵变换提供了一个统一的、
目标导向的抽象接口。这个抽象的核心思想是，一个变换不仅仅是一个函数，
它还与一个明确的“目标”相关联。

一个 `Transformation` 实例封装了以下信息：
1.  **变换类型 (`T`)**: 描述一个具体变换所需参数的类型。例如，对于行交换，
    `T` 可以是一对行索引 `ι × ι`；对于 Householder 变换，`T` 可以是一个向量。
2.  **目标 (`Goal`)**: 一个谓词，描述了该变换旨在让矩阵达到的状态。例如，
    “主元非零”或“第一列的特定元素为零”。
3.  **可判定性 (`decGoal`)**: 一个证明，确保 `Goal` 是一个算法上可判定的性质。
    这是在证明和计算中能够使用 `if ... then ... else` 的关键。
4.  **应用 (`apply`)**: 如何将一个具体的变换实例 `t : T` 应用于矩阵。
5.  **查找 (`find`)**: 一个构造性函数。如果一个矩阵尚未达到 `Goal`，`find`
    能够找到一个具体的变换 `t : T`。
6.  **规约 (`find_spec`)**: `find` 函数的正确性证明，保证它找到的变换 `t`
    在应用后确实能使矩阵满足 `Goal`。

此外，本文件还定义了两种变换的组合方式：
- `compose`: 用于严格的、每一步都必须执行的顺序组合。
- `compose_sequential`: 用于灵活的、只执行必要步骤的顺序组合。
-/


/--
`Transformation` 是一个描述“目标导向”的矩阵变换的结构体。

*   `X`: 被变换对象的类型，在本项目中通常是 `Matrix ι κ R`。
*   `T`: 变换参数的类型。
*   `Goal`: 变换旨在达到的目标状态，是一个谓词。
*   `decGoal`: 一个实例，证明 `Goal` 是一个可判定的谓词。
*   `apply`: 将一个变换参数 `t : T` 应用于对象 `x : X`。
*   `find`: 当对象 `x` 不满足 `Goal` 时，找到一个能使其满足 `Goal` 的变换参数 `t`。
*   `find_spec`: 证明 `find` 找到的 `t` 是有效的。
-/
structure Transformation (X : Type*) where
  /-- 变换参数的类型。例如，对于行交换，是 `ι × ι`。 -/
  T : Type*
  /-- 变换旨在达到的目标状态。例如 `fun A ↦ A i₀ j₀ ≠ 0`。 -/
  Goal : X → Prop
  /-- 证明 `Goal` 是一个可判定的谓词。这是使用 `if` 语句的前提。 -/
  [decGoal : DecidablePred Goal]
  /-- 将变换应用于对象。 -/
  apply : T → X → X
  /-- 当目标未达成时，找到一个有效的变换。这是一个构造性的核心。 -/
  find : (x : X) → (h : ¬ Goal x) → T
  /-- `find` 函数的正确性证明，确保 `find` 找到了正确的变换。 -/
  find_spec : ∀ (x : X) (h : ¬ Goal x), Goal (apply (find x h) x)

-- 将 `decGoal` 注册为类型类实例，使得 Lean 在遇到 `if T.Goal x then ...` 时能自动找到判定依据。
attribute [instance] Transformation.decGoal


/--
`Transformation.compose` 函数将两个变换 `T₁` 和 `T₂` 严格地按顺序串联起来，
形成一个新的宏观变换。

这个组合适用于“总是先执行 `T₁`，再执行 `T₂`”的场景，例如 `T₁` 为 `T₂` 准备前提条件。

*   **`h_precond`**: 一个关键的辅助函数。调用者必须提供一个方法，
    从“最终目标 `T₂.Goal` 未达成”推导出“第一步目标 `T₁.Goal` 也未达成”。
    这形式化了 `T₁` 是 `T₂` 的必要前置步骤这一概念。
*   **`h_preserves`**: 另一个前提，确保 `T₁` 的应用不会意外地“修复”`T₂` 的问题，
    从而保证 `T₂.find` 总是可以被调用。
-/
def Transformation.compose {X} (T₁ T₂ : Transformation X)
    (h_precond : ∀ x, ¬ T₂.Goal x → ¬ T₁.Goal x)
    (h_preserves : ∀ (x : X) (h₁ : ¬ T₁.Goal x),
      ¬ T₂.Goal x → ¬ T₂.Goal (T₁.apply (T₁.find x h₁) x))
    : Transformation X where
  T := T₁.T × T₂.T
  Goal := T₂.Goal
  decGoal := T₂.decGoal
  apply := fun (t₁, t₂) x ↦ T₂.apply t₂ (T₁.apply t₁ x)
  find := fun x h_goal_not_met ↦
    -- 利用 h_precond 从最终目标未达成推导出第一步目标未达成
    let h₁ := h_precond x h_goal_not_met
    let t₁_inst := T₁.find x h₁
    let x' := T₁.apply t₁_inst x
    -- 利用 h_preserves 证明在应用 T₁ 后，T₂ 的目标仍然未达成
    let h₂ := h_preserves x h₁ h_goal_not_met
    let t₂_inst := T₂.find x' h₂
    (t₁_inst, t₂_inst)
  find_spec := by
    intro x h_goal_not_met
    -- `simp only` 在这里用于展开 `find` 和 `apply` 的定义，使目标更清晰。
    -- 但由于 `find` 内部使用了 `let`，直接 `simp` 可能效果不佳。
    -- 更稳健的证明是手动模拟 `find` 的逻辑。
    let h₁ := h_precond x h_goal_not_met
    let t₁_inst := T₁.find x h₁
    let x' := T₁.apply t₁_inst x
    let h₂ := h_preserves x h₁ h_goal_not_met
    let t₂_inst := T₂.find x' h₂
    -- 目标是 `T₂.Goal (T₂.apply t₂_inst x')`，这正是 `T₂.find_spec` 的结论。
    exact T₂.find_spec x' h₂

/--
`Transformation.compose_sequential` 是一个更灵活的顺序组合器。

它适用于以下场景：我们想先达成 `T₁` 的目标，然后再达成 `T₂` 的目标，但其中
任何一步都可能因为目标已经达成而被跳过。

*   **新的变换类型 `T`**: `Option T₁.T × Option T₂.T`。`none` 表示该步骤的变换
    是不必要的（因为目标已经达成）。
*   **新的 `find` 逻辑**: 它会精确地计算出哪一步变换是必需的。
-/
def Transformation.compose_sequential {X} (T₁ T₂ : Transformation X) :
    Transformation X where
  T := Option T₁.T × Option T₂.T
  Goal := T₂.Goal
  decGoal := T₂.decGoal
  apply := fun
    | (some t₁, some t₂) => fun x ↦ T₂.apply t₂ (T₁.apply t₁ x)
    | (some t₁, none)    => fun x ↦ T₁.apply t₁ x
    | (none,    some t₂) => fun x ↦ T₂.apply t₂ x
    | (none,    none)    => fun x ↦ x
  find := fun x h_t2_goal_not_met ↦
    if h₁ : T₁.Goal x then
      -- 步骤1的目标已达成，只需执行步骤2。
      (none, some (T₂.find x h_t2_goal_not_met))
    else
      -- 步骤1的目标未达成，必须先执行步骤1。
      let t₁_inst := T₁.find x h₁
      let x' := T₁.apply t₁_inst x
      if h₂ : T₂.Goal x' then
        -- 应用 T₁ 后，步骤2的目标意外达成，无需执行步骤2。
        (some t₁_inst, none)
      else
        -- 应用 T₁ 后，步骤2的目标仍未达成，需继续执行步骤2。
        (some t₁_inst, some (T₂.find x' h₂))
  find_spec := by
    intro x h_t2_goal_not_met
    -- `simp only` 用于展开 `find` 的定义，让 `split_ifs` 可以看到 `if` 语句。
    simp only
    -- 根据 `find` 函数中的 `if` 条件进行分支证明。
    split_ifs with h₁ h₂
    · -- 分支 1: T₁.Goal x (h₁) 为真。
      -- `find` 返回 (none, some ...)，`apply` 应用 T₂。
      -- 目标 `T₂.Goal (T₂.apply ...)` 由 `T₂.find_spec` 保证。
      simp only
      exact T₂.find_spec x h_t2_goal_not_met
    · -- 分支 2: ¬ T₁.Goal x (h₁) 且 T₂.Goal (T₁.apply ... x) (h₂) 为真。
      -- `find` 返回 (some ..., none)，`apply` 应用 T₁。
      -- 目标 `T₂.Goal (T₁.apply ... x)` 正是前提 `h₂`。
      exact h₂
    · -- 分支 3: ¬ T₁.Goal x (h₁) 且 ¬ T₂.Goal (T₁.apply ... x) (h₂)。
      -- `find` 返回 (some ..., some ...)，`apply` 先应用 T₁ 再应用 T₂。
      -- 目标 `T₂.Goal (T₂.apply ... (T₁.apply ... x))` 由 `T₂.find_spec` 保证。
      simp only
      let x' := T₁.apply (T₁.find x h₁) x
      exact T₂.find_spec x' h₂

end MatDecompFormal.Abstractions
