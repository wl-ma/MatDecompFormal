import Mathlib
import MatDecompFormal.Framework.Universe -- 明确指出宇宙类型来自这里


namespace MatDecompFormal.Framework

/-!
# 通用归纳框架 (The General Induction Framework) - v3.0 (Universe Version)

本文件定义了整个形式化项目的核心归纳原理。这个最终版本基于一个“宇宙”
类型 `X`，它包含了所有可能尺寸的矩阵。通过在这个统一的类型上进行
归纳，我们优雅地解决了跨类型（即降维）规约的问题。

在本项目的应用中，这个宇宙 `X` 将被实例化为 `Σ n, SquareMatFamily n R`，
即所有维度方阵的带依赖的求和类型。

### 框架层次
1.  **`X` (宇宙类型)**:
    一个统一的类型，封装了所有可能尺寸的矩阵。

2.  **`induction_by_reduction` (核心引擎)**:
    最底层的、统一的归纳原理，在 `X` 宇宙上操作。它将证明任务分解为
    处理一个明确指定的“基例集合” (`BaseSet`) 和一个“规约步骤”。

3.  **`wellFounded_induction_via_reduction` (通用API)**:
    `induction_by_reduction` 的一个便利封装，用于处理当基例就是归纳关系下的
    “最小元”集合时的常见情况。

4.  **`transformSliceInduction` (领域特定API)**:
    另一个便利封装，专门为本项目设计，用于处理当归纳基于一个自然数
    度量 `μ`，且基例是“度量为0”的集合时。这是本项目中最常被直接调用的定理。
-/

variable {X : Type*}

/--
`Transport r P` 叙述了命题 `P` 可以在变换 `r` 下“传递”。
-/
def Transport (r : X → X → Prop) (P : X → Prop) : Prop :=
  ∀ (x y : X), r x y → P x → P y


-- ==================================================================
-- L0: THE CORE ENGINE (on X)
-- ==================================================================

/--
`induction_by_reduction` 是本框架最核心的、统一的归纳原理，
它在 `X` 宇宙上操作。
-/
theorem induction_by_reduction
    {rel : X → X → Prop} (hwf : WellFounded rel)
    (BaseSet : X → Prop)
    {r : X → X → Prop} {P : X → Prop}
    (h_trans : Transport r P)
    (IsReducible : X → Prop)
    (decompose : ∀ {x : X}, IsReducible x → X)
    (reconstruct : ∀ {x : X} (hx : IsReducible x), P (decompose hx) → P x)
    (prove_on_base : ∀ {x : X}, BaseSet x → P x)
    (reach_from_non_base : ∀ {x : X}, ¬ BaseSet x →
      ∃ y, ∃ (hy : IsReducible y), r y x ∧ rel (decompose hy) x)
    : ∀ (x : X), P x := by
  intro x_to_prove
  apply hwf.induction x_to_prove
  clear x_to_prove
  intro x ih
  by_cases h_is_base : BaseSet x
  · exact prove_on_base h_is_base
  · rcases reach_from_non_base h_is_base with ⟨y, hy, h_r_yx, h_rel_decompose⟩
    have p_decompose : P (decompose hy) := ih (decompose hy) h_rel_decompose
    have p_y : P y := reconstruct hy p_decompose
    exact h_trans y x h_r_yx p_y

-- ==================================================================
-- L1: CONVENIENCE APIS (Corollaries of the Core Engine)
-- ==================================================================

/--
`wellFounded_induction_via_reduction` 是 `induction_by_reduction` 的一个实例，
专门用于基例是“最小元”集合的情况，在 `X` 宇宙上操作。
-/
theorem wellFounded_induction_via_reduction
    {rel : X → X → Prop} (hwf : WellFounded rel)
    {r : X → X → Prop} {P : X → Prop}
    (h_trans : Transport r P)
    (IsReducible : X → Prop)
    (decompose : ∀ {x : X}, IsReducible x → X)
    (reconstruct : ∀ {x : X} (hx : IsReducible x), P (decompose hx) → P x)
    (reachability : ∀ {x : X}, (∃ y, rel y x) →
      ∃ y, ∃ (hy : IsReducible y), r y x ∧ rel (decompose hy) x)
    (base_case : ∀ {x : X}, (¬ ∃ y, rel y x) → P x)
    : ∀ (x : X), P x := by
  -- 通过将 BaseSet 定义为最小元集合，直接调用核心引擎来证明。
  apply induction_by_reduction hwf
    (BaseSet := fun x ↦ ¬ ∃ y, rel y x)
    h_trans IsReducible decompose reconstruct
    (prove_on_base := base_case)
    (reach_from_non_base := by
      -- `¬ (¬ ∃ y, rel y x)` 等价于 `∃ y, rel y x`
      intro x h_non_minimal
      push_neg at h_non_minimal
      exact reachability h_non_minimal)


/--
`transformSliceInduction` (最终版): 这是一个在 `X` 宇宙中
进行良基归纳的便利API，是 `wellFounded_induction_via_reduction` 的一个实例。
-/
theorem transformSliceInduction
    (μ : X → Nat)
    (P : X → Prop)
    {r : X → X → Prop}
    (h_trans : Transport r P)
    (IsSliceable : X → Prop)
    (slice : ∀ {x : X}, IsSliceable x → X)
    (lift_from_slice : ∀ {x : X} (hx : IsSliceable x), P (slice hx) → P x)
    (reach_metric : ∀ {x : X}, μ x > 0 →
      ∃ y, ∃ (hy : IsSliceable y), r y x ∧ μ (slice hy) < μ x)
    (base_metric : ∀ {x : X}, μ x = 0 → P x)
    : ∀ (x : X), P x := by
  -- 直接调用核心引擎，明确定义基例集合。
  apply induction_by_reduction (WellFounded.onFun wellFounded_lt)
    (BaseSet := fun x ↦ μ x = 0)
    (h_trans := h_trans)
    (IsReducible := IsSliceable)
    (decompose := slice)
    (reconstruct := lift_from_slice)
    (prove_on_base := base_metric)
    (reach_from_non_base := by
      -- 证明 `¬ BaseSet x` 蕴含 `reach` 条件
      -- `¬ (μ x = 0)` 等价于 `μ x ≠ 0`。
      intro x h_non_base
      -- 对于自然数，`μ x ≠ 0` 等价于 `μ x > 0`。
      have h_mu_pos : μ x > 0 := Nat.pos_of_ne_zero h_non_base
      -- 直接应用 `reach_metric`
      exact reach_metric h_mu_pos)

variable {X : Type*}

/--
`transformSliceInductionGeneral`：`transformSliceInduction` 的扩展版本，
允许基例是任意给定的度量下界 `μ_base`（而非仅为 0）。

当 `μ x > μ_base` 时，需要找到一个可规约的状态，其切片后的度量严格变小；
当 `μ x ≤ μ_base` 时，直接使用 `base_metric`。
-/
theorem transformSliceInductionGeneral
    (μ : X → Nat) (μ_base : Nat)
    (P : X → Prop)
    {r : X → X → Prop}
    (h_trans : Transport r P)
    (IsSliceable : X → Prop)
    (slice : ∀ {x : X}, IsSliceable x → X)
    (lift_from_slice : ∀ {x : X} (hx : IsSliceable x), P (slice hx) → P x)
    (reach_metric : ∀ {x : X}, μ x > μ_base →
      ∃ y, ∃ (hy : IsSliceable y), r y x ∧ μ (slice hy) < μ x)
    (base_metric : ∀ {x : X}, μ x ≤ μ_base → P x)
    : ∀ (x : X), P x := by
  -- 直接调用核心引擎，基例集合是 `μ x ≤ μ_base`。
  apply induction_by_reduction (WellFounded.onFun wellFounded_lt)
    (BaseSet := fun x ↦ μ x ≤ μ_base)
    (h_trans := h_trans)
    (IsReducible := IsSliceable)
    (decompose := slice)
    (reconstruct := lift_from_slice)
    (prove_on_base := base_metric)
    (reach_from_non_base := by
      intro x h_non_base
      -- `¬ (μ x ≤ μ_base)` 等价于 `μ x > μ_base`。
      have h_mu_pos : μ x > μ_base := Nat.lt_of_not_ge h_non_base
      -- 直接使用提供的 `reach_metric`
      exact reach_metric h_mu_pos)


/--
`induction_on_subtype` (最终版核心归纳定理)

这是一个为“子集驱动”的归纳证明量身定制的强大原理。它在一个
通用宇宙 `X` 上进行良基归纳，但其核心的变换和规约逻辑只作用于
一个指定的子类型 `SubX`。

这个定理完美地捕捉了我们在矩阵分解中遇到的模式：我们在所有矩阵
的宇宙中进行归纳，但只对“正维度矩阵”这个子集应用复杂的分解算法。

参数:
*   `X`: 归纳所在的通用宇宙类型。
*   `SubX`: `X` 的一个子类型，代表我们真正关心、需要进行复杂处理的对象集合。
*   `μ`: 定义在整个宇宙 `X` 上的度量函数。
*   `μ_base`: 归纳基例的度量边界。
*   `P`: 要在整个宇宙 `X` 上证明的性质。
*   `P_sub`: `P` 在子类型 `SubX` 上的“版本”。
*   `P_compat`: 保证 `P` 和 `P_sub` 在子类型上是等价的。
*   `r_sub`: 只在 `SubX` 的成员之间定义的变换关系。
*   `IsSliceable_sub`: 只为 `SubX` 的成员定义的可切片谓词。
*   `slice_sub`: 从 `SubX` 的可切片成员中提取一个（可能在 `X` 中的）子问题。
*   `transport_sub`, `lift_from_slice_sub`, `reach_sub`:
    所有核心的归纳步骤引理，都只在 `SubX` 上下文中定义和证明。
*   `base_univ`: 为宇宙 `X` 中**不属于** `SubX` 的所有对象，或度量 `≤ μ_base` 的对象
    提供一个统一的基例证明。
-/
theorem induction_on_subtype
    (SubX : Type*) (toX : SubX → X) -- 新增：显式的转换函数
    (μ : X → Nat) (μ_base : Nat)
    (P : X → Prop)
    (P_sub : SubX → Prop)
    (P_compat : ∀ (x_sub : SubX), P_sub x_sub ↔ P (toX x_sub)) -- 修改：使用 toX
    (r_sub : SubX → SubX → Prop)
    (IsSliceable_sub : SubX → Prop)
    (slice_sub : ∀ (x_sub : SubX), IsSliceable_sub x_sub → X)
    (transport_sub : Transport r_sub P_sub)
    (lift_from_slice_sub : ∀ (x_sub : SubX) (hx : IsSliceable_sub x_sub),
                           P (slice_sub x_sub hx) → P_sub x_sub)
    (reach_sub : ∀ (x_sub : SubX), μ (toX x_sub) > μ_base → -- 修改：使用 toX
                 Σ' (y_sub : SubX), Σ' (hy : IsSliceable_sub y_sub),
                   r_sub y_sub x_sub ∧ μ (slice_sub y_sub hy) < μ (toX x_sub)) -- 修改：使用 toX
    (base_univ : ∀ (x : X), (∀ (x_sub : SubX), toX x_sub ≠ x) ∨ μ x ≤ μ_base → P x) -- 修改：使用 toX
    : ∀ (x : X), P x := by
  refine (WellFounded.fix (InvImage.wf μ wellFounded_lt) (C := fun _ => P _) ?_)
  intro x ih
  by_cases h_in_sub : ∃ (x_sub : SubX), toX x_sub = x -- 修改：使用 toX
  · rcases h_in_sub with ⟨x_sub, rfl⟩
    -- 目标现在是 P (toX x_sub)，通过在子类型上证明 P_sub x_sub 来实现
    have hP_sub : P_sub x_sub := by
      by_cases h_mu : μ (toX x_sub) > μ_base -- 修改：使用 toX
      · rcases reach_sub x_sub h_mu with ⟨y_sub, hy, h_r, h_prog⟩
        let slice_obj := slice_sub y_sub hy
        have h_slice_p : P slice_obj := ih slice_obj h_prog
        have h_y_p : P_sub y_sub := lift_from_slice_sub y_sub hy h_slice_p
        exact transport_sub _ _ h_r h_y_p
      · -- 子类型中的基例，直接由 base_univ 提供，再用兼容性转换
        have hP : P (toX x_sub) :=
          base_univ (toX x_sub) (Or.inr (le_of_not_gt h_mu))
        exact (P_compat x_sub).2 hP
    exact (P_compat x_sub).1 hP_sub
  · -- 宇宙中的基例
    -- 将 `¬ ∃ x_sub, toX x_sub = x` 转换为需要的全称形式
    have h_forall : ∀ (x_sub : SubX), toX x_sub ≠ x := by
      intro x_sub hx
      exact h_in_sub ⟨x_sub, hx⟩
    exact base_univ x (Or.inl h_forall)

variable {α : Type*}
/--
`induction_on_subtype` (generalized version):

This is the same “subtype-driven” induction principle as before, but generalized from
`μ : X → Nat` (with `<`) to an arbitrary measure type `α` equipped with a well-founded
relation `relα`.

You also provide a base predicate `BaseSet : X → Prop` (replacing the old `μ x ≤ μ_base`).
-/
theorem induction_on_subtype'
    (SubX : Type*) (toX : SubX → X)
    (μ : X → α) (relα : α → α → Prop) (hwf : WellFounded relα)
    (P : X → Prop)
    (P_sub : SubX → Prop)
    (P_compat : ∀ (x_sub : SubX), P_sub x_sub ↔ P (toX x_sub))
    (r_sub : SubX → SubX → Prop)
    (IsSliceable_sub : SubX → Prop)
    (slice_sub : ∀ (x_sub : SubX), IsSliceable_sub x_sub → X)
    (transport_sub : ∀ {x_sub y_sub}, r_sub y_sub x_sub → P_sub y_sub → P_sub x_sub)
    (lift_from_slice_sub :
      ∀ (x_sub : SubX) (hx : IsSliceable_sub x_sub),
        P (slice_sub x_sub hx) → P_sub x_sub)
    (BaseSet : X → Prop)
    (reach_sub :
      ∀ (x_sub : SubX), ¬ BaseSet (toX x_sub) →
        Σ' (y_sub : SubX), Σ' (hy : IsSliceable_sub y_sub),
          r_sub y_sub x_sub ∧ relα (μ (slice_sub y_sub hy)) (μ (toX x_sub)))
    (base_univ :
      ∀ (x : X), (∀ (x_sub : SubX), toX x_sub ≠ x) ∨ BaseSet x → P x)
    : ∀ (x : X), P x := by
  classical
  -- Well-founded recursion on the inv-image relation `InvImage relα μ` on `X`.
  refine
    (WellFounded.fix (InvImage.wf (f := μ) hwf) (C := fun _ => P _) ?_)
  intro x ih

  by_cases h_in_sub : ∃ (x_sub : SubX), toX x_sub = x
  · rcases h_in_sub with ⟨x_sub, rfl⟩

    have hP_sub : P_sub x_sub := by
      by_cases h_base : BaseSet (toX x_sub)
      · -- Subtype base case: use `base_univ`, then convert via `P_compat`.
        have hP : P (toX x_sub) := base_univ (toX x_sub) (Or.inr h_base)
        exact (P_compat x_sub).2 hP
      · -- Non-base: use `reach_sub`, then recurse on the slice (strict progress in `relα`).
        rcases reach_sub x_sub h_base with ⟨y_sub, hy, h_r, h_prog⟩
        let slice_obj := slice_sub y_sub hy
        have h_slice_p : P slice_obj := ih slice_obj h_prog
        have h_y_p : P_sub y_sub := lift_from_slice_sub y_sub hy h_slice_p
        exact transport_sub h_r h_y_p

    exact (P_compat x_sub).1 hP_sub
  · -- Universe base case: not in the subtype, so discharge with `base_univ`.
    have h_forall : ∀ (x_sub : SubX), toX x_sub ≠ x := by
      intro x_sub hx
      exact h_in_sub ⟨x_sub, hx⟩
    exact base_univ x (Or.inl h_forall)

end MatDecompFormal.Framework












-- import Mathlib
-- import MatDecompFormal.Abstractions.Strategy
-- import Mathlib.Data.FinEnum


-- namespace MatDecompFormal.Framework
-- open MatDecompFormal.Abstractions
-- open FinEnum

-- /-!
-- # 通用归纳框架 (The General Induction Framework)

-- 本文件定义了整个形式化项目的核心归纳原理。这些定理是通用的，
-- 不依赖于矩阵或任何具体的代数结构。它们形成了一个三层结构：

-- 1.  **`induction_by_reduction` (引擎)**:
--     最底层的、统一的归纳原理。它将证明任务分解为处理一个明确指定的
--     “基例集合” (`BaseSet`) 和一个“规约步骤”。

-- 2.  **`wellFounded_induction_via_reduction` (通用API)**:
--     `induction_by_reduction` 的一个便利封装，用于处理一个常见的场景：
--     当基例就是归纳关系下的“最小元”集合时。

-- 3.  **`transformSliceInduction` (领域特定API)**:
--     另一个便利封装，专门为本项目设计，用于处理当归纳基于一个自然数
--     度量 `μ`，且基例是“度量为0”的集合时。

-- 这个分层结构兼顾了理论的完备性、通用性和实践的便利性。
-- -/

-- variable {X : Type*}

-- /--
-- `Transport r P` 叙述了命题 `P` 可以在变换 `r` 下“传递”。
-- -/
-- def Transport (r : X → X → Prop) (P : X → Prop) : Prop :=
--   ∀ (x y : X), r x y → P x → P y

-- -- ==================================================================
-- -- L0: THE CORE ENGINE
-- -- ==================================================================

-- /--
-- `induction_by_reduction` 是本框架最核心的、统一的归纳原理。

-- 它将证明 `∀ x, P x` 的任务分解为处理“基例” (`BaseSet`) 和“非基例”两种情况。
-- 对于非基例，它要求我们能够通过变换和规约，将其化为一个“更小”的问题。
-- -/
-- theorem induction_by_reduction
--     {rel : X → X → Prop} (hwf : WellFounded rel)
--     (BaseSet : X → Prop)
--     {r : X → X → Prop} {P : X → Prop}
--     (h_trans : Transport r P)
--     (IsReducible : X → Prop)
--     (decompose : ∀ {x : X}, IsReducible x → X)
--     (reconstruct : ∀ {x : X} (hx : IsReducible x), P (decompose hx) → P x)
--     (prove_on_base : ∀ {x : X}, BaseSet x → P x)
--     (reach_from_non_base : ∀ {x : X}, ¬ BaseSet x →
--       ∃ y, ∃ (hy : IsReducible y), r y x ∧ rel (decompose hy) x)
--     : ∀ (x : X), P x := by
--   intro x_to_prove
--   apply hwf.induction x_to_prove
--   clear x_to_prove
--   intro x ih
--   by_cases h_is_base : BaseSet x
--   · exact prove_on_base h_is_base
--   · rcases reach_from_non_base h_is_base with ⟨y, hy, h_r_yx, h_rel_decompose⟩
--     have p_decompose : P (decompose hy) := ih (decompose hy) h_rel_decompose
--     have p_y : P y := reconstruct hy p_decompose
--     exact h_trans y x h_r_yx p_y

-- -- ==================================================================
-- -- L1: CONVENIENCE APIS (Corollaries of the Core Engine)
-- -- ==================================================================

-- /--
-- `wellFounded_induction_via_reduction` 是 `induction_by_reduction` 的一个实例，
-- 专门用于基例是“最小元”集合 (`¬ ∃ y, rel y x`) 的常见情况。
-- -/
-- theorem wellFounded_induction_via_reduction
--     {rel : X → X → Prop} (hwf : WellFounded rel)
--     {r : X → X → Prop} {P : X → Prop}
--     (h_trans : Transport r P)
--     (IsReducible : X → Prop)
--     (decompose : ∀ {x : X}, IsReducible x → X)
--     (reconstruct : ∀ {x : X} (hx : IsReducible x), P (decompose hx) → P x)
--     (reachability : ∀ {x : X}, (∃ y, rel y x) →
--       ∃ y, ∃ (hy : IsReducible y), r y x ∧ rel (decompose hy) x)
--     (base_case : ∀ {x : X}, (¬ ∃ y, rel y x) → P x)
--     : ∀ (x : X), P x := by
--   -- 通过将 BaseSet 定义为最小元集合，直接调用核心引擎来证明。
--   apply induction_by_reduction hwf
--     (BaseSet := fun x ↦ ¬ ∃ y, rel y x)
--     h_trans IsReducible decompose reconstruct
--     (prove_on_base := base_case)
--     (reach_from_non_base := by
--       -- `¬ (¬ ∃ y, rel y x)` 等价于 `∃ y, rel y x`
--       intro x h_non_minimal
--       push_neg at h_non_minimal
--       exact reachability h_non_minimal)

-- /--
-- `transformSliceInduction` 是 `induction_by_reduction` 的另一个实例，
-- 专门为使用自然数度量 `μ`，且基例是“度量为0”的集合的情况设计。
-- 这是本项目中最常用的归纳工具。
-- -/
-- theorem transformSliceInduction
--     (μ : X → Nat)
--     {r : X → X → Prop} {P : X → Prop}
--     (h_trans : Transport r P)
--     (IsSliceable : X → Prop)
--     (slice : ∀ {x : X}, IsSliceable x → X)
--     (lift_from_slice : ∀ {x : X} (hx : IsSliceable x), P (slice hx) → P x)
--     (reach_metric : ∀ {x : X}, μ x > 0 → ∃ y, ∃ (hy : IsSliceable y), r y x ∧ μ (slice hy) < μ x)
--     (base_metric : ∀ {x : X}, μ x = 0 → P x)
--     : ∀ (x : X), P x := by
--   -- 通过将 BaseSet 定义为度量为0的集合，直接调用核心引擎来证明。
--   apply induction_by_reduction (WellFounded.onFun wellFounded_lt)
--     (BaseSet := fun x ↦ μ x = 0)
--     h_trans IsSliceable slice lift_from_slice
--     (prove_on_base := base_metric)
--     (reach_from_non_base := by
--       -- `¬ (μ x = 0)` 等价于 `μ x ≠ 0`，对于自然数，这等价于 `μ x > 0`。
--       intro x h_non_base
--       have h_mu_pos : μ x > 0 := Nat.pos_of_ne_zero h_non_base
--       exact reach_metric h_mu_pos)

-- end MatDecompFormal.Framework
