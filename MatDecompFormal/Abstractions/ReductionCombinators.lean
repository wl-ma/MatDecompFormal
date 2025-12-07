import MatDecompFormal.Abstractions.ReductionMethod

namespace MatDecompFormal.Abstractions

/-!
# 规约方法组合子 (Reduction Method Combinators)

本文件定义了用于组合 `ReductionMethod` 实例的“高阶函数”，即组合子。
这些组合子允许我们从简单的、模块化的规约方法（如 `SchurMethod` 或
`SubmatrixMethod`）以声明式的方式构建出更复杂的、带有控制流的规约策略。

这体现了本框架的一个核心设计原则：将复杂的算法逻辑分解为可组合的、
纯粹的代数组件。

### 核心组合子：`try_else`
本文件目前定义了最重要的组合子 `ReductionMethod.try_else`。它实现了
一个“尝试-回退” (try-fallback) 的逻辑：
- **尝试** 应用第一个规约方法 `M₁`。
- 如果 `M₁` 的 `IsSliceable` 条件不满足，则**回退**到应用第二个方法 `M₂`。

这个组合子是构造 `PLU` 分解通用策略的关键，因为它精确地模拟了 `PLU`
算法的逻辑：尝试进行主元消元，如果不行（因为主元为零），则检查一个
更弱的条件（整列为零）并采取不同的规约步骤。
-/


/--
`ReductionMethod.try_else` 是一个组合子，它将两个规约方法 `M₁` 和 `M₂`
合并为一个新的、带有回退逻辑的规约方法。

### 类型兼容性
一个关键的挑战是 `M₁` 和 `M₂` 可能会产生不同类型 (`Type*`) 的“切片”。
例如，一个方法可能切出 `Fin (n-1)` 的子矩阵，另一个可能切出 `Fin (n-2)`。
为了使组合后的 `slice` 和 `reconstruct` 函数具有统一的返回类型，我们
必须要求 `M₁` 和 `M₂` 的切片类型在定义上是相等的。

*   `M₁`, `M₂`: 要组合的两个规约方法。
*   `h_slice_ι_eq`, `h_slice_κ_eq`: **关键前提**。这两个等式证明了 `M₁` 和 `M₂`
    产生的切片具有完全相同的行和列索引类型。在实践中，例如对于 `PLU`，
    两个分支都规约到 `n-1` 维的子问题，因此这个证明通常是 `rfl`。
-/
noncomputable def ReductionMethod.try_else {ι κ R : Type*}
    [FinEnum ι] [FinEnum κ] [CommRing R]
    (M₁ M₂ : ReductionMethod ι κ R)
    (h_slice_ι_eq : M₁.Sliceι = M₂.Sliceι)
    (h_slice_κ_eq : M₁.Sliceκ = M₂.Sliceκ)
    : ReductionMethod ι κ R where
  -- 1. 定义新方法的切片类型和 FinEnum 实例
  --    由于我们要求类型相等，所以可以直接采用 M₁ 的类型。
  Sliceι := M₁.Sliceι
  Sliceκ := M₁.Sliceκ
  finEnum_slice_ι := M₁.finEnum_slice_ι
  finEnum_slice_κ := M₁.finEnum_slice_κ

  -- 2. 新的 IsSliceable 条件是两者的析取（或）。
  IsSliceable := fun A ↦ M₁.IsSliceable A ∨ M₂.IsSliceable A

  -- 3. 新的 slice 操作带有分支逻辑。
  slice := by
    intro A hA
    by_cases h₁ : M₁.IsSliceable A
    · exact M₁.slice A h₁
    · let h₂ : M₂.IsSliceable A := hA.resolve_left h₁
      rw [h_slice_ι_eq, h_slice_κ_eq]
      exact M₂.slice A h₂

  -- 4. 新的 reconstruct 操作同样带有分支逻辑。
  reconstruct := by
    intro A hA slice_sol
    by_cases h₁ : M₁.IsSliceable A
    · exact M₁.reconstruct A h₁ slice_sol
    · let h₂ : M₂.IsSliceable A := hA.resolve_left h₁
      rw [h_slice_ι_eq, h_slice_κ_eq] at slice_sol
      exact M₂.reconstruct A h₂ slice_sol

  -- 5. 正确性证明也需要分情况讨论。
  reconstruct_slice_eq := by
    intro A hA
    dsimp only
    split_ifs with h₁
    · exact M₁.reconstruct_slice_eq A h₁
    · simp
      exact M₂.reconstruct_slice_eq A (hA.resolve_left h₁)

end MatDecompFormal.Abstractions
