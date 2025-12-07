import MatDecompFormal.Components.Transformations.Elementary.AnnihilateColumn
import MatDecompFormal.Components.Transformations.Elementary.AnnihilateRow

namespace MatDecompFormal.Components.Transformations.Composed

open MatDecompFormal.Abstractions MatDecompFormal.Components.Transformations.Elementary

/-!
# 双对角化步骤变换 (Bidiagonalization Step Transformation)

本文件定义了 `BidiagStepTransform`，这是一个宏观的、组合而成的 `Transformation`
实例。它代表了双对角化算法中一个完整的归纳步骤：

1.  **首先**，通过左乘一个变换（如 Householder），消去主元所在列下方的所有元素。
2.  **然后**，通过右乘另一个变换，消去主元所在行右方的所有元素（通常会保留超对角线元素）。

这个宏观步骤是通过 `Transformation.compose_sequential` 将
`AnnihilateColumnTransform` 和 `AnnihilateRowTransform` 组合而成的。

### 设计选择：`compose_sequential`
我们选择使用 `compose_sequential` 而不是 `compose`，因为它更加灵活和健壮。
`compose_sequential` 会检查每一步的目标是否已经达成：
- 如果第一列已经被消元，它会跳过列消元步骤。
- 如果应用列消元后，第一行恰好也被消元了，它会跳过行消元步骤。
这种行为不仅正确地模拟了算法的逻辑，而且避免了为 `compose` 提供复杂的、
在所有情况下都成立的逻辑前提 (`h_precond`, `h_preserves`)。

这个组件完美地展示了如何通过组合基本的、可复用的“变换积木”来构建
更复杂的算法步骤。
-/

section BidiagStepTransform

-- 声明所有定义共享的类型和类型类实例。
variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Field R] [DecidableEq R]

/--
`BidiagStepTransform` 将列消元和行消元组合成一个单一的变换步骤。

*   `i₀`, `j₀`: 主元的行和列索引。
*   `h_col_pivot_nz`: `AnnihilateColumnTransform` 所需的前提，保证在需要时主元非零。
*   `h_row_pivot_nz`: `AnnihilateRowTransform` 所需的前提，保证在需要时主元非零。
-/
noncomputable def BidiagStepTransform (i₀ : ι) (j₀ : κ)
    (h_col_pivot_nz : ∀ (A : Matrix ι κ R), (∃ i, i ≠ i₀ ∧ A i j₀ ≠ 0) → A i₀ j₀ ≠ 0)
    (h_row_pivot_nz : ∀ (A : Matrix ι κ R), (∃ j, j ≠ j₀ ∧ A i₀ j ≠ 0) → A i₀ j₀ ≠ 0) :
    Transformation (Matrix ι κ R) :=
  -- 使用 `compose_sequential` 将两个基本变换组合起来。
  -- 变换 T₁ 是列消元。
  -- 变换 T₂ 是行消元。
  -- 最终的 `Goal` 是 T₂ 的 `Goal`，即行被成功消元。
  Transformation.compose_sequential
    (AnnihilateColumnTransform i₀ j₀ h_col_pivot_nz)
    (AnnihilateRowTransform i₀ j₀ h_row_pivot_nz)

end BidiagStepTransform

end MatDecompFormal.Components.Transformations.Composed
