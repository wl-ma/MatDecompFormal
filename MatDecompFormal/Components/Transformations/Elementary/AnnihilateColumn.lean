import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import MatDecompFormal.Abstractions.Transformation

namespace MatDecompFormal.Components.Transformations.Elementary

open Matrix FinEnum

/-!
# 列消元变换 (Column Annihilation Transformation)

本文件定义了 `AnnihilateColumnTransform`，这是一个 `Transformation` 的具体实例，
其目标是通过行变换，将矩阵特定列中主元之外的所有元素变为零。

这是通过高斯消元（左乘一个初等矩阵）来实现的。这个组件封装了“构造一个
合适的消元矩阵并应用它”这一核心算法步骤，是 QR 分解、Hessenberg 分解等
算法的基石。

### 工作原理
1.  **目标 (`Goal`)**: `fun A ↦ ∀ i, i ≠ i₀ → A i j₀ = 0`，即在 `j₀` 列，
    除了主元行 `i₀` 之外的所有元素都为零。
2.  **变换类型 (`T`)**: `ι → R`。一个变换由一个“消元向量” `l` 唯一定义。
3.  **应用 (`apply`)**: `fun l A ↦ (gaussTrans i₀ l) * A`。通过左乘一个
    高斯变换矩阵 `E = I - l ⊗ eᵢ₀ᵀ` 来实现。
4.  **查找 (`find`)**: 当 `A` 的 `j₀` 列尚未被消元时，`find` 负责构造
    正确的消元向量 `l`，其定义为 `lᵢ = Aᵢⱼ₀ / Aᵢ₀ⱼ₀` (当 `i ≠ i₀`)。
    - **重要**: `find` 的能力依赖于一个前提 `h_pivot_nz`，即调用者必须保证
      如果该列有非零元需要被消去，那么主元 `A i₀ j₀` 自身必须是非零的。

这个组件将算法的“列消元”逻辑与归纳证明的其余部分完全解耦。
-/

section GaussUtils

-- 声明所有定义共享的类型和类型类实例。
-- 我们需要一个域 `Field`，因为消元操作需要除法。
variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Field R]

/--
`gaussTrans i₀ l` - 高斯变换矩阵 `E = I - l ⊗ eᵢ₀ᵀ`。

左乘 `gaussTrans i₀ l` 于矩阵 `A` 的效果是：对于每一行 `i`，
从 `A` 的第 `i` 行中减去 `lᵢ` 倍的第 `i₀` 行。
-/
def gaussTrans (i₀ : ι) (l : ι → R) : Matrix ι ι R :=
  1 - vecMulVec l (Pi.single i₀ 1)

/--
高斯变换矩阵是可逆的（属于 `GL ι R`），只要 `l i₀ = 0`。
这个条件确保了对角线上没有零，保证了矩阵的非奇异性。
-/
def gaussTransGL (i₀ : ι) (l : ι → R) (hl : l i₀ = 0) : GL ι R where
  val := gaussTrans i₀ l
  inv := 1 + vecMulVec l (Pi.single i₀ 1)
  val_inv := by
    -- 这个证明直接从你的草稿中迁移而来，并适用于通用的 Fintype ι
    simp [gaussTrans, mul_add, mul_one, sub_mul, one_mul, vecMulVec_mul_vecMulVec,
      single_dotProduct, hl, mul_zero, zero_smul, sub_zero, sub_add_cancel]
  inv_val := by
    simp [gaussTrans, mul_sub, mul_one, add_mul, one_mul, vecMulVec_mul_vecMulVec,
      single_dotProduct, hl, mul_zero, zero_smul, add_zero, add_sub_cancel_right]

/--
高斯变换的核心性质：应用变换后，目标列的元素被正确地修改。
`(E * A)ᵢⱼ₀ = Aᵢⱼ₀ - lᵢ * Aᵢ₀ⱼ₀`
-/
lemma gaussTrans_mul_apply (A : Matrix ι κ R) (i₀ : ι) (l : ι → R) (i : ι) (j₀ : κ) :
    (gaussTrans i₀ l * A) i j₀ = A i j₀ - l i * A i₀ j₀ := by
  simp [gaussTrans]
  rw [Matrix.sub_mul, Matrix.one_mul, vecMulVec_mul]
  simp [vecMulVec, mul_comm]

end GaussUtils


section AnnihilateColumnTransform

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Field R] [DecidableEq R]

/--
`AnnihilateColumnTransform` 是一个 `Transformation` 实例，它通过高斯变换
来消去主元 `(i₀, j₀)` 所在列的其他所有元素。

*   `i₀`, `j₀`: 主元的行和列索引。
*   `h_pivot_nz`: 一个关键的前提假设。它断言：如果 `j₀` 列中存在需要被
    消元的非零元素（即 `Goal` 不成立），那么主元 `A i₀ j₀` 必须是非零的。
    这个假设的证明由使用此变换的具体分解算法（如 QR）来提供。
-/
noncomputable def AnnihilateColumnTransform (i₀ : ι) (j₀ : κ)
    (h_pivot_nz : ∀ (A : Matrix ι κ R), (∃ i, i ≠ i₀ ∧ A i j₀ ≠ 0) → A i₀ j₀ ≠ 0) :
    Abstractions.Transformation (Matrix ι κ R) where
  -- 变换参数的类型是消元向量 `l`。
  T := ι → R
  -- 目标：`j₀` 列中，所有不在 `i₀` 行的元素都为零。
  Goal := fun A ↦ ∀ i, i ≠ i₀ → A i j₀ = 0
  -- `Field` 和 `DecidableEq` 保证了 `Goal` 是可判定的。
  decGoal := by infer_instance
  -- 应用变换：左乘一个高斯变换矩阵。
  apply := fun l A ↦ gaussTrans i₀ l * A
  -- 查找变换：当目标未达成时，构造消元向量 `l`。
  find := fun A h_goal_not_met ↦
    -- `h_goal_not_met` 是 `¬ (∀ i, i ≠ i₀ → A i j₀ = 0)`。
    -- `push_neg` 将其转换为 `∃ i, i ≠ i₀ ∧ A i j₀ ≠ 0`。
    let h_exists_nonzero := by push_neg at h_goal_not_met; exact h_goal_not_met
    -- 利用前提 `h_pivot_nz` 得到主元非零的证明。
    let pivot_nz := h_pivot_nz A h_exists_nonzero
    -- 构造消元向量 `l`。
    fun i ↦ if i = i₀ then 0 else A i j₀ / A i₀ j₀
  -- 正确性证明：证明 `find` 构造的 `l` 在应用后确实能达成 `Goal`。
  find_spec := by
    intro A h_goal_not_met
    -- 展开 `Goal` 的定义
    dsimp only
    -- 目标：对任意 `i ≠ i₀`，证明变换后 `(apply ... A) i j₀ = 0`。
    intro i hi_ne_i₀
    -- 获取 `find` 构造的 `l` 和主元非零的证明。
    let h_exists_nonzero := by push_neg at h_goal_not_met; exact h_goal_not_met
    let pivot_nz := h_pivot_nz A h_exists_nonzero
    let l := fun i' ↦ if i' = i₀ then 0 else A i' j₀ / A i₀ j₀
    -- 使用 `gaussTrans_mul_apply` 引理来计算变换后的元素值。
    rw [gaussTrans_mul_apply A i₀ l i j₀]
    -- `l i` 的值是什么？因为 `hi_ne_i₀`，`if` 条件为假。
    have l_i_def : l i = A i j₀ / A i₀ j₀ := by simp [l, hi_ne_i₀]
    rw [l_i_def]
    -- 目标化为 `A i j₀ - (A i j₀ / A i₀ j₀) * A i₀ j₀ = 0`。
    field_simp
    rw [sub_self, mul_zero]

end AnnihilateColumnTransform

end MatDecompFormal.Components.Transformations.Elementary
