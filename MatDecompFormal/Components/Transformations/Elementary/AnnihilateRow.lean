import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import MatDecompFormal.Abstractions.Transformation

namespace MatDecompFormal.Components.Transformations.Elementary

open Matrix

/-!
# 行消元变换 (Row Annihilation Transformation)

本文件定义了 `AnnihilateRowTransform`，这是一个在 `Fin n` 世界中实现的
`Transformation` 实例，其目标是通过右乘高斯变换将矩阵第一行主元之右的所有元素变为零。
-/

section GaussUtilsRight

variable {n m : ℕ} {R : Type*} [Fintype (Fin m)] [DecidableEq (Fin m)] [Field R]
variable [NeZero m]

def gaussTransRight (l : Fin m → R) : Matrix (Fin m) (Fin m) R :=
  1 - vecMulVec (Pi.single 0 1) l

def gaussTransRightGL (l : Fin m → R) (hl : l 0 = 0) : GL (Fin m) R where
  val := gaussTransRight l
  inv := 1 + vecMulVec (Pi.single 0 1) l
  val_inv := by simp [gaussTransRight, mul_add, mul_one, sub_mul, one_mul,
                      vecMulVec_mul_vecMulVec, hl, zero_smul, sub_zero, sub_add_cancel]
  inv_val := by simp [gaussTransRight, mul_sub, mul_one, add_mul, one_mul,
                      vecMulVec_mul_vecMulVec, hl, zero_smul, add_zero, add_sub_cancel_right]

lemma mul_gaussTransRight_apply (A : Matrix (Fin n) (Fin m) R)
    (l : Fin m → R) (i : Fin n) (j : Fin m) :
    (A * gaussTransRight l) i j = A i j - A i 0 * l j := by
  simp [gaussTransRight]
  rw [Matrix.mul_sub, Matrix.mul_one, mul_vecMulVec]
  simp [vecMulVec]

end GaussUtilsRight

/--
`AnnihilateRowTransform` 是一个 `Transformation` 实例，它通过右乘高斯变换
来消去第一行中主元 `A 0 0` 之右的所有元素。

*   `h_pivot_nz`: 一个关键的前提假设，断言如果第一行有非零元需要被消去，
    那么主元 `A 0 0` 必须是非零的。
-/
noncomputable def AnnihilateRowTransform (n m : ℕ) (R : Type*) [NeZero n] [NeZero m]
    [Field R] [DecidableEq R]
    (h_pivot_nz : ∀ (A : Matrix (Fin n) (Fin m) R), (∃ j, j ≠ 0 ∧ A 0 j ≠ 0) → A 0 0 ≠ 0) :
    Abstractions.Transformation (Matrix (Fin n) (Fin m) R) where
  T := Fin m → R
  Goal := fun A ↦ ∀ j, j ≠ 0 → A 0 j = 0
  decGoal := by infer_instance
  apply := fun l A ↦ A * gaussTransRight l
  find := fun A h_goal_not_met ↦
    let h_exists_nonzero := by push_neg at h_goal_not_met; exact h_goal_not_met
    let pivot_nz := h_pivot_nz A h_exists_nonzero
    fun j ↦ if j = 0 then 0 else A 0 j / A 0 0
  find_spec := by
    intro A h_goal_not_met
    dsimp only; intro j hj_ne_zero
    let h_exists_nonzero := by push_neg at h_goal_not_met; exact h_goal_not_met
    let pivot_nz := h_pivot_nz A h_exists_nonzero
    let l := fun j' ↦ if j' = 0 then 0 else A 0 j' / A 0 0
    rw [mul_gaussTransRight_apply A l 0 j]
    have l_j_def : l j = A 0 j / A 0 0 := by simp [l, hj_ne_zero]
    rw [l_j_def]
    field_simp [pivot_nz]; rw [sub_self, mul_zero]

end MatDecompFormal.Components.Transformations.Elementary







-- import Mathlib.Data.FinEnum
-- import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
-- import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
-- import MatDecompFormal.Abstractions.Transformation

-- namespace MatDecompFormal.Components.Transformations.Elementary

-- open Matrix FinEnum

-- /-!
-- # 行消元变换 (Row Annihilation Transformation)

-- 本文件定义了 `AnnihilateRowTransform`，这是一个 `Transformation` 的具体实例，
-- 其目标是通过列变换，将矩阵特定行中主元之外的所有元素变为零。

-- 这是通过高斯消元（右乘一个初等矩阵）来实现的。这个组件封装了“构造一个
-- 合适的消元矩阵并应用它”这一核心算法步骤，是双对角化等算法的基石。

-- ### 工作原理
-- 1.  **目标 (`Goal`)**: `fun A ↦ ∀ j, j ≠ j₀ → A i₀ j = 0`，即在 `i₀` 行，
--     除了主元列 `j₀` 之外的所有元素都为零。
-- 2.  **变换类型 (`T`)**: `κ → R`。一个变换由一个“消元向量” `l` 唯一定义。
-- 3.  **应用 (`apply`)**: `fun l A ↦ A * (gaussTransRight j₀ l)`。通过右乘一个
--     高斯变换矩阵 `F = I - eⱼ₀ ⊗ lᵀ` 来实现。
-- 4.  **查找 (`find`)**: 当 `A` 的 `i₀` 行尚未被消元时，`find` 负责构造
--     正确的消元向量 `l`，其定义为 `lⱼ = Aᵢ₀ⱼ / Aᵢ₀ⱼ₀` (当 `j ≠ j₀`)。
--     - **重要**: `find` 的能力依赖于一个前提 `h_pivot_nz`，即调用者必须保证
--       如果该行有非零元需要被消去，那么主元 `A i₀ j₀` 自身必须是非零的。

-- 这个组件将算法的“行消元”逻辑与归纳证明的其余部分完全解耦。
-- -/

-- section GaussUtilsRight

-- -- 声明所有定义共享的类型和类型类实例。
-- variable {ι κ R : Type*} [Fintype κ] [DecidableEq κ] [Field R]

-- /--
-- `gaussTransRight j₀ l` - 用于右乘的高斯变换矩阵 `F = I - eⱼ₀ ⊗ lᵀ`。

-- 右乘 `gaussTransRight j₀ l` 于矩阵 `A` 的效果是：对于每一列 `j`，
-- 从 `A` 的第 `j` 列中减去 `lⱼ` 倍的第 `j₀` 列。
-- -/
-- def gaussTransRight (j₀ : κ) (l : κ → R) : Matrix κ κ R :=
--   1 - vecMulVec (Pi.single j₀ 1) l

-- /--
-- 用于右乘的高斯变换矩阵是可逆的（属于 `GL κ R`），只要 `l j₀ = 0`。
-- -/
-- def gaussTransRightGL (j₀ : κ) (l : κ → R) (hl : l j₀ = 0) : GL κ R where
--   val := gaussTransRight j₀ l
--   inv := 1 + vecMulVec (Pi.single j₀ 1) l
--   val_inv := by
--     -- 证明与左乘版本对称
--     simp [gaussTransRight, mul_add, mul_one, sub_mul, one_mul, vecMulVec_mul_vecMulVec,
--       hl, zero_smul, sub_zero, sub_add_cancel]
--   inv_val := by
--     simp [gaussTransRight, mul_sub, mul_one, add_mul, one_mul, vecMulVec_mul_vecMulVec,
--       hl, zero_smul, add_zero, add_sub_cancel_right]

-- /--
-- 右乘高斯变换的核心性质：应用变换后，目标行的元素被正确地修改。
-- `(A * F)ᵢ₀ⱼ = Aᵢ₀ⱼ - Aᵢ₀ⱼ₀ * lⱼ`
-- -/
-- lemma mul_gaussTransRight_apply (A : Matrix ι κ R) (j₀ : κ) (l : κ → R) (i₀ : ι) (j : κ) :
--     (A * gaussTransRight j₀ l) i₀ j = A i₀ j - A i₀ j₀ * l j := by
--   simp [gaussTransRight]
--   rw [Matrix.mul_sub, Matrix.mul_one, mul_vecMulVec]
--   simp [vecMulVec]

-- end GaussUtilsRight


-- section AnnihilateRowTransform

-- variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Field R] [DecidableEq R]

-- /--
-- `AnnihilateRowTransform` 是一个 `Transformation` 实例，它通过右乘高斯变换
-- 来消去主元 `(i₀, j₀)` 所在行的其他所有元素。

-- *   `i₀`, `j₀`: 主元的行和列索引。
-- *   `h_pivot_nz`: 一个关键的前提假设。它断言：如果 `i₀` 行中存在需要被
--     消元的非零元素（即 `Goal` 不成立），那么主元 `A i₀ j₀` 必须是非零的。
-- -/
-- noncomputable def AnnihilateRowTransform (i₀ : ι) (j₀ : κ)
--     (h_pivot_nz : ∀ (A : Matrix ι κ R), (∃ j, j ≠ j₀ ∧ A i₀ j ≠ 0) → A i₀ j₀ ≠ 0) :
--     Abstractions.Transformation (Matrix ι κ R) where
--   -- 变换参数的类型是消元向量 `l`，其索引为列索引 `κ`。
--   T := κ → R
--   -- 目标：`i₀` 行中，所有不在 `j₀` 列的元素都为零。
--   Goal := fun A ↦ ∀ j, j ≠ j₀ → A i₀ j = 0
--   -- `Field` 和 `DecidableEq` 保证了 `Goal` 是可判定的。
--   decGoal := by infer_instance
--   -- 应用变换：右乘一个高斯变换矩阵。
--   apply := fun l A ↦ A * gaussTransRight j₀ l
--   -- 查找变换：当目标未达成时，构造消元向量 `l`。
--   find := fun A h_goal_not_met ↦
--     -- `h_goal_not_met` 是 `¬ (∀ j, j ≠ j₀ → A i₀ j = 0)`。
--     -- `push_neg` 将其转换为 `∃ j, j ≠ j₀ ∧ A i₀ j ≠ 0`。
--     let h_exists_nonzero := by push_neg at h_goal_not_met; exact h_goal_not_met
--     -- 利用前提 `h_pivot_nz` 得到主元非零的证明。
--     let pivot_nz := h_pivot_nz A h_exists_nonzero
--     -- 构造消元向量 `l`。
--     fun j ↦ if j = j₀ then 0 else A i₀ j / A i₀ j₀
--   -- 正确性证明：证明 `find` 构造的 `l` 在应用后确实能达成 `Goal`。
--   find_spec := by
--     intro A h_goal_not_met
--     -- 展开 `Goal` 的定义
--     dsimp only
--     -- 目标：对任意 `j ≠ j₀`，证明变换后 `(apply ... A) i₀ j = 0`。
--     intro j hj_ne_j₀
--     -- 获取 `find` 构造的 `l` 和主元非零的证明。
--     let h_exists_nonzero := by push_neg at h_goal_not_met; exact h_goal_not_met
--     let pivot_nz := h_pivot_nz A h_exists_nonzero
--     let l := fun j' ↦ if j' = j₀ then 0 else A i₀ j' / A i₀ j₀
--     -- 使用 `mul_gaussTransRight_apply` 引理来计算变换后的元素值。
--     rw [mul_gaussTransRight_apply A j₀ l i₀ j]
--     -- `l j` 的值是什么？因为 `hj_ne_j₀`，`if` 条件为假。
--     have l_j_def : l j = A i₀ j / A i₀ j₀ := by simp [l, hj_ne_j₀]
--     rw [l_j_def]
--     -- 目标化为 `A i₀ j - A i₀ j₀ * (A i₀ j / A i₀ j₀) = 0`。
--     field_simp
--     rw [sub_self, mul_zero]

-- end AnnihilateRowTransform

-- end MatDecompFormal.Components.Transformations.Elementary
