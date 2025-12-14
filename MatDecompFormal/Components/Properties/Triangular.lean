import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Sum.Order


namespace MatDecompFormal.Components.Properties

open Matrix

/-!
# 三角矩阵属性 (Triangular Matrix Properties)

本文件定义了上三角、下三角和单位下三角矩阵的属性。

设计要点：

* 定义仅依赖于索引类型上的 `LinearOrder`，**不依赖 `FinEnum`**。
* `IsUpperTriangular` 使用 `Matrix.BlockTriangular`，分块函数取恒等映射
  `fun i ↦ i`，因此条件等价于：若 `j < i` 则 `A i j = 0`。
* 对于一般 `FinEnum` 索引类型，可以通过 `Framework/FinEnum.lean` 中提供的
  规范 `LinearOrder` 实例来使用这些定义。
-/

section Triangular

variable {ι R : Type*} [Zero R] [LinearOrder ι]

/--
`IsUpperTriangular A`：矩阵 `A` 在给定索引顺序下是上三角矩阵。

形式上，它被定义为相对于恒等映射 `id : ι → ι` 的 `BlockTriangular`：
如果 `j < i`，则 `A i j = 0`。
-/
def IsUpperTriangular (A : Matrix ι ι R) : Prop :=
  BlockTriangular A (fun i : ι => i)

/--
`IsLowerTriangular A`：矩阵 `A` 是下三角矩阵，当且仅当 `Aᵀ` 是上三角矩阵。
-/
def IsLowerTriangular (A : Matrix ι ι R) : Prop :=
  IsUpperTriangular Aᵀ

/--
`IsUnitLowerTriangular A`：`A` 是一个单位下三角矩阵，
即下三角且主对角线全为 `1`。
-/
def IsUnitLowerTriangular [One R] (A : Matrix ι ι R) : Prop :=
  IsLowerTriangular A ∧ A.diag = 1

-- ==================================================================
-- Basic Properties
-- ==================================================================

variable [One R] [DecidableEq ι]

/-- 单位矩阵 `1` 是上三角矩阵。 -/
lemma isUpperTriangular_one : IsUpperTriangular (1 : Matrix ι ι R) := by
  -- `blockTriangular_one` 说明单位矩阵对任意分块函数都是 BlockTriangular
  dsimp [IsUpperTriangular]
  simpa using
    (blockTriangular_one (b := fun i : ι => i))

/-- 单位矩阵 `1` 是下三角矩阵。 -/
lemma isLowerTriangular_one : IsLowerTriangular (1 : Matrix ι ι R) := by
  dsimp [IsLowerTriangular]
  -- `(1 : Matrix _ _ _)ᵀ = 1`
  simpa [Matrix.transpose_one] using
    (isUpperTriangular_one (ι := ι) (R := R))

/-- 单位矩阵 `1` 是单位下三角矩阵。 -/
lemma isUnitLowerTriangular_one : IsUnitLowerTriangular (1 : Matrix ι ι R) := by
  constructor
  · exact isLowerTriangular_one (ι := ι) (R := R)
  · -- 对角线全为 1
    simp [Matrix.diag_one]

end Triangular


/-!
## `fromBlocks` 与单位下三角结构

这一小节提供一个专门面向块矩阵的引理：
如果右下角块是单位下三角的，那么
\[
  \begin{pmatrix}
    I & 0 \\
    L₂₁ & L'
  \end{pmatrix}
\]
整体仍然是单位下三角矩阵。
-/

section BlockFromBlocks

variable {n₁ n₂ : ℕ} {R : Type*} [CommRing R]

/-
把 `Fin n₁ ⊕ Fin n₂` 的序结构一次性集中在这里提供：
后面所有 “fromBlocks 保持三角性” 的 lemma 都直接用，不再到处补 instance。
-/
local instance instLESumLex : LE (Fin n₁ ⊕ Fin n₂) :=
  (inferInstance : LE ((Fin n₁) ⊕ₗ (Fin n₂)))

local instance instLTSumLex : LT (Fin n₁ ⊕ Fin n₂) :=
  (inferInstance : LT ((Fin n₁) ⊕ₗ (Fin n₂)))

local instance instPreorderSumLex : Preorder (Fin n₁ ⊕ Fin n₂) :=
  (inferInstance : Preorder ((Fin n₁) ⊕ₗ (Fin n₂)))

local instance instLinearOrderFinSum : LinearOrder (Fin n₁ ⊕ Fin n₂) :=
  (inferInstance : LinearOrder ((Fin n₁) ⊕ₗ (Fin n₂)))

/--
若对角块 `A₁₁` 和 `A₂₂` 都是上三角的，则 `fromBlocks A₁₁ A₁₂ 0 A₂₂`
（一个上块三角矩阵）也是上三角的。
-/
lemma isUpperTriangular_fromBlocks
    (A₁₁ : Matrix (Fin n₁) (Fin n₁) R) (A₁₂ : Matrix (Fin n₁) (Fin n₂) R)
    (A₂₂ : Matrix (Fin n₂) (Fin n₂) R)
    (hA₁₁ : IsUpperTriangular A₁₁) (hA₂₂ : IsUpperTriangular A₂₂) :
    IsUpperTriangular (fromBlocks A₁₁ A₁₂ 0 A₂₂ : Matrix (Fin n₁ ⊕ Fin n₂)
      (Fin n₁ ⊕ Fin n₂) R) := by
  classical
  -- The definition of IsUpperTriangular is `BlockTriangular _ id`.
  -- We use the definition of `BlockTriangular` for sum types.
  dsimp [IsUpperTriangular]
  -- Goal: `BlockTriangular (fromBlocks A₁₁ A₁₂ 0 A₂₂) id`
  -- This means if `j < i`, then the entry is 0.
  -- The order on `Fin n₁ ⊕ Fin n₂` is lexicographical.
  intro i j hij
  -- We proceed by cases on the indices i and j.
  rcases i with (i₁ | i₂)
  · -- Case i is in the left block (Fin n₁)
    rcases j with (j₁ | j₂)
    · -- Case j is also in the left block.
      -- `hij` is carried by the `Lex.inl` constructor, yielding `j₁ < i₁`.
      cases hij with
      | inl hlt =>
          -- Use the hypothesis that A₁₁ is upper triangular.
          simpa [fromBlocks_apply₁₁] using (hA₁₁ (i := i₁) (j := j₁) hlt)
    · -- Case j is in the right block.
      -- `Sum.inr _ < Sum.inl _` is impossible in the lexicographic order.
      cases hij
  · -- Case i is in the right block (Fin n₂)
    rcases j with (j₁ | j₂)
    · -- Case j is in the left block.
      -- The entry is from the bottom-left block, which is 0.
      simp [fromBlocks_apply₂₁]
    · -- Case j is also in the right block.
      -- `hij` is carried by the `Lex.inr` constructor, yielding `j₂ < i₂`.
      cases hij with
      | inr hlt =>
          -- Use the hypothesis that A₂₂ is upper triangular.
          simpa [fromBlocks_apply₂₂] using (hA₂₂ (i := i₂) (j := j₂) hlt)

/--
`isUpperTriangular_fromBlocks` 的一个特例：当左上角块为零时。
-/
lemma isUpperTriangular_fromBlocks_zero_top
    (A₁₂ : Matrix (Fin n₁) (Fin n₂) R) (A₂₂ : Matrix (Fin n₂) (Fin n₂) R)
    (hA₂₂ : IsUpperTriangular A₂₂) :
    IsUpperTriangular (fromBlocks 0 A₁₂ 0 A₂₂ : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R) := by
  -- This is a corollary of the main lemma.
  -- We just need to prove that the zero matrix is upper triangular.
  have h_zero_ut : IsUpperTriangular (0 : Matrix (Fin n₁) (Fin n₁) R) := by
    dsimp [IsUpperTriangular, BlockTriangular]
    intro i j _; simp
  exact isUpperTriangular_fromBlocks 0 A₁₂ A₂₂ h_zero_ut hA₂₂

/-- 若 `L'` 是单位下三角，则 `fromBlocks 1 0 L₂₁ L'` 也是单位下三角。 -/
lemma isUnitLowerTriangular_fromBlocks_one_zero
    (L₂₁ : Matrix (Fin n₂) (Fin n₁) R)
    (L' : Matrix (Fin n₂) (Fin n₂) R)
    (hL' : IsUnitLowerTriangular L') :
    IsUnitLowerTriangular
      (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 L₂₁ L' :
        Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R) := by
  classical
  constructor
  · -- 下三角性
    dsimp [IsLowerTriangular, IsUpperTriangular]
    -- 用转置把 lower 变成 upper
    simp [fromBlocks_transpose]
    intro i j hij
    cases i with
    | inl i₁ =>
        cases j with
        | inl j₁ =>
            -- 左上块：1 的非对角项为 0
            cases hij with
            | inl hlt =>
                have hne : j₁ ≠ i₁ := ne_of_lt hlt
                simp [fromBlocks_apply₁₁, hne.symm]
        | inr j₂ =>
            -- 右上块：在 lex 顺序下 `inr _ < inl _` 不可能（由 hij 可推出矛盾）
            cases hij
    | inr i₂ =>
        cases j with
        | inl j₁ =>
            -- 左下块：本来就是 0
            cases hij
            simp [fromBlocks_apply₂₁]
        | inr j₂ =>
            -- 右下块：继承自 L'
            cases hij with
            | inr hlt =>
                -- 这里直接用 hL'.1（lower）等价于 L'ᵀ upper 的事实
                -- hL'.1 : IsLowerTriangular L'
                -- 目标在右下角块上就是 L'ᵀ 的 upper
                have : IsUpperTriangular (L'ᵀ) := by
                  -- lower(L') ↔ upper(L'ᵀ) 是定义展开
                  simpa [IsLowerTriangular, IsUpperTriangular] using hL'.1
                simpa [fromBlocks_apply₂₂] using this hlt
  · -- 对角线为 1
    funext i
    cases i using Sum.rec with
    | inl i₁ =>
        simp [diag_apply, fromBlocks_apply₁₁]
    | inr i₂ =>
        -- 右下块的对角线由 hL'.2 控制
        simpa [diag_apply, fromBlocks_apply₂₂] using congrArg (fun d => d i₂) hL'.2

end BlockFromBlocks

end MatDecompFormal.Components.Properties







-- import Mathlib.Data.FinEnum
-- import Mathlib.LinearAlgebra.Matrix.Block
-- import Mathlib.Data.Matrix.Diagonal
-- import MatDecompFormal.Framework.FinEnum

-- namespace MatDecompFormal.Components.Properties

-- open Matrix FinEnum

-- /-!
-- # 三角矩阵属性 (Triangular Matrix Properties) - v3.0 (BlockTriangular-based)

-- 本文件定义了上三角、下三角和单位下三角矩阵的属性。

-- 这个版本的设计完全基于 Mathlib 的 `Matrix.BlockTriangular` 概念，
-- 以确保与 Mathlib 生态系统的最大兼容性并避免类型类实例冲突。

-- `BlockTriangular A b` 意味着如果 `b j < b i`，则 `A i j = 0`。
-- 我们通过使用由 `FinEnum` 提供的规范映射 `FinEnum.equiv : ι → Fin (card ι)`
-- 作为分块函数 `b`，来定义通用的三角属性。
-- -/

-- section Triangular

-- -- 声明所有定义共享的类型和类型类实例。
-- variable {ι R : Type*} [FinEnum ι] [Zero R]

-- /--
-- `IsUpperTriangular A` 是一个谓词，判断矩阵 `A` 是否为上三角矩阵。

-- 它被定义为相对于 `FinEnum.equiv` 映射下的 `BlockTriangular`。
-- -/
-- def IsUpperTriangular (A : Matrix ι ι R) : Prop :=
--   BlockTriangular A (@equiv ι _)

-- /--
-- `IsLowerTriangular A` 是一个谓词，判断矩阵 `A` 是否为下三角矩阵。

-- 一个矩阵是下三角的，当且仅当它的转置是上三角的。
-- -/
-- def IsLowerTriangular (A : Matrix ι ι R) : Prop :=
--   IsUpperTriangular Aᵀ

-- /--
-- `IsUnitLowerTriangular A` 是一个谓词，判断矩阵 `A` 是否为一个单位下三角矩阵。
-- -/
-- def IsUnitLowerTriangular [One R] (A : Matrix ι ι R) : Prop :=
--   IsLowerTriangular A ∧ A.diag = 1

-- -- ==================================================================
-- -- Basic Properties
-- -- ==================================================================

-- variable [One R] [DecidableEq ι]

-- /-- 单位矩阵 `1` 是上三角矩阵。 -/
-- lemma isUpperTriangular_one : IsUpperTriangular (1 : Matrix ι ι R) := by
--   -- 证明现在变得非常直接，因为 Mathlib 已经为我们做好了工作。
--   dsimp [IsUpperTriangular]
--   -- `BlockTriangular.one` 是 Mathlib 中的标准引理。
--   apply blockTriangular_one

-- /-- 单位矩阵 `1` 是下三角矩阵。 -/
-- lemma isLowerTriangular_one : IsLowerTriangular (1 : Matrix ι ι R) := by
--   dsimp [IsLowerTriangular]
--   rw [Matrix.transpose_one]
--   exact isUpperTriangular_one

-- /-- 单位矩阵 `1` 是单位下三角矩阵。 -/
-- lemma isUnitLowerTriangular_one : IsUnitLowerTriangular (1 : Matrix ι ι R) := by
--   constructor
--   · exact isLowerTriangular_one
--   · simp [Matrix.diag_one]

-- end Triangular

-- end MatDecompFormal.Components.Properties
