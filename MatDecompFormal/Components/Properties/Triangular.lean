import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Sum.Order
import Mathlib.Data.FinEnum


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

variable {ι R : Type*} [Zero R]  --[LinearOrder ι]

/--
`IsUpperTriangular A`：矩阵 `A` 在给定索引顺序下是上三角矩阵。

形式上，它被定义为相对于恒等映射 `id : ι → ι` 的 `BlockTriangular`：
如果 `j < i`，则 `A i j = 0`。
-/
def IsUpperTriangular [LT ι] (A : Matrix ι ι R) : Prop :=
  BlockTriangular A (fun i : ι => i)

/--
`IsLowerTriangular A`：矩阵 `A` 是下三角矩阵，当且仅当 `Aᵀ` 是上三角矩阵。
-/
def IsLowerTriangular [LT ι] (A : Matrix ι ι R) : Prop :=
  IsUpperTriangular Aᵀ

/--
`IsUnitLowerTriangular A`：`A` 是一个单位下三角矩阵，
即下三角且主对角线全为 `1`。
-/
def IsUnitLowerTriangular [LT ι] [One R] (A : Matrix ι ι R) : Prop :=
  IsLowerTriangular A ∧ A.diag = 1

-- ==================================================================
-- Basic Properties
-- ==================================================================

variable [One R] [Preorder ι] [DecidableEq ι]

/-- 单位矩阵 `1` 是上三角矩阵。 -/
lemma isUpperTriangular_one : IsUpperTriangular (1 : Matrix ι ι R) := by
  -- `blockTriangular_one` 说明单位矩阵对任意分块函数都是 BlockTriangular
  dsimp [IsUpperTriangular]
  simpa using
    (blockTriangular_one (R := R) (b := fun i : ι => i))

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

/--
任何由“单例”类型（只有一个元素的类型）索引的方阵都是上三角矩阵。
这个结论是“空洞为真”的，因为 `j < i` 的条件永远无法满足。
-/
lemma isUpperTriangular_of_subsingleton {ι R} [Zero R] [Preorder ι] [Subsingleton ι]
    (A : Matrix ι ι R) : IsUpperTriangular A := by
  dsimp [IsUpperTriangular, BlockTriangular]
  intro i j hij
  -- 因为 ι 是一个单例类型，所以任意两个元素都相等。
  have : i = j := Subsingleton.elim i j
  -- 将 i = j 代入 hij
  rw [this] at hij
  -- hij 现在是 j < j，这与小于号的非自反性矛盾。
  exfalso; exact lt_irrefl j hij

/--
任何由“单例”类型索引的方阵也都是下三角矩阵。
-/
lemma isLowerTriangular_of_subsingleton {ι R} [Zero R] [Preorder ι] [Subsingleton ι]
    (A : Matrix ι ι R) : IsLowerTriangular A := by
  -- 证明：A 是下三角 ↔ Aᵀ 是上三角。
  -- Aᵀ 也是由 Subsingleton 类型索引的，所以它是上三角的。
  dsimp [IsLowerTriangular]
  exact isUpperTriangular_of_subsingleton Aᵀ

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

-- 关键：用 `⊕ₗ` 的字典序索引（它在 Mathlib 里自带顺序结构）
local notation "ι" => (Fin n₁ ⊕ₗ Fin n₂)

/--
若对角块 `A₁₁` 和 `A₂₂` 都是上三角的，则
把 `fromBlocks A₁₁ A₁₂ 0 A₂₂` 通过 `reindex Sum.toLex Sum.toLex`
搬到 `Fin n₁ ⊕ₗ Fin n₂` 上之后，它是上三角的。
-/
lemma isUpperTriangular_fromBlocks_toLex
    (A₁₁ : Matrix (Fin n₁) (Fin n₁) R) (A₁₂ : Matrix (Fin n₁) (Fin n₂) R)
    (A₂₂ : Matrix (Fin n₂) (Fin n₂) R)
    (hA₁₁ : IsUpperTriangular A₁₁) (hA₂₂ : IsUpperTriangular A₂₂) :
    IsUpperTriangular
      ((fromBlocks A₁₁ A₁₂ 0 A₂₂ :
          Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R).reindex toLex toLex :
        Matrix ι ι R) := by
  dsimp [IsUpperTriangular, BlockTriangular] at hA₁₁ hA₂₂ ⊢
  intro i j hij
  -- i j : Fin n₁ ⊕ₗ Fin n₂，但仍可按 inl/inr 分块讨论
  rcases i with i₁ | i₂
  · rcases j with j₁ | j₂
    · -- 左上块：归约到 hA₁₁
      have hij' : j₁ < i₁ := Sum.Lex.inl_lt_inl_iff.mp hij
      -- reindex 后矩阵条目就是原矩阵在 ofLex 下的条目；`simp` 可以把它化回 fromBlocks_apply₁₁
      simpa [Matrix.reindex_apply, fromBlocks_apply₁₁] using hA₁₁ (i := i₁) (j := j₁) hij'
    · -- 右上块：在字典序下不可能出现 `inr _ < inl _`
      -- （这里 j = inr, i = inl，所以 hij 不可构造）
      cases hij
  · rcases j with j₁ | j₂
    · -- 左下块：fromBlocks 的左下块就是 0
      simp [ofLex, Lex, fromBlocks_apply₂₁]
    · -- 右下块：归约到 hA₂₂
      have hij' : j₂ < i₂ := Sum.Lex.inr_lt_inr_iff.mp hij
      simpa [Matrix.reindex_apply, fromBlocks_apply₂₂] using hA₂₂ (i := i₂) (j := j₂) hij'

/-- `isUpperTriangular_fromBlocks_toLex` 的一个特例：左上角块为 0。 -/
lemma isUpperTriangular_fromBlocks_zero_top_toLex
    (A₁₂ : Matrix (Fin n₁) (Fin n₂) R) (A₂₂ : Matrix (Fin n₂) (Fin n₂) R)
    (hA₂₂ : IsUpperTriangular A₂₂) :
    IsUpperTriangular
      ((fromBlocks 0 A₁₂ 0 A₂₂ :
          Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R).reindex toLex toLex :
        Matrix ι ι R) := by
  have h_zero_ut : IsUpperTriangular (0 : Matrix (Fin n₁) (Fin n₁) R) := by
    dsimp [IsUpperTriangular, BlockTriangular]; intro _ _ _; simp
  exact isUpperTriangular_fromBlocks_toLex
    (n₁ := n₁) (n₂ := n₂) (A₁₁ := 0) (A₁₂ := A₁₂) (A₂₂ := A₂₂) h_zero_ut hA₂₂

/-- 若 `L'` 是单位下三角，则搬到 `⊕ₗ` 后 `fromBlocks 1 0 L₂₁ L'` 也是单位下三角。 -/
lemma isUnitLowerTriangular_fromBlocks_one_zero_toLex
    (L₂₁ : Matrix (Fin n₂) (Fin n₁) R)
    (L' : Matrix (Fin n₂) (Fin n₂) R)
    (hL' : IsUnitLowerTriangular L') :
    IsUnitLowerTriangular
      ((fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 L₂₁ L' :
          Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R).reindex toLex toLex :
        Matrix ι ι R) := by
  constructor
  · -- lower triangular ↔ transpose is upper triangular
    dsimp [IsLowerTriangular]
    -- transpose 与 reindex 可交换（mathlib 里有 transpose_reindex）
    simpa [Matrix.transpose_reindex, fromBlocks_transpose] using
      (isUpperTriangular_fromBlocks_toLex (n₁ := n₁) (n₂ := n₂)
        (A₁₁ := (1 : Matrix (Fin n₁) (Fin n₁) R)ᵀ)
        (A₁₂ := (L₂₁ : Matrix (Fin n₂) (Fin n₁) R)ᵀ)
        (A₂₂ := (L' : Matrix (Fin n₂) (Fin n₂) R)ᵀ)
        (by simp [transpose_one]; apply isUpperTriangular_one)
        (by
          -- hL'.1 : IsLowerTriangular L' = IsUpperTriangular L'ᵀ
          simpa [IsLowerTriangular] using hL'.1))
  · -- diag = 1
    funext i
    rcases i with i₁ | i₂
    · simp [Matrix.diag, Matrix.reindex_apply, fromBlocks_apply₁₁, Lex, toLex]
    · -- 右下角对角线继承自 hL'.2
      have := congrArg (fun d => d i₂) hL'.2
      simpa [Matrix.diag, Matrix.reindex_apply, fromBlocks_apply₂₂] using this

end BlockFromBlocks

-- section BlockFromBlocks

-- variable {n₁ n₂ : ℕ} {R : Type*} [CommRing R]
-- -- variable [FinEnum (Fin n₁ ⊕ Fin n₂)]
-- -- variable [LinearOrder (Fin n₁ ⊕ Fin n₂)]

-- /--
-- 若对角块 `A₁₁` 和 `A₂₂` 都是上三角的，则 `fromBlocks A₁₁ A₁₂ 0 A₂₂`
-- （一个上块三角矩阵）也是上三角的。
-- -/
-- lemma isUpperTriangular_fromBlocks
--     (A₁₁ : Matrix (Fin n₁) (Fin n₁) R) (A₁₂ : Matrix (Fin n₁) (Fin n₂) R)
--     (A₂₂ : Matrix (Fin n₂) (Fin n₂) R)
--     (hA₁₁ : IsUpperTriangular A₁₁) (hA₂₂ : IsUpperTriangular A₂₂) :
--     IsUpperTriangular (fromBlocks A₁₁ A₁₂ 0 A₂₂ : Matrix (Fin n₁ ⊕ Fin n₂)
--       (Fin n₁ ⊕ Fin n₂) R) := by
--   dsimp [IsUpperTriangular, BlockTriangular] at hA₁₁ hA₂₂ ⊢
--   intro i j hij
--   rcases i with i₁ | i₂
--   · rcases j with j₁ | j₂
--     · -- Both indices lie in the top-left block; reduce to `hA₁₁`.
--       have hij' : j₁ < i₁ := Sum.inl_lt_inl_iff.mp hij
--       simpa [fromBlocks_apply₁₁] using hA₁₁ (i := i₁) (j := j₁) hij'
--     · -- `Sum.inr _ < Sum.inl _` is impossible in the chosen order.
--       cases hij
--   · rcases j with j₁ | j₂
--     · -- Bottom-left block is zero regardless of `hij`.
--       simp [fromBlocks_apply₂₁]
--     · -- Both indices lie in the bottom-right block; reduce to `hA₂₂`.
--       have hij' : j₂ < i₂ := by simpa using hij
--       simpa [fromBlocks_apply₂₂] using hA₂₂ (i := i₂) (j := j₂) hij'

-- /--
-- `isUpperTriangular_fromBlocks` 的一个特例：当左上角块为零时。
-- -/
-- lemma isUpperTriangular_fromBlocks_zero_top
--     (A₁₂ : Matrix (Fin n₁) (Fin n₂) R) (A₂₂ : Matrix (Fin n₂) (Fin n₂) R)
--     (hA₂₂ : IsUpperTriangular A₂₂) :
--     IsUpperTriangular (fromBlocks 0 A₁₂ 0 A₂₂ : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R) := by
--   have h_zero_ut : IsUpperTriangular (0 : Matrix (Fin n₁) (Fin n₁) R) := by
--     dsimp [IsUpperTriangular, BlockTriangular]; intro i j _; simp
--   exact isUpperTriangular_fromBlocks 0 A₁₂ A₂₂ h_zero_ut hA₂₂

-- /-- 若 `L'` 是单位下三角，则 `fromBlocks 1 0 L₂₁ L'` 也是单位下三角。 -/
-- lemma isUnitLowerTriangular_fromBlocks_one_zero
--     (L₂₁ : Matrix (Fin n₂) (Fin n₁) R)
--     (L' : Matrix (Fin n₂) (Fin n₂) R)
--     (hL' : IsUnitLowerTriangular L') :
--     IsUnitLowerTriangular
--       (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 L₂₁ L' :
--         Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R) := by
--   constructor
--   · -- Prove lower triangularity by showing the transpose is upper triangular.
--     dsimp [IsLowerTriangular]
--     rw [fromBlocks_transpose]
--     apply isUpperTriangular_fromBlocks
--     · -- Top-left block is `(1)ᵀ = 1`, which is upper triangular.
--       rw [transpose_one]
--       exact isUpperTriangular_one
--     · -- Bottom-right block is `L'ᵀ`, which is upper triangular because `L'` is lower triangular.
--       exact hL'.1
--   · -- Prove diagonal is all ones.
--     funext i
--     rcases i with (i₁ | i₂)
--     · -- Diagonal entry in the top-left block.
--       simp [diag_apply, fromBlocks_apply₁₁]
--     · -- Diagonal entry in the bottom-right block.
--       simpa [diag_apply, fromBlocks_apply₂₂] using congr_fun hL'.2 i₂

-- end BlockFromBlocks

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
