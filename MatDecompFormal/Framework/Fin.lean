import Mathlib.Order.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Algebra.Ring.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Block


namespace MatDecompFormal.Framework
open Matrix


/-!
### Fin n Utilities

本节定义了我们项目中特有的、基于 `Mathlib` 基础工具的高级 `Fin n` 等价关系。
这些是我们框架特有的“胶水代码”，用于简化 `Components` 中的证明。
-/

#check finSumFinEquiv

/--
一个专门用于将 `Fin (n + 1)` 拆分为 `Fin 1 ⊕ Fin n` 的等价关系。
这个定义是“计算性的”，它通过模式匹配 (`Fin.cases`) 而不是类型转换 (`cast`)
来构造，因此对 Lean 的 `simp` 自动化工具非常友好。

- `0` 映射到 `Sum.inl 0`。
- `i.succ` 映射到 `Sum.inr i`。
-/
def finSuccEquivSum (n : ℕ) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n where
  toFun := Fin.cases (Sum.inl 0) (fun i => Sum.inr i)
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv := by
    intro x; cases x using Fin.cases <;> simp
  right_inv := by
    intro x
    rcases x with (y | i) <;> simp
    rw [Subsingleton.elim y 0]

def finSuccEquivSumLex (n : ℕ) : Fin (n + 1) ≃ (Fin 1 ⊕ₗ Fin n) := by
  -- 直接把你原来的 finSuccEquivSum 的 toFun / invFun 搬过来
  -- 注意 codomain 改成 ⊕ₗ
  classical
  refine
  { toFun := Fin.cases (Sum.inl 0) (fun i => Sum.inr i)
    invFun := Sum.elim (fun _ => 0) Fin.succ
    left_inv := ?_
    right_inv := ?_ }
  · intro x; cases x using Fin.cases <;> simp
  · intro x; rcases x with (y | i) <;> simp
    -- y : Fin 1
    simp [Subsingleton.elim y 0]


-- /--
-- `finSuccEquivSum` 的保序同构版本。

-- 它证明了 `finSuccEquivSum` 定义的映射，在 `Fin (n + 1)` 的标准序和
-- `Fin 1 ⊕ Fin n` 的字典序之间是保序的。
-- -/
-- def finSuccOrderIsoSum (n : ℕ) : Fin (n + 1) ≃o Fin 1 ⊕ₗ Fin n where
--   toEquiv := (finSuccEquivSum n).trans (toLex (α := Fin 1 ⊕ Fin n))
--   map_rel_iff' := by
--     intro x y
--     cases x using Fin.cases with
--     | zero =>
--         cases y using Fin.cases with
--         | zero =>
--             simp [finSuccEquivSum]
--         | succ y =>
--             -- `0 ≤ y.succ` corresponds to the lexicographic fact that `inl 0` is
--             -- always before any `inr y`.
--             simp [finSuccEquivSum]
--     | succ x =>
--         cases y using Fin.cases with
--         | zero =>
--             simp [finSuccEquivSum]
--         | succ y =>
--             simp [finSuccEquivSum, Fin.succ_le_succ_iff]


-- /--
-- A helper lemma proving that `finSuccEquivSum` (viewed in the lex order)
-- is strictly monotone. This encapsulates the proof logic so it can be
-- reused easily.
-- -/
-- lemma finSuccEquivSum_strictMono (n : ℕ) : StrictMono (finSuccEquivSum n) := by
--   intro x y h_lt
--   cases x using Fin.cases with
--   | zero =>
--       cases y using Fin.cases with
--       | zero =>
--           -- x=0, y=0 contradicts h_lt : 0 < 0
--           exact (lt_irrefl _ h_lt).elim
--       | succ y_val =>
--           -- x=0, y=y_val.succ
--           -- finSuccEquivSum sends 0 ↦ inl 0, succ _ ↦ inr _
--           dsimp [finSuccEquivSum]
--           -- goal: Sum.inl 0 < Sum.inr y_val, true for lex order on sums
--           change toLex (Sum.inl 0) < toLex (Sum.inr y_val)
--           exact Sum.Lex.inl_lt_inr _ _
--   | succ x_val =>
--       cases y using Fin.cases with
--       | zero =>
--           -- x=x_val.succ, y=0 contradicts h_lt
--           exact (by cases (not_lt_of_ge (Fin.zero_le _) h_lt))
--       | succ y_val =>
--           -- x=x_val.succ, y=y_val.succ
--           dsimp [finSuccEquivSum]
--           -- goal reduces to x_val < y_val
--           simpa using (Fin.succ_lt_succ_iff.mp h_lt)



/--
一个用于将 `Fin n` 视为 `Fin 0 ⊕ Fin n` 的等价关系。
这个定义是“计算性的”，它直接将 `Fin n` 中的每个元素 `i` 映射到 `Sum.inr i`。

这在需要对行或列进行“平凡”的分块以适应 `fromBlocks` API 时非常有用，
例如在 `ZeroColumnMethod` 中。
-/
def finZeroSumFinEquiv (n : ℕ) : Fin n ≃ Fin 0 ⊕ Fin n where
  toFun := Sum.inr
  invFun := Sum.elim (Fin.elim0) (fun i => i)
  left_inv := by
    intro i; simp
  right_inv := by
    intro x
    rcases x with (y | i) <;> simp
    exact Fin.elim0 y


/--
一个关键的“胶水”引理，它证明了通过 `Fin.succ` 切片与通过 `finSuccEquivSum`
进行 `reindex` 后取 `toBlocks₂₂` 是等价的。
-/
lemma submatrix_succ_eq_toBlocks₂₂ {n m : ℕ} {R : Type*}
    (A : Matrix (Fin (n + 1)) (Fin (m + 1)) R) :
    A.submatrix Fin.succ Fin.succ =
      (reindex (finSuccEquivSum n) (finSuccEquivSum m) A).toBlocks₂₂ := by
  rfl

end MatDecompFormal.Framework
