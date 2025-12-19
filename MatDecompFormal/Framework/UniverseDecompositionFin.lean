import MatDecompFormal.Framework.Universe
import MatDecompFormal.Framework.Induction

namespace MatDecompFormal.Framework

open Matrix

/-!
# Universe Decomposition Instances (Fin version) — flattened

This file provides a *single* instance structure `SubtypeInductionInstance`
whose fields match the parameters of `induction_on_subtype`.

It then specializes this to:

* the **rectangular** universe `FinRectUniverse R` with subtype `PosFinRectUniverse R`;
* a **square** universe `FinSqUniverse R` (Fin-indexed square matrices) with
  subtype `PosFinSqUniverse R`.

The goal is to make concrete decomposition instances (e.g. PLU) much shorter:
they only need to fill the fields of `SubtypeInductionInstance`.
-/

section CastTools

variable {R : Type*}

/-- Cast a square matrix along a dimension equality. -/
def castSq {m n : ℕ} (h : m = n) (A : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin n) (Fin n) R := by
  cases h
  simpa using A

@[simp] lemma castSq_rfl {m : ℕ} (A : Matrix (Fin m) (Fin m) R) :
    castSq (R := R) (m := m) (n := m) rfl A = A := by
  rfl

lemma castSq_congr {m n : ℕ} (h₁ h₂ : m = n) (A : Matrix (Fin m) (Fin m) R) :
    castSq (R := R) h₁ A = castSq (R := R) h₂ A := by
  cases h₁; cases h₂; rfl

lemma castSq_trans {m n p : ℕ} (h₁ : m = n) (h₂ : n = p) (A : Matrix (Fin m) (Fin m) R) :
    castSq (R := R) h₂ (castSq (R := R) h₁ A) = castSq (R := R) (h₁.trans h₂) A := by
  cases h₁; cases h₂; rfl

@[simp] lemma castSq_symm {m n : ℕ} (h : m = n) (A : Matrix (Fin m) (Fin m) R) :
    castSq (R := R) h.symm (castSq (R := R) h A) = A := by
  cases h; rfl

/--
For `n > 0`, cast `n×n` to `(n-1+1)×(n-1+1)`.

**Implementation note**: we define this by cases on `n`, so the `succ`-case is definitional,
making simp much easier downstream.
-/
def castToPredSucc {n : ℕ} (hn : n > 0) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin ((n - 1) + 1)) (Fin ((n - 1) + 1)) R := by
  cases n with
  | zero =>
      -- hn : 0 > 0, contradiction
      exact (False.elim ((lt_irrefl 0) hn))
  | succ k =>
      -- here ((succ k - 1) + 1) definitionaly simplifies to (k+1)
      simpa using A

/-- A simp lemma for the common case `n = k+1`. -/
@[simp] lemma castToPredSucc_succ (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    castToPredSucc (R := R) (n := k + 1) (Nat.succ_pos _) A = A := by
  simp [castToPredSucc]

/--
For `n>0`, `castToPredSucc` cancels the cast from `(n-1+1)` to `n`.
This is the lemma you want to simp away goals like
`castToPredSucc hn (castSq (succ_pred_eq_of_pos hn) B) = B`.
-/
@[simp] lemma castToPredSucc_castSq_succPred {n : ℕ} (hn : n > 0)
    (B : Matrix (Fin ((n - 1) + 1)) (Fin ((n - 1) + 1)) R) :
    castToPredSucc (R := R) (n := n) hn
        (castSq (R := R) (Nat.succ_pred_eq_of_pos hn) B)
      = B := by
  cases n with
  | zero =>
      exact (False.elim ((lt_irrefl 0) hn))
  | succ n' =>
      -- here everything is definitional / simp
      simp [castToPredSucc, castSq]

end CastTools


/-!
## L0: A single “flattened” instance for `induction_on_subtype`
-/

/--
`SubtypeInductionInstance` packages exactly the data needed to run
`induction_on_subtype` on a universe `X` with a distinguished subtype `SubX`.
-/
structure SubtypeInductionInstance (X SubX : Type*) (toX : SubX → X) where
  μ : X → Nat
  μ_base : Nat
  P : X → Prop
  P_sub : SubX → Prop
  P_compat : ∀ (x_sub : SubX), P_sub x_sub ↔ P (toX x_sub)

  r_sub : SubX → SubX → Prop
  IsSliceable_sub : SubX → Prop
  slice_sub : ∀ (x_sub : SubX), IsSliceable_sub x_sub → X

  transport_sub :
    ∀ {x_sub y_sub}, r_sub y_sub x_sub → P_sub y_sub → P_sub x_sub

  lift_from_slice_sub :
    ∀ (x_sub : SubX) (hx : IsSliceable_sub x_sub),
      P (slice_sub x_sub hx) → P_sub x_sub

  /--
  Reachability packaged in the “metric > μ_base” style (your usual style).
  We will translate it to the new `¬ BaseSet` form when calling the induction.
  -/
  reach_sub :
    ∀ (x_sub : SubX), μ (toX x_sub) > μ_base →
      Σ' (y_sub : SubX), Σ' (hy : IsSliceable_sub y_sub),
        r_sub y_sub x_sub ∧ μ (slice_sub y_sub hy) < μ (toX x_sub)

  /--
  Base case on the whole universe:
  either `x` is not in the subtype-image, or `μ x ≤ μ_base`.
  -/
  base_univ :
    ∀ (x : X), (∀ (x_sub : SubX), toX x_sub ≠ x) ∨ μ x ≤ μ_base → P x

namespace SubtypeInductionInstance

variable {X SubX : Type*} {toX : SubX → X}

/-- Main driver: directly calls the new `induction_on_subtype`. -/
theorem prove (inst : SubtypeInductionInstance X SubX toX) :
    ∀ (x : X), inst.P x := by
  -- BaseSet is “μ x ≤ μ_base” (the typical choice).
  let BaseSet : X → Prop := fun x => inst.μ x ≤ inst.μ_base

  -- Call the generalized induction.
  refine induction_on_subtype'
    (X := X)
    (SubX := SubX) (toX := toX)
    (μ := inst.μ) (relα := (· < ·)) (hwf := wellFounded_lt)
    (P := inst.P)
    (P_sub := inst.P_sub)
    (P_compat := inst.P_compat)
    (r_sub := inst.r_sub)
    (IsSliceable_sub := inst.IsSliceable_sub)
    (slice_sub := inst.slice_sub)
    (transport_sub := inst.transport_sub)
    (lift_from_slice_sub := inst.lift_from_slice_sub)
    (BaseSet := BaseSet)
    (reach_sub := by
      intro x_sub h_not_base
      -- `¬ (μ ≤ μ_base)` -> `μ > μ_base`
      have h_gt : inst.μ (toX x_sub) > inst.μ_base :=
        Nat.lt_of_not_ge h_not_base
      -- use the instance reach
      rcases inst.reach_sub x_sub h_gt with ⟨y_sub, hy, h_r, h_prog⟩
      exact ⟨y_sub, hy, h_r, h_prog⟩)
    (base_univ := by
      intro x hx
      -- just reuse inst.base_univ; BaseSet is definitional
      simpa [BaseSet] using inst.base_univ x hx)

end SubtypeInductionInstance



/-!
## L1: Rectangular universe specialization
-/

/-- Rectangular specialization: `X = FinRectUniverse R`, `SubX = PosFinRectUniverse R`. -/
abbrev RectSubtypeInductionInstance (R : Type*) :=
  SubtypeInductionInstance (X := FinRectUniverse R)
    (SubX := PosFinRectUniverse R) (toX := Subtype.val)

namespace RectSubtypeInductionInstance

variable {R : Type*} (inst : RectSubtypeInductionInstance R)

/-- Convenience API: prove `inst.P` for every `m × n` matrix. -/
theorem prove_for_fin :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) R),
      inst.P ⟨⟨m, n⟩, ⟨A⟩⟩ := by
  intro m n A
  exact (SubtypeInductionInstance.prove inst) ⟨⟨m, n⟩, ⟨A⟩⟩

end RectSubtypeInductionInstance



/-!
## L2: Square universe (Fin-indexed) and specialization

-/


/-- Square specialization: `X = FinSqUniverse R`, `SubX = PosFinSqUniverse R`. -/
abbrev SquareSubtypeInductionInstance (R : Type*) :=
  SubtypeInductionInstance (X := FinSqUniverse R)
    (SubX := PosFinSqUniverse R) (toX := Subtype.val)

namespace SquareSubtypeInductionInstance

variable {R : Type*} (inst : SquareSubtypeInductionInstance R)

/-- Convenience API: prove `inst.P` for every `n × n` matrix. -/
theorem prove_for_fin :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R),
      inst.P ⟨n, ⟨A⟩⟩ := by
  intro n A
  exact (SubtypeInductionInstance.prove (inst := inst)) ⟨n, ⟨A⟩⟩

end SquareSubtypeInductionInstance


end MatDecompFormal.Framework







-- import MatDecompFormal.Framework.Universe
-- import MatDecompFormal.Framework.Induction

-- namespace MatDecompFormal.Framework

-- open Matrix


-- /-!
-- # 宇宙分解实例 (Universe Decomposition Instance) - v6.0 (Final Version)

-- 本文件是连接抽象框架与具体实例的最终版本。它定义了 `RectDecompositionInstance`
-- 结构体，并提供了一个主定理 `prove_for_fin`，该定理通过调用 `induction_on_subtype`
-- 来完成所有证明工作。
-- -/

-- -- PositiveDecompositionInstance 结构体定义 (签名微调版)
-- -- 现在它的字段直接使用 PosFinRectUniverse 类型，而不是零散的 (m n h_pos)
-- structure PositiveDecompositionInstance (R : Type*) where
--   P_univ : FinRectUniverse R → Prop
--   P_pos : PosFinRectUniverse R → Prop
--   P_compat : ∀ (x : PosFinRectUniverse R), P_pos x ↔ P_univ x.val
--   μ : FinRectUniverse R → ℕ
--   μ_base : ℕ
--   base_pos : ∀ {x : PosFinRectUniverse R}, μ x.val ≤ μ_base → P_pos x
--   r_pos : PosFinRectUniverse R → PosFinRectUniverse R → Prop
--   IsSliceable_pos : PosFinRectUniverse R → Prop
--   slice_pos : ∀ (x : PosFinRectUniverse R), IsSliceable_pos x → FinRectUniverse R
--   transport : ∀ {x y : PosFinRectUniverse R}, r_pos y x → P_pos y → P_pos x
--   lift_from_slice : ∀ (x : PosFinRectUniverse R) (hx : IsSliceable_pos x),
--                     P_univ (slice_pos x hx) → P_pos x
--   reach : ∀ (x : PosFinRectUniverse R), μ x.val > μ_base →
--           Σ' (y : PosFinRectUniverse R),
--             Σ' (hy : IsSliceable_pos y),
--               r_pos y x ∧ μ (slice_pos y hy) < μ x.val

-- -- RectDecompositionInstance 结构体定义保持不变
-- structure RectDecompositionInstance (R : Type*) where
--   P_univ : FinRectUniverse R → Prop
--   pos_instance : PositiveDecompositionInstance R
--   P_univ_compat : pos_instance.P_univ = P_univ
--   P_pos_compat_top : ∀ (x : PosFinRectUniverse R), pos_instance.P_pos x ↔ P_univ x.val
--   base_zero : ∀ {x}, x.1.1 = 0 ∨ x.1.2 = 0 → P_univ x

-- namespace RectDecompositionInstance

-- variable {R : Type*}

-- /--
-- 主原理 (最终版)：从 `RectDecompositionInstance` 证明对所有 `m, n` 的定理。
-- 这个证明是对 `induction_on_subtype` 的一个清晰、直接的调用。
-- -/
-- theorem prove_for_fin (inst : RectDecompositionInstance R) :
--     ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) R), inst.P_univ ⟨⟨m, n⟩, ⟨A⟩⟩ := by
--   suffices ∀ (x : FinRectUniverse R), inst.P_univ x by
--     intro m n A; exact this ⟨⟨m, n⟩, ⟨A⟩⟩

--   -- 直接调用新定理，显式传入 Subtype.val
--   apply induction_on_subtype
--     -- 1. 提供宇宙、子类型和显式转换函数
--     (X := FinRectUniverse R)
--     (SubX := PosFinRectUniverse R)
--     (toX := Subtype.val) -- 关键改动！
--     -- 2. 提供度量和性质
--     (μ := inst.pos_instance.μ)
--     (μ_base := inst.pos_instance.μ_base)
--     (P := inst.P_univ)
--     (P_sub := inst.pos_instance.P_pos)
--     (P_compat := inst.P_pos_compat_top)
--     -- 3. 将 inst.pos_instance 中的字段直接传递给 _sub 参数
--     (r_sub := inst.pos_instance.r_pos)
--     (IsSliceable_sub := inst.pos_instance.IsSliceable_pos)
--     (slice_sub := inst.pos_instance.slice_pos)
--     (transport_sub := inst.pos_instance.transport)
--     (lift_from_slice_sub := by
--       intro x hx h
--       -- 将 `inst.P_univ` 上的证明转换为 `pos_instance.P_univ`
--       have h' : inst.pos_instance.P_univ (inst.pos_instance.slice_pos x hx) := by
--         simpa [inst.P_univ_compat] using h
--       exact inst.pos_instance.lift_from_slice x hx h')
--     (reach_sub := inst.pos_instance.reach)
--     -- 4. 构造统一的基例证明 `base_univ`
--     (base_univ := by
--       intro x h_base_reason
--       cases h_base_reason with
--       | inl h_not_in_sub =>
--         have h_zero_dim : x.1.1 = 0 ∨ x.1.2 = 0 := by
--           by_contra h_not_zero
--           push_neg at h_not_zero
--           have h_pos : x.1.1 > 0 ∧ x.1.2 > 0 := by
--             exact ⟨Nat.pos_of_ne_zero h_not_zero.left, Nat.pos_of_ne_zero h_not_zero.right⟩
--           -- 构造一个 x_sub，其 .val 就是 x
--           let x_sub : PosFinRectUniverse R := ⟨x, h_pos⟩
--           -- 这与 h_not_in_sub 矛盾
--           exact h_not_in_sub x_sub rfl
--         exact inst.base_zero h_zero_dim
--       | inr h_mu_le =>
--         by_cases h_in_sub : ∃ (x_sub : PosFinRectUniverse R), x_sub.val = x
--         · rcases h_in_sub with ⟨x_sub, rfl⟩
--           rw [← inst.P_pos_compat_top]
--           exact inst.pos_instance.base_pos h_mu_le
--         · have h_zero_dim : x.1.1 = 0 ∨ x.1.2 = 0 := by
--             by_contra h_not_zero
--             push_neg at h_not_zero
--             have h_pos : x.1.1 > 0 ∧ x.1.2 > 0 := by
--               exact ⟨Nat.pos_of_ne_zero h_not_zero.left, Nat.pos_of_ne_zero h_not_zero.right⟩
--             exact h_in_sub ⟨⟨x, h_pos⟩, rfl⟩
--           exact inst.base_zero h_zero_dim)

-- end RectDecompositionInstance


-- /--
-- `SquareDecompositionInstance`：方阵版本的便捷封装，直接复用矩形实例的性质。
-- -/
-- abbrev SquareDecompositionInstance (R : Type*) (_rect_inst : RectDecompositionInstance R) :=
--   (Σ n, Matrix (Fin n) (Fin n) R) → Prop

-- namespace SquareDecompositionInstance

-- variable {R : Type*} {rect_inst : RectDecompositionInstance R}

-- /-- 方阵宇宙的性质，直接由矩形实例专门化得到。 -/
-- def P (rect_inst : RectDecompositionInstance R) : SquareDecompositionInstance R rect_inst :=
--   fun x : Σ n, Matrix (Fin n) (Fin n) R =>
--     rect_inst.pos_instance.P_univ ⟨⟨x.1, x.1⟩, ⟨x.2⟩⟩

-- /-- 方阵版的证明直接调用矩形实例的主定理。 -/
-- theorem prove_for_fin_square :
--     ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R),
--       (P (rect_inst := rect_inst)) ⟨n, A⟩ := by
--   intro n A
--   simpa [P, rect_inst.P_univ_compat] using
--     (RectDecompositionInstance.prove_for_fin rect_inst n n A)

-- end SquareDecompositionInstance


-- end MatDecompFormal.Framework







-- import Mathlib
-- import MatDecompFormal.Framework.Universe
-- import MatDecompFormal.Framework.Induction
-- import MatDecompFormal.Abstractions.Schema

-- /-!
-- # UniverseDecompositionFin

-- 这个文件把「在 Fin 上做分解 / 归纳」的宇宙版抽象成一个可复用的模块。

-- **Universe 固定为**

-- `FinSqUniverse R := Σ n, Matrix (Fin n) (Fin n) R`

-- 也就是「所有阶数的方阵」的 disjoint union。

-- 我们在这个 Universe 上抽象出一份数据
-- `SquareDecompositionInstance R`，只要你在这个宇宙上提供：

-- * `P_univ` : 要证明的性质（例如：存在某种分解）
-- * `r` : 在宇宙上的“允许变换”
-- * `IsSliceable` : 哪些状态可被切片
-- * `slice` : 对可切片状态进行“降维”的算子
-- * `transport` : 沿变换关系 `r` 搬运 `P_univ`
-- * `lift_from_slice` : 从子问题解 `P_univ (slice x)` 提升回原问题 `P_univ x`
-- * `reach_metric` : 若阶数 `n > 0`，可以走一步，切出一个阶数严格更小的子问题
-- * `base_metric` : 阶数为 `0` 的基例

-- 那么就可以调用 `transformSliceInduction`，得到这类通用原理：

-- * `SquareDecompositionInstance.prove_all`:
--   对所有宇宙元素 `x : FinSqUniverse R`，都有 `P_univ x`
-- * `SquareDecompositionInstance.prove_for_fin`:
--   专门化到每个 `n` 和 `A : Matrix (Fin n) (Fin n) R`

-- 之后每个具体分解（比如 PLU、行阶梯形等），只需要在自己的 `Instance` 文件里：

-- 1. 选定 `P_univ`（一般就是“HasDecomposition 某 schema”）
-- 2. 定义 `r` / `IsSliceable` / `slice`（通常来自某个 `ReductionStrategy`）
-- 3. 给出四个引理 `transport` / `lift_from_slice` / `reach_metric` / `base_metric`

-- 就可以直接用本文件的原理，拿到 **Fin n 版本** 的存在性定理。
-- -/

-- namespace MatDecompFormal.Framework

-- open Matrix
-- open MatDecompFormal.Abstractions


-- /--
-- 在 `FinSqUniverse R` 上描述一个“宇宙级”的分解 / 性质证明问题。

-- 只要提供：

-- * `P_univ` : 在宇宙上的命题（例如 `∃ 分解`）
-- * `r` : 宇宙上的“允许变换”关系
-- * `IsSliceable` : 哪些宇宙状态可以被“切片”
-- * `slice` : 对可切片状态执行降维切片
-- * `transport` : 若 `r y x` 且 `P_univ x`，则可搬运到 `P_univ y`
-- * `lift_from_slice` : 若 `x` 可切片，且子问题 `slice x` 满足 `P_univ`，则原问题 `x` 也满足
-- * `reach_metric` : 若当前阶数 `> 0`，则存在一步下降到更小阶数的子问题
-- * `base_metric` : 阶数 `= 0` 的基例

-- 就可以通过 `transformSliceInduction` 得到 `∀ x, P_univ x`。
-- -/
-- structure SquareDecompositionInstance (R : Type*) where
--   /-- 宇宙上要证明的性质。对于具体分解来说，它通常会是
--   `fun ⟨n, A⟩ ↦ HasDecomposition (某个 Schema n) A`。 -/
--   P_univ : FinSqUniverse R → Prop

--   /-- 宇宙上的“允许变换”关系。 -/
--   r : FinSqUniverse R → FinSqUniverse R → Prop

--   /-- 哪些宇宙状态是“可切片”的。 -/
--   IsSliceable : FinSqUniverse R → Prop

--   /-- 对一个可切片状态，给出它的“子问题”（通常是子块矩阵）。 -/
--   slice : ∀ {x}, IsSliceable x → FinSqUniverse R

--   /-- `Transport`：若 `r y x` 且 `P_univ x`，则可以得到 `P_univ y`。 -/
--   transport :
--     Transport r P_univ

--   /-- 从子问题的结论提升回原问题。 -/
--   lift_from_slice :
--     ∀ {x} (hx : IsSliceable x),
--       P_univ (slice hx) → P_univ x

--   /-- 进展性：当阶数 `> 0` 时，可以走一步，
--   找到一个 `y`，它是 `x` 的变换后状态，且切片后的阶数严格变小。 -/
--   reach_metric :
--     ∀ {x}, μ_fin x > 0 →
--       ∃ y, ∃ (hy : IsSliceable y),
--         r y x ∧ μ_fin (slice hy) < μ_fin x

--   /-- 基例：当阶数为 `0` 时，直接给出 `P_univ x`。 -/
--   base_metric :
--     ∀ {x}, μ_fin x = 0 → P_univ x

-- namespace SquareDecompositionInstance

-- variable {R : Type*}

-- /--
-- 主原理 1：在 `FinSqUniverse R` 上，用 `SquareDecompositionInstance` 给出的数据，
-- 通过 `transformSliceInduction` 得到 `∀ x, inst.P_univ x`。
-- -/
-- theorem prove_all (inst : SquareDecompositionInstance R) :
--     ∀ x : FinSqUniverse R, inst.P_univ x := by
--   -- 直接调用框架层的归纳原理
--   have h :=
--     transformSliceInduction
--       (X := FinSqUniverse R)
--       (μ := μ_fin)
--       (P := inst.P_univ)
--       (r := inst.r)
--       (h_trans := inst.transport)
--       (IsSliceable := inst.IsSliceable)
--       (slice := inst.slice)
--       (lift_from_slice := inst.lift_from_slice)
--       (reach_metric := inst.reach_metric)
--       (base_metric := inst.base_metric)
--   -- `h` : ∀ x, inst.P_univ x
--   exact h

-- /--
-- 主原理 2：把 `prove_all` 专门化成“对每个阶数 `n` 和方阵 `A` 的定理”。

-- 以后在具体分解实例（比如 PLU）中，只要把

-- inst.P_univ ⟨n, A⟩

-- 设定为你想要的结论（如 `HasDecomposition (PLU_Schema n R) A`），
-- 就可以通过这个定理拿到 Fin 版本的存在性结论。
-- -/
-- theorem prove_for_fin (inst : SquareDecompositionInstance R) :
--     ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), inst.P_univ ⟨n, A⟩ := by
--   intro n A
--   -- 直接从宇宙版本专门化
--   have h := prove_all (R := R) inst ⟨n, A⟩
--   exact h

-- end SquareDecompositionInstance

-- end MatDecompFormal.Framework
