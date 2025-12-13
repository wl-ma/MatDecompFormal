import MatDecompFormal.Framework.Universe
import MatDecompFormal.Framework.Induction

namespace MatDecompFormal.Framework

open Matrix


/-!
# 宇宙分解实例 (Universe Decomposition Instance) - v6.0 (Final Version)

本文件是连接抽象框架与具体实例的最终版本。它定义了 `RectDecompositionInstance`
结构体，并提供了一个主定理 `prove_for_fin`，该定理通过调用 `induction_on_subtype`
来完成所有证明工作。
-/

-- PositiveDecompositionInstance 结构体定义 (签名微调版)
-- 现在它的字段直接使用 PosFinRectUniverse 类型，而不是零散的 (m n h_pos)
structure PositiveDecompositionInstance (R : Type*) where
  P_univ : FinRectUniverse R → Prop
  P_pos : PosFinRectUniverse R → Prop
  P_compat : ∀ (x : PosFinRectUniverse R), P_pos x ↔ P_univ x.val
  μ : FinRectUniverse R → ℕ
  μ_base : ℕ
  base_pos : ∀ {x : PosFinRectUniverse R}, μ x.val ≤ μ_base → P_pos x
  r_pos : PosFinRectUniverse R → PosFinRectUniverse R → Prop
  IsSliceable_pos : PosFinRectUniverse R → Prop
  slice_pos : ∀ (x : PosFinRectUniverse R), IsSliceable_pos x → FinRectUniverse R
  transport : ∀ {x y : PosFinRectUniverse R}, r_pos y x → P_pos y → P_pos x
  lift_from_slice : ∀ (x : PosFinRectUniverse R) (hx : IsSliceable_pos x),
                    P_univ (slice_pos x hx) → P_pos x
  reach : ∀ (x : PosFinRectUniverse R), μ x.val > μ_base →
          Σ' (y : PosFinRectUniverse R),
            Σ' (hy : IsSliceable_pos y),
              r_pos y x ∧ μ (slice_pos y hy) < μ x.val

-- RectDecompositionInstance 结构体定义保持不变
structure RectDecompositionInstance (R : Type*) where
  P_univ : FinRectUniverse R → Prop
  pos_instance : PositiveDecompositionInstance R
  P_univ_compat : pos_instance.P_univ = P_univ
  P_pos_compat_top : ∀ (x : PosFinRectUniverse R), pos_instance.P_pos x ↔ P_univ x.val
  base_zero : ∀ {x}, x.1.1 = 0 ∨ x.1.2 = 0 → P_univ x

namespace RectDecompositionInstance

variable {R : Type*}

/--
主原理 (最终版)：从 `RectDecompositionInstance` 证明对所有 `m, n` 的定理。
这个证明是对 `induction_on_subtype` 的一个清晰、直接的调用。
-/
theorem prove_for_fin (inst : RectDecompositionInstance R) :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) R), inst.P_univ ⟨⟨m, n⟩, ⟨A⟩⟩ := by
  suffices ∀ (x : FinRectUniverse R), inst.P_univ x by
    intro m n A; exact this ⟨⟨m, n⟩, ⟨A⟩⟩

  -- 直接调用新定理，显式传入 Subtype.val
  apply induction_on_subtype
    -- 1. 提供宇宙、子类型和显式转换函数
    (X := FinRectUniverse R)
    (SubX := PosFinRectUniverse R)
    (toX := Subtype.val) -- 关键改动！
    -- 2. 提供度量和性质
    (μ := inst.pos_instance.μ)
    (μ_base := inst.pos_instance.μ_base)
    (P := inst.P_univ)
    (P_sub := inst.pos_instance.P_pos)
    (P_compat := inst.P_pos_compat_top)
    -- 3. 将 inst.pos_instance 中的字段直接传递给 _sub 参数
    (r_sub := inst.pos_instance.r_pos)
    (IsSliceable_sub := inst.pos_instance.IsSliceable_pos)
    (slice_sub := inst.pos_instance.slice_pos)
    (transport_sub := inst.pos_instance.transport)
    (lift_from_slice_sub := by
      intro x hx h
      -- 将 `inst.P_univ` 上的证明转换为 `pos_instance.P_univ`
      have h' : inst.pos_instance.P_univ (inst.pos_instance.slice_pos x hx) := by
        simpa [inst.P_univ_compat] using h
      exact inst.pos_instance.lift_from_slice x hx h')
    (reach_sub := inst.pos_instance.reach)
    -- 4. 构造统一的基例证明 `base_univ`
    (base_univ := by
      intro x h_base_reason
      cases h_base_reason with
      | inl h_not_in_sub =>
        have h_zero_dim : x.1.1 = 0 ∨ x.1.2 = 0 := by
          by_contra h_not_zero
          push_neg at h_not_zero
          have h_pos : x.1.1 > 0 ∧ x.1.2 > 0 := by
            exact ⟨Nat.pos_of_ne_zero h_not_zero.left, Nat.pos_of_ne_zero h_not_zero.right⟩
          -- 构造一个 x_sub，其 .val 就是 x
          let x_sub : PosFinRectUniverse R := ⟨x, h_pos⟩
          -- 这与 h_not_in_sub 矛盾
          exact h_not_in_sub x_sub rfl
        exact inst.base_zero h_zero_dim
      | inr h_mu_le =>
        by_cases h_in_sub : ∃ (x_sub : PosFinRectUniverse R), x_sub.val = x
        · rcases h_in_sub with ⟨x_sub, rfl⟩
          rw [← inst.P_pos_compat_top]
          exact inst.pos_instance.base_pos h_mu_le
        · have h_zero_dim : x.1.1 = 0 ∨ x.1.2 = 0 := by
            by_contra h_not_zero
            push_neg at h_not_zero
            have h_pos : x.1.1 > 0 ∧ x.1.2 > 0 := by
              exact ⟨Nat.pos_of_ne_zero h_not_zero.left, Nat.pos_of_ne_zero h_not_zero.right⟩
            exact h_in_sub ⟨⟨x, h_pos⟩, rfl⟩
          exact inst.base_zero h_zero_dim)

end RectDecompositionInstance


/--
`SquareDecompositionInstance`：方阵版本的便捷封装，直接复用矩形实例的性质。
-/
abbrev SquareDecompositionInstance (R : Type*) (_rect_inst : RectDecompositionInstance R) :=
  (Σ n, Matrix (Fin n) (Fin n) R) → Prop

namespace SquareDecompositionInstance

variable {R : Type*} {rect_inst : RectDecompositionInstance R}

/-- 方阵宇宙的性质，直接由矩形实例专门化得到。 -/
def P (rect_inst : RectDecompositionInstance R) : SquareDecompositionInstance R rect_inst :=
  fun x : Σ n, Matrix (Fin n) (Fin n) R =>
    rect_inst.pos_instance.P_univ ⟨⟨x.1, x.1⟩, ⟨x.2⟩⟩

/-- 方阵版的证明直接调用矩形实例的主定理。 -/
theorem prove_for_fin_square :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R),
      (P (rect_inst := rect_inst)) ⟨n, A⟩ := by
  intro n A
  simpa [P, rect_inst.P_univ_compat] using
    (RectDecompositionInstance.prove_for_fin rect_inst n n A)

end SquareDecompositionInstance


end MatDecompFormal.Framework







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
