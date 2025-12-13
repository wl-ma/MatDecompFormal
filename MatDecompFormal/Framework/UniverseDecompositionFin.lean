import MatDecompFormal.Framework.Universe
import MatDecompFormal.Framework.Induction

namespace MatDecompFormal.Framework

open Matrix

/-!
# 宇宙分解实例 (Universe Decomposition Instance) - v4.2 (Final Corrected & Simplified)

本文件是连接抽象框架与具体实例的最终、最简洁的版本。
它通过在 `prove` 定理的内部证明中巧妙地处理类型边界，为用户提供了
一个极其干净和直观的接口。
-/

/--
`PositiveDecompositionInstance` 描述了如何在 `m > 0 ∧ n > 0` 的宇宙中进行归纳证明。
-/
structure PositiveDecompositionInstance (R : Type*) where
  /-- 在整个（包括零维度）宇宙上要证明的性质。 -/
  P_univ : FinRectUniverse R → Prop
  /-- 在 `m > 0 ∧ n > 0` 宇宙上要证明的性质。 -/
  P_pos : PosFinRectUniverse R → Prop
  /-- 关键兼容性证明：确保两个性质在正维度宇宙中是等价的。 -/
  P_compat : ∀ (x : PosFinRectUniverse R), P_pos x ↔ P_univ x.val
  /-- 归纳所使用的度量函数。 -/
  μ : FinRectUniverse R → ℕ
  /-- 归纳基例的度量边界。 -/
  μ_base : ℕ
  /-- 正维度宇宙中的基例证明 (`μ ≤ μ_base`)。 -/
  base_pos : ∀ {x : PosFinRectUniverse R}, μ x.val ≤ μ_base → P_pos x
  r_pos : ∀ {m n} (_h_pos : m > 0 ∧ n > 0),
        Matrix (Fin m) (Fin n) R → Matrix (Fin m) (Fin n) R → Prop
  IsSliceable_pos : ∀ {m n} (_h_pos : m > 0 ∧ n > 0),
                    Matrix (Fin m) (Fin n) R → Prop
  slice_pos : ∀ {m n h_pos} {A : Matrix (Fin m) (Fin n) R},
              IsSliceable_pos h_pos A → FinRectUniverse R
  transport : ∀ {m n h_pos} {A B}, r_pos h_pos B A → P_pos ⟨⟨⟨m,n⟩,⟨B⟩⟩, h_pos⟩ →
              P_pos ⟨⟨⟨m,n⟩,⟨A⟩⟩, h_pos⟩
  lift_from_slice : ∀ {m n h_pos} {A} (hA : IsSliceable_pos h_pos A),
                    P_univ (slice_pos hA) → P_pos ⟨⟨⟨m,n⟩,⟨A⟩⟩, h_pos⟩
  reach : ∀ {m n h_pos} (A : Matrix (Fin m) (Fin n) R),
          μ ⟨⟨m,n⟩,⟨A⟩⟩ > μ_base →
          -- The return type is now a Σ type, carrying the new matrix and proofs
          Σ' (B : Matrix (Fin m) (Fin n) R),
            Σ' (hB : IsSliceable_pos h_pos B),
              r_pos h_pos B A ∧ μ (slice_pos hB) < μ ⟨⟨m,n⟩,⟨A⟩⟩

/--
`RectDecompositionInstance` (v4.2)
-/
structure RectDecompositionInstance (R : Type*) where
  P_univ : FinRectUniverse R → Prop
  pos_instance : PositiveDecompositionInstance R
  P_univ_compat : pos_instance.P_univ = P_univ
  P_pos_compat_top : ∀ (x : PosFinRectUniverse R), pos_instance.P_pos x ↔ P_univ x.val
  base_zero : ∀ {x}, x.1.1 = 0 ∨ x.1.2 = 0 → P_univ x

namespace RectDecompositionInstance

variable {R : Type*}

/--
主原理 (v4.2)：从 `RectDecompositionInstance` 证明对所有 `m, n` 的定理。
-/
theorem prove_for_fin (inst : RectDecompositionInstance R) :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) R), inst.P_univ ⟨⟨m, n⟩, ⟨A⟩⟩ := by
  -- 核心思想：我们想对 `P_univ` 在 `FinRectUniverse` 上进行归纳。
  -- 我们将使用 `WellFounded.induction`，这是最底层的归纳法。
  intro m n A
  let x : FinRectUniverse R := ⟨⟨m, n⟩, ⟨A⟩⟩
  -- 在 `μ` 上进行良基归纳
  suffices ∀ (x : FinRectUniverse R), inst.P_univ x by
    simpa using this x

  intro x'
  apply WellFounded.fix μ_wf
  intro x ih
  -- 对 x 的维度进行情况讨论
  by_cases h_pos : x.1.1 > 0 ∧ x.1.2 > 0
  · -- Case 1: 维度为正。这里是归纳的核心。
    let x_pos : PosFinRectUniverse R := ⟨x, h_pos⟩
    -- 使用 P_compat 将目标转换为 P_pos
    -- 先证明 `P_pos`，再通过兼容性得到目标。
    -- 对 μ(x) 与 μ_base 的关系进行讨论
    by_cases h_mu : inst.pos_instance.μ x > inst.pos_instance.μ_base
    · -- Subcase 1.1: 归纳步骤
      -- 调用 reach 找到 y 和切片
      rcases inst.pos_instance.reach (m := x.1.1) (n := x.1.2) (h_pos := h_pos)
          (A := x.2.A) h_mu with ⟨B, ⟨hB, h_r, h_prog⟩⟩
      -- 获取切片对象
      let slice_obj := inst.pos_instance.slice_pos hB
      -- 对切片对象应用归纳假设 `ih`
      have h_slice_p : inst.pos_instance.P_univ slice_obj := by
        simpa [inst.P_univ_compat] using ih slice_obj h_prog
      -- 使用 lift 将结论提升到 B
      have h_b_p : inst.pos_instance.P_pos ⟨⟨⟨x.1.1, x.1.2⟩, ⟨B⟩⟩, h_pos⟩ :=
        inst.pos_instance.lift_from_slice hB h_slice_p
      -- 使用 transport 将结论传递到 x
      have h_x_p : inst.pos_instance.P_pos x_pos :=
        inst.pos_instance.transport (A := x.2.A) (B := B) h_r h_b_p
      exact (inst.P_pos_compat_top x_pos).1 h_x_p
    · -- Subcase 1.2: 正维度宇宙的基例
      have h_mu_le : inst.pos_instance.μ x ≤ inst.pos_instance.μ_base := by
        exact le_of_not_gt h_mu
      have h_pos_p : inst.pos_instance.P_pos x_pos :=
        inst.pos_instance.base_pos h_mu_le
      exact (inst.P_pos_compat_top x_pos).1 h_pos_p
  · -- Case 2: 维度为零。这是整个归纳的最终基例。
    have h_zero : x.1.1 = 0 ∨ x.1.2 = 0 := by
      have h_not_pos : ¬ (x.1.1 > 0) ∨ ¬ (x.1.2 > 0) := (not_and_or).mp h_pos
      cases h_not_pos with
      | inl hm_not_pos =>
        exact Or.inl (Nat.le_zero.mp (le_of_not_gt hm_not_pos))
      | inr hn_not_pos =>
        exact Or.inr (Nat.le_zero.mp (le_of_not_gt hn_not_pos))
    exact inst.base_zero h_zero
where
  μ_wf : WellFounded (fun x y : FinRectUniverse R ↦
      inst.pos_instance.μ x < inst.pos_instance.μ y) :=
    InvImage.wf (fun x ↦ inst.pos_instance.μ x) wellFounded_lt

end RectDecompositionInstance

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
