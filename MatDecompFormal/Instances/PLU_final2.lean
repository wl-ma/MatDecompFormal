import MatDecompFormal.Framework.Induction
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Abstractions.Strategy
import MatDecompFormal.Abstractions.ReductionCombinators
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Components.Reductions.Schur
import MatDecompFormal.Components.Reductions.ZeroColumn
import MatDecompFormal.Components.Transformations.Elementary.Pivot
import MatDecompFormal.Framework.UniverseDecompositionFin  -- 你刚写好的通用“宇宙分解实例”模块

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Components.Transformations.Elementary

/-!
# PLU decomposition (Fin n core)

本文件只给出 PLU 的 **Fin n 核心版**：
* 定义 Schema
* 定义 Strategy（只依赖 Fin n 上已有的 SchurMethod / ZeroColumnMethod / PivotTransform）
* 构建一个 SquareDecompositionInstanceFin（用于复用 `exists_decomposition_fin`）
* 得到最终定理 `exists_plu_decomposition_fin`

证明部分目标：尽量只“调用已有模块”，复杂代数证明放在 Components/BlockLifting 等处。
-/


/- =======================================================================
   1. PLU Schema on `Fin n`
   ======================================================================= -/

section PLU_Fin_Schema

variable {n : ℕ} (R : Type*) [Field R] [DecidableEq R]

/-- PLU 分解的分解模式（Fin n 版） -/
def PLU_Schema_fin (n : ℕ) : DecompositionSchema (Fin n) (Fin n) R where
  Factors := Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R
  property := fun (P, L, U) ↦
    IsPermutation P ∧ IsUnitLowerTriangular L ∧ IsUpperTriangular U
  equation := fun A (P, L, U) ↦ P * A = L * U

/-- 命题：`A` 存在 PLU 分解（Fin n 版） -/
def HasPLU_fin {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Prop :=
  HasDecomposition (PLU_Schema_fin (R := R) n) A

end PLU_Fin_Schema


/- =======================================================================
   2. PLU Strategy on `Fin n`
   ======================================================================= -/

section PLU_Fin_Strategy

variable {n : ℕ} (R : Type*) [Field R] [DecidableEq R]

/--
PLU 的策略（Fin n 版）：
* transform: 选择首列非零元做行交换（Pivot）
* reduction: SchurMethod 若可切片，否则 ZeroColumnMethod
-/
noncomputable def PLU_Strategy_fin (hn : n > 0) :
    ReductionStrategy (Fin n) (Fin n) R where
  -- 令 n = k.succ，方便对齐 Components 中的 n+1 约定
  transform :=
    let k := n - 1
    have hsucc : n = k.succ := Nat.succ_pred_eq_of_pos hn
    let j0 : Fin n := ⟨0, hn⟩
    let i0 : Fin n := ⟨0, hn⟩
    let red :=
      (ReductionMethod.try_else
        (SchurMethod (n := k) (R := R))
        (ZeroColumnMethod (n := k) (m := k) (R := R))
        (by rfl) (by rfl))
    {
      T := Fin n
      Goal := red.IsSliceable
      decGoal := by classical exact Classical.decPred _
      apply := fun i A => (swap R i0 i) * A
      find := by
        intro A h_goal_not_met
        classical
        -- 未达成目标 ⇒ 既非可逆首元，也非整列为 0，因此存在非零行可换到顶部
        have h_not : ¬ (IsUnit (A 0 0) ∨ ∀ i, A i 0 = 0) := by
          simpa [hsucc, red, ReductionMethod.try_else, SchurMethod, ZeroColumnMethod] using
            h_goal_not_met
        have h_exists : ∃ i, A i 0 ≠ 0 := by
          have h_zero_col : ¬ ∀ i, A i 0 = 0 := (not_or.mp h_not).2
          push_neg at h_zero_col; exact h_zero_col
        exact Classical.choose h_exists
      find_spec := by
        intro A h_goal_not_met
        classical
        have h_not : ¬ (IsUnit (A 0 0) ∨ ∀ i, A i 0 = 0) := by
          simpa [hsucc, red, ReductionMethod.try_else, SchurMethod, ZeroColumnMethod] using
            h_goal_not_met
        have h_exists : ∃ i, A i 0 ≠ 0 := by
          have h_zero_col : ¬ ∀ i, A i 0 = 0 := (not_or.mp h_not).2
          push_neg at h_zero_col; exact h_zero_col
        let i := Classical.choose h_exists
        have hi : A i 0 ≠ 0 := Classical.choose_spec h_exists
        -- 交换后首元变为非零 ⇒ 可走 Schur 分支
        have h_unit : IsUnit (((swap R i0 i) * A) i0 j0) := by
          have hne : ((swap R i0 i) * A) i0 j0 ≠ 0 := by
            -- 在域上，非零即单位
            have : ((swap R i0 i) * A) i0 j0 = A i 0 := by
              simp [swap_mul_apply_left]
            simpa [this] using hi
          exact isUnit_iff_ne_zero.mpr hne
        have hi0 : (i0 : Fin n) = 0 := by
          apply Fin.ext; simp [i0]
        have hj0 : (j0 : Fin n) = 0 := by
          apply Fin.ext; simp [j0]
        exact Or.inl (by
          -- 直接展开目标
          dsimp [red, ReductionMethod.try_else, SchurMethod, ZeroColumnMethod]
          simpa [hsucc, hi0, hj0] using h_unit)
    }
  reduction :=
    let k := n - 1
    have hsucc : n = k.succ := Nat.succ_pred_eq_of_pos hn
    show ReductionMethod (Fin n) (Fin n) R from
      by
        -- 使用 Components 中基于 n+1 的实现，借助 n = k.succ 对齐类型
        simpa [hsucc] using
          (ReductionMethod.try_else
            (SchurMethod (n := k) (R := R))
            (ZeroColumnMethod (n := k) (m := k) (R := R))
            (by rfl) (by rfl))
  goal_is_sliceable := by
    -- transform.Goal 与 reduction.IsSliceable 按定义相同
    rfl
  μ := fun {_ι _κ} _ _ _ => FinEnum.card _ι
  μ_mono := by
    intro A t
    -- 行交换不改维度
    simp
  slice_progress := by
    intro A hA
    -- 切片把行维度从 n 降到 n-1
    let k := n - 1
    have hsucc : n = k.succ := Nat.succ_pred_eq_of_pos hn
    -- 与 transform/reduction 中一致的规约方法
    let red :=
      (ReductionMethod.try_else
        (SchurMethod (n := k) (R := R))
        (ZeroColumnMethod (n := k) (m := k) (R := R))
        (by rfl) (by rfl))
    -- μ 仅依赖行维度，切片行维度为 k，原矩阵为 k.succ
    change FinEnum.card red.Sliceι < FinEnum.card (Fin n)
    simp [μ, red, hsucc, FinEnum.card_eq_fintypeCard]
    have : k < k.succ := Nat.lt_succ_self k
    simpa [hsucc] using this

end PLU_Fin_Strategy


/- =======================================================================
   3. 四个“胶水”引理：transport / lift / base / reach
   ======================================================================= -/

section PLU_Fin_Glue

variable (R : Type*) [Field R] [DecidableEq R]

/-- transport：沿策略的 `r` 搬运 HasPLU（Fin n 版） -/
private lemma transport_plu_fin (n : ℕ) (hn : n > 0) :
    Transport (PLU_Strategy_fin (n := n) (R := R) hn).r
      (HasPLU_fin (R := R) (n := n)) := by
  -- 这里一般只用 PivotTransform 的 `r` 定义 + IsPermutation / triangular 的闭包性质
  -- 建议最终放进 PivotTransform 对应文件里：PivotTransform.transport
  intro x y hxy hx
  -- TODO: 把 PivotTransform 的搬运性质整理成可复用 lemma，然后这里 `simpa` 调用
  sorry

/-- lift：从 slice 的解提升到原问题（Fin n 版） -/
private lemma lift_from_slice_plu_fin (n : ℕ) (hn : n > 0) :
    LiftFromSlice
      (reduction := (PLU_Strategy_fin (n := n) (R := R) hn).reduction)
      (P := HasPLU_fin (R := R) (n := n)) := by
  -- 这里用 Components/BlockLifting + Schur/ZeroColumn 的重构公式
  -- 建议把具体代数证明放到 BlockLifting.lean，留这里一行调用
  intro A hSlice hP
  -- TODO: 用 `BlockLifting` 中的“reconstruct preserves PLU”引理
  sorry

/-- base：n = 0 的基例（Fin 0 上矩阵惟一） -/
private lemma base_plu_fin :
    BaseMetric
      (μ := fun (x : Matrix (Fin 0) (Fin 0) R) => 0)
      (P := HasPLU_fin (R := R) (n := 0)) := by
  intro A hμ
  classical
  -- Fin 0 上 A = 1（ext 无元素）
  refine ⟨(1, 1, 1), ?_, ?_⟩
  · -- 因子性质
    dsimp [PLU_Schema_fin]
    refine ⟨?_, ?_, ?_⟩
    · -- IsPermutation 1
      simpa [IsPermutation]
    · -- IsUnitLowerTriangular 1
      simp [IsUnitLowerTriangular, IsLowerTriangular, IsUpperTriangular]
    · -- IsUpperTriangular 1
      simp [IsUpperTriangular]
  · -- 方程
    simp

/-- reach：n > 0 时，策略可以找到可切片态并让 μ 严格下降 -/
private lemma reach_plu_fin (n : ℕ) (hn : n > 0) :
    ReachMetric
      (μ := fun (A : Matrix (Fin n) (Fin n) R) => n)
      (r := (PLU_Strategy_fin (n := n) (R := R) hn).r)
      (IsSliceable := (PLU_Strategy_fin (n := n) (R := R) hn).reduction.IsSliceable)
      (slice := (PLU_Strategy_fin (n := n) (R := R) hn).reduction.slice) := by
  -- 这通常就是 `ReductionStrategy.mk_reach_metric` 的一个直接实例
  intro A hμpos
  classical
  simpa using (PLU_Strategy_fin (n := n) (R := R) hn).mk_reach_metric (A := A) hn

end PLU_Fin_Glue


/- =======================================================================
   4. 构建可复用的 Fin n “分解实例”，并导出最终定理
   ======================================================================= -/

section PLU_Fin_Instance

variable {n : ℕ} (R : Type*) [Field R] [DecidableEq R]

/--
把 PLU 的 Schema + Strategy + glue lemmas 打包成通用实例，
以便直接调用 `exists_decomposition_fin`。
-/
noncomputable def PLU_Instance_fin (hn : n > 0) :
    SquareDecompositionInstance (R := R) where
  Schema := PLU_Schema_fin (R := R) n
  Strategy := PLU_Strategy_fin (n := n) (R := R) hn
  transport := transport_plu_fin (R := R) n hn
  lift_from_slice := lift_from_slice_plu_fin (R := R) n hn
  base := by
    -- 这个字段仅在 n=0 分支使用；对 n>0 这里不会被用到
    -- 若你的 SquareDecompositionInstanceFin 把 base/reach 都放在同一个结构里，
    -- 这里可以用 `by cases n <;> ...` 的方式统一处理。
    classical
    cases n with
    | zero =>
        simpa using (base_plu_fin (R := R))
    | succ n =>
        -- 任意占位（不会被用到），可用 `by intro; simp` 或者 `by aesop`
        intro A hμ
        cases hμ
  reach := reach_plu_fin (R := R) n hn

/-- **PLU 存在性（Fin n 版最终定理）** -/
theorem exists_plu_decomposition_fin (hn : n > 0) (A : Matrix (Fin n) (Fin n) R) :
    HasPLU_fin (R := R) (n := n) A := by
  -- 主定理：完全复用通用模块
  simpa [HasPLU_fin, PLU_Schema_fin] using
    (exists_decomposition_fin (R := R) (n := n) (inst := PLU_Instance_fin (R := R) (n := n) hn) A)

end PLU_Fin_Instance

end MatDecompFormal.Instances
