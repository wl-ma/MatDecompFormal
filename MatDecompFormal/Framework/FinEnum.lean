import Mathlib.Data.FinEnum
import Mathlib.Order.Basic


open FinEnum List

namespace MatDecompFormal.Framework

-- 步骤 1: 为所有 FinEnum 类型提供一个规范的 Preorder 实例
/--
为任何 `FinEnum` 类型 `α` 提供一个规范的 `Preorder` 实例。
序关系 `i ≤ j` 被定义为 `i` 的枚举索引小于等于 `j` 的枚举索引。
-/
noncomputable instance Preorder.ofFinEnum (α : Type*) [FinEnum α] : Preorder α :=
  Preorder.lift (@equiv α _)

/--
`FinEnum.equiv_sum_inl_lt_inr` 证明了在 `FinEnum` 为 `Sum` 类型 `α ⊕ β`
构造的双射 `equiv` 中，任何来自左侧 `α` 的元素，其枚举顺序总是严格小于
任何来自右侧 `β` 的元素。

这是分块矩阵引理能够保持序关系属性（如三角性）的理论基石。
-/
lemma equiv_sum_inl_lt_inr {α β : Type*} [FinEnum α] [FinEnum β] (a : α) (b : β) :
    equiv (Sum.inl a) < equiv (Sum.inr b) := by
  classical
  -- 使用 `DecidableEq` 提供的默认 `BEq` 实例，避免 `Sum.instBEq` 带来的冲突
  letI : BEq (α ⊕ β) := instBEqOfDecidableEq (α := α ⊕ β)
  letI : LawfulBEq (α ⊕ β) := inferInstance
  -- `FinEnum.sum` 的枚举列表：先 `α` 后 `β`
  let xs : List (α ⊕ β) := (toList α).map Sum.inl
  let ys : List (α ⊕ β) := (toList β).map Sum.inr

  have hxs : xs.Nodup := by
    dsimp [xs]
    simpa using
      (List.nodup_map_iff (f := Sum.inl) (l := toList α) (hf := Sum.inl_injective)).2
        (nodup_toList (α := α))
  have hys : ys.Nodup := by
    dsimp [ys]
    simpa using
      (List.nodup_map_iff (f := Sum.inr) (l := toList β) (hf := Sum.inr_injective)).2
        (nodup_toList (α := β))
  have hdisj : List.Disjoint xs ys := by
    refine List.disjoint_left.mpr ?_
    intro x hx hy
    cases x <;> simp [xs, ys] at hx hy
  have hnodup : (xs ++ ys).Nodup := hxs.append hys hdisj

  -- 将不等式转化为索引比较
  change (equiv (Sum.inl a)).val < (equiv (Sum.inr b)).val
  simp [FinEnum.sum, FinEnum.ofList, FinEnum.ofNodupList, xs, ys,
    List.dedup_eq_self.mpr hnodup]
  -- 目标化为 `idxOf` 上的简单算术
  have h_inl_mem : Sum.inl a ∈ xs := by dsimp [xs]; simp
  have h_inr_not_mem : Sum.inr b ∉ xs := by dsimp [xs]; simp
  have h_inl_idx :
      (xs ++ ys).idxOf (Sum.inl a) = xs.idxOf (Sum.inl a) :=
    List.idxOf_append_of_mem (a := Sum.inl a) (l₁ := xs) (l₂ := ys) h_inl_mem
  have h_inr_idx :
      (xs ++ ys).idxOf (Sum.inr b) = xs.length + ys.idxOf (Sum.inr b) :=
    List.idxOf_append_of_notMem (a := Sum.inr b) (l₁ := xs) (l₂ := ys) h_inr_not_mem
  have h_inl_lt : xs.idxOf (Sum.inl a) < xs.length :=
    List.idxOf_lt_length_iff.mpr h_inl_mem
  have h_goal : xs.idxOf (Sum.inl a) < xs.length + ys.idxOf (Sum.inr b) :=
    Nat.lt_of_lt_of_le h_inl_lt (Nat.le_add_right _ _)
  have h_idx :
      (xs ++ ys).idxOf (Sum.inl a) < (xs ++ ys).idxOf (Sum.inr b) := by
    simpa [h_inl_idx, h_inr_idx] using h_goal
  simpa [xs, ys] using h_idx

/-- 这是一个方便的推论，用于在证明中制造矛盾 -/
lemma not_equiv_sum_inr_lt_inl {α β : Type*} [FinEnum α] [FinEnum β] (a : α) (b : β) :
    ¬ (equiv (Sum.inr b) < equiv (Sum.inl a)) :=
  by
    -- Ensure we use the standard `Fin` order (coming from its `LinearOrder` instance),
    -- rather than the `Preorder` induced by `FinEnum`.
    letI : Preorder (Fin (card (α ⊕ β))) := Fin.instLinearOrder.toPreorder
    exact not_lt.mpr (le_of_lt (equiv_sum_inl_lt_inr (α := α) (β := β) a b))

/--
`FinEnum.orderIsoOfCardEq` 构造了一个保序同构 `α ≃o β`，
只要 `α` 和 `β` 的基数相等。
-/
def FinEnum.orderIsoOfCardEq {α β} [FinEnum α] [FinEnum β] (h : card α = card β) : α ≃o β :=
  let e_α : α ≃o Fin (card α) := {
    toEquiv := @equiv α _,
    map_rel_iff' := by intro a b; rfl
  }
  let e_β : Fin (card β) ≃o β := {
    toEquiv := (@equiv β _).symm,
    map_rel_iff' := by
      intro a b
      change (@equiv β _ ((@equiv β _).symm a) ≤ @equiv β _ ((@equiv β _).symm b)) ↔ a ≤ b
      simp [Equiv.apply_symm_apply]
  }
  e_α.trans ((Fin.castOrderIso h).trans e_β)

end MatDecompFormal.Framework
