import Mathlib.Data.FinEnum
import Mathlib.Order.Basic


open FinEnum List

namespace MatDecompFormal.Framework

-- ==================================================================
-- Section 1: The Correct Order Instance for FinEnum
-- ==================================================================

/--
为任何 `FinEnum` 类型 `α` 提供一个规范的 `LinearOrder` 实例。

序关系 `i ≤ j` 被定义为 `i` 的枚举索引小于等于 `j` 的枚举索引。
由于 `Fin n` 上的序是线性的，通过 `Equiv` 提升后得到的序也是线性的。
这个实例是整个框架中所有与序相关的属性（如三角性）的基石。
-/
noncomputable instance LinearOrder.ofFinEnum (α : Type*) [FinEnum α] : LinearOrder α :=
  -- `LinearOrder.lift` 是一个高阶构造器，它将一个已知线性序通过一个单射函数
  -- “提升”到一个新的类型上。`equiv` 是一个双射，因此自然是单射。
  LinearOrder.lift' (@equiv α _) (equiv.injective)

-- ==================================================================
-- Section 2: Properties of the FinEnum Order
-- ==================================================================


/--
`FinEnum.equiv_sum_inl_lt_inr` 证明了在 `FinEnum` 为 `Sum` 类型 `α ⊕ β`
构造的双射 `equiv` 中，任何来自左侧 `α` 的元素，其枚举顺序总是严格小于
任何来自右侧 `β` 的元素。

这是分块矩阵引理能够保持序关系属性（如三角性）的理论基石。
-/
lemma equiv_sum_inl_lt_inr {α β : Type*} [FinEnum α] [FinEnum β] (a : α) (b : β) :
    equiv (Sum.inl a) < equiv (Sum.inr b) := by
  classical
  -- Fix the `DecidableEq` choices so `List.dedup` uses the enumeration-induced equality
  letI decEqα : DecidableEq α := FinEnum.decEq
  letI decEqβ : DecidableEq β := FinEnum.decEq
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
  have h_dedup : (xs ++ ys).dedup = xs ++ ys := List.dedup_eq_self.mpr hnodup

  -- 将不等式转化为索引比较
  change (equiv (Sum.inl a)).val < (equiv (Sum.inr b)).val
  simp [FinEnum.sum, FinEnum.ofList, FinEnum.ofNodupList]
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
  have h_idx_dedup :
      ((xs ++ ys).dedup).idxOf (Sum.inl a) < ((xs ++ ys).dedup).idxOf (Sum.inr b) := by
    simpa [h_dedup] using h_idx
  simpa [xs, ys] using h_idx_dedup

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


/--
构造一个 `ι` 与 `({i₀} ⊕ {i | i ≠ i₀})` 之间的保序同构。
这个构造是 PLU 分解等算法中分块正确性的关键。
-/
noncomputable def orderIsoSumComplFirst {ι} [FinEnum ι] (i₀ : ι) (h_min : ∀ i, i₀ ≤ i) :
    ι ≃o ({i // i = i₀} ⊕ {i // i ≠ i₀}) :=
  -- 证明思路：通过一系列保序同构的复合来构造
  -- ι ≃o Fin n ≃o Fin 1 ⊕ Fin (n-1) ≃o {i₀} ⊕ {i≠i₀}
  let n := card ι
  have h_pos : n > 0 := by
    by_contra h_n_le_zero
    -- 修正 1: 使用 rw 进行推理
    have h_card_eq_n : card ι = n := by simp [n]
    rw [Nat.eq_zero_of_le_zero (not_lt.mp h_n_le_zero)] at h_card_eq_n
    have h_empty := card_eq_zero_iff.mp h_card_eq_n
    exact h_empty.false i₀

  -- 1. ι ≃o Fin n
  let e₁ : ι ≃o Fin n := FinEnum.orderIsoOfCardEq rfl

  -- 2. i₀ 对应的 Fin n 中的元素是 0
  have h_i₀_is_zero : e₁ i₀ = ⟨0, h_pos⟩ := by
    -- 修正 2 & 3: 明确构造 ⟨0, h_pos⟩ 并使用 Fin.eq_of_val_eq
    apply Fin.eq_of_val_eq
    apply Nat.eq_zero_of_le_zero
    have := (e₁.map_rel_iff').mpr (h_min (e₁.symm ⟨0, h_pos⟩))
    simp at this
    exact this

  -- 3. Fin n ≃o Fin 1 ⊕ Fin (n-1)
  let e₂ : Fin n ≃o Fin 1 ⊕ Fin (n - 1) :=
    -- 修正 4: 使用 Order.finSumFinEquiv
    (Order.finSumFinEquiv 1 (n - 1)).symm.trans (finCongrOrderIso (add_tsub_cancel_of_le (Nat.one_le_of_lt h_pos)))

  -- 4. {i₀} ≃o Fin 1
  let e₃_inl : {i // i = i₀} ≃o Fin 1 :=
    FinEnum.orderIsoOfCardEq (by
      -- 修正 5: 使用 rw 和 Fintype.card_of_subsingleton
      have : Subsingleton { i // i = i₀ } := by intro a b; exact Subtype.eq (a.2.trans b.2.symm)
      rw [card_of_subsingleton])

  -- 5. {i≠i₀} ≃o Fin (n-1)
  let e₃_inr : {i // i ≠ i₀} ≃o Fin (n - 1) :=
    FinEnum.orderIsoOfCardEq (by
      -- 修正 5: 使用 rw 和 Fintype.card_subtype_neq
      have h_card_eq_n : card ι = n := by simp [n]
      rw [card_subtype_neq, h_card_eq_n])

  -- 6. {i₀} ⊕ {i≠i₀} ≃o Fin 1 ⊕ Fin (n-1)
  let e₃ : ({i // i = i₀} ⊕ {i // i ≠ i₀}) ≃o Fin 1 ⊕ Fin (n-1) :=
    -- 修正 6: 使用 OrderIso.sumCongr
    OrderIso.sumCongr e₃_inl e₃_inr

  -- 7. 复合所有同构: ι ≃o Fin n ≃o Fin 1 ⊕ Fin (n-1) ≃o {i₀} ⊕ {i≠i₀}
  e₁.trans (e₂.trans e₃.symm)

end MatDecompFormal.Framework
