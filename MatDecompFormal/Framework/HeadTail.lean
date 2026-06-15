import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Sum.Order

namespace MatDecompFormal.Framework

open Equiv
open Sum.Lex

section HeadTail

variable {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α]

noncomputable def headElem : α := by
  classical
  exact Finset.min' Finset.univ ⟨Classical.choice ‹Nonempty α›, by simp⟩

lemma headElem_le (a : α) : headElem (α := α) ≤ a := by
  classical
  exact Finset.min'_le _ a (by simp)

noncomputable def headSubtypeEquivUnit :
    { a : α // a = headElem (α := α) } ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨headElem (α := α), rfl⟩
  left_inv := by
    intro x
    rcases x with ⟨x, rfl⟩
    rfl
  right_inv := by
    intro u
    cases u
    rfl

@[simp] theorem headSubtypeEquivUnit_apply
    (x : { a : α // a = headElem (α := α) }) :
    headSubtypeEquivUnit (α := α) x = () := rfl

@[simp] theorem headSubtypeEquivUnit_symm_apply :
    (headSubtypeEquivUnit (α := α)).symm () = ⟨headElem (α := α), rfl⟩ := rfl

noncomputable def headSubtypeOrderIsoUnit :
    { a : α // a = headElem (α := α) } ≃o Unit where
  toEquiv := headSubtypeEquivUnit (α := α)
  map_rel_iff' := by
    intro x y
    simp

noncomputable def headTailEquiv :
    α ≃ Unit ⊕ { a : α // a ≠ headElem (α := α) } :=
  (Equiv.sumCompl fun a : α => a = headElem (α := α)).symm.trans
    (Equiv.sumCongr (headSubtypeEquivUnit (α := α)) (Equiv.refl _))

@[simp] theorem headTailEquiv_apply_head :
    headTailEquiv (α := α) (headElem (α := α)) = Sum.inl () := by
  simp [headTailEquiv, headElem]

@[simp] theorem headTailEquiv_apply_tail
    (x : { a : α // a ≠ headElem (α := α) }) :
    headTailEquiv (α := α) x = Sum.inr x := by
  simp [headTailEquiv]

@[simp] theorem headTailEquiv_symm_apply_inl :
    (headTailEquiv (α := α)).symm (Sum.inl ()) = headElem (α := α) := by
  change ↑((headSubtypeEquivUnit (α := α)).symm ()) = headElem (α := α)
  rfl

@[simp] theorem headTailEquiv_symm_apply_inr
    (x : { a : α // a ≠ headElem (α := α) }) :
    (headTailEquiv (α := α)).symm (Sum.inr x) = x := by
  simp [headTailEquiv]

noncomputable def sumToLexEquiv (β γ : Type*) : β ⊕ γ ≃ β ⊕ₗ γ where
  toFun := toLex
  invFun := ofLex
  left_inv := by
    intro x
    cases x
    · rfl
    · rfl
  right_inv := by
    intro x
    rfl

@[simp] theorem sumToLexEquiv_symm_apply_inl {β γ : Type*} (x : β) :
    (sumToLexEquiv β γ).symm (Sum.inlₗ x) = Sum.inl x := rfl

@[simp] theorem sumToLexEquiv_symm_apply_inr {β γ : Type*} (x : γ) :
    (sumToLexEquiv β γ).symm (Sum.inrₗ x) = Sum.inr x := rfl

@[simp] theorem sumToLexEquiv_symm_apply_inl_raw {β γ : Type*} (x : β) :
    (sumToLexEquiv β γ).symm (Sum.inl x : β ⊕ₗ γ) = Sum.inl x := rfl

@[simp] theorem sumToLexEquiv_symm_apply_inr_raw {β γ : Type*} (x : γ) :
    (sumToLexEquiv β γ).symm (Sum.inr x : β ⊕ₗ γ) = Sum.inr x := rfl

lemma sumToLexEquiv_strictMono {β γ : Type*} [Preorder β] [Preorder γ] :
    StrictMono (sumToLexEquiv β γ) := by
  intro x y hxy
  rcases x with (_ | x) <;> rcases y with (_ | y)
  · exact Sum.Lex.inl (Sum.inl_lt_inl_iff.mp hxy)
  · exact (Sum.not_inl_lt_inr hxy).elim
  · exact (Sum.not_inr_lt_inl hxy).elim
  · exact Sum.Lex.inr (Sum.inr_lt_inr_iff.mp hxy)

noncomputable def headTailLexEquiv :
    α ≃ Unit ⊕ₗ { a : α // a ≠ headElem (α := α) } :=
  (headTailEquiv (α := α)).trans (sumToLexEquiv Unit { a : α // a ≠ headElem (α := α) })

@[simp] theorem headTailLexEquiv_apply_head :
    headTailLexEquiv (α := α) (headElem (α := α)) = Sum.inlₗ () := by
  simp [headTailLexEquiv, sumToLexEquiv]

@[simp] theorem headTailLexEquiv_apply_tail
    (x : { a : α // a ≠ headElem (α := α) }) :
    headTailLexEquiv (α := α) x = Sum.inrₗ x := by
  simp [headTailLexEquiv, sumToLexEquiv]

@[simp] theorem headTailLexEquiv_symm_apply_inl :
    (headTailLexEquiv (α := α)).symm (Sum.inlₗ ()) = headElem (α := α) := by
  rfl

@[simp] theorem headTailLexEquiv_symm_apply_inr
    (x : { a : α // a ≠ headElem (α := α) }) :
    (headTailLexEquiv (α := α)).symm (Sum.inrₗ x) = x := by
  rfl

lemma headTailLexEquiv_strictMono : StrictMono (headTailLexEquiv (α := α)) := by
  intro a b hab
  by_cases ha : a = headElem (α := α)
  · subst ha
    have hb : b ≠ headElem (α := α) := by
      intro h
      subst h
      exact lt_irrefl _ hab
    rw [headTailLexEquiv_apply_head, headTailLexEquiv_apply_tail ⟨b, hb⟩]
    exact inl_lt_inr () ((⟨b, hb⟩ : { a : α // a ≠ headElem (α := α) }))
  · have hb : b ≠ headElem (α := α) := by
      intro h
      subst h
      exact not_lt_of_ge (headElem_le (α := α) a) hab
    have hab_sub : (⟨a, ha⟩ : { a : α // a ≠ headElem (α := α) }) < ⟨b, hb⟩ := hab
    rw [headTailLexEquiv_apply_tail ⟨a, ha⟩, headTailLexEquiv_apply_tail ⟨b, hb⟩]
    simpa using hab_sub

end HeadTail

end MatDecompFormal.Framework
