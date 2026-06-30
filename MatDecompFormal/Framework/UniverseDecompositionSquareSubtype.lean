/-
Copyright (c) 2026 Wanli Ma, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanli Ma, Zichen Wang
-/
import MatDecompFormal.Framework.Universe

namespace MatDecompFormal.Framework

/-!
# Universe Decomposition Square Subtype Support

This file contains the square-subtype support layer used by the universe
decomposition driver. It only keeps the universe-level measure and the
zero-dimensional base fact.
-/

variable {R : Type*}

/-- The standard square-universe measure: matrix dimension. -/
abbrev squareSubtypeμ (x : SquareUniverse R) : Nat :=
  Fintype.card x.ι

/-- The standard square subtype induction base measure. -/
abbrev squareSubtypeμBase : Nat := 0

/-- The standard rectangular-universe measure: the smaller matrix dimension. -/
abbrev rectSubtypeμ (x : RectUniverse R) : Nat :=
  min (Fintype.card x.ι) (Fintype.card x.κ)

/-- The standard rectangular subtype induction base measure. -/
abbrev rectSubtypeμBase : Nat := 0

/--
Framework-level zero-dimensional base skeleton for square subtype induction.
-/
theorem squareSubtypeBaseDimEqZero
    (x : SquareUniverse R)
    (hx :
      (∀ x_sub : PosSquareUniverse R, (x_sub : SquareUniverse R) ≠ x) ∨
        squareSubtypeμ x ≤ squareSubtypeμBase) :
    Fintype.card x.ι = 0 := by
  cases hx with
  | inl hnot =>
      by_contra hn0
      have hnpos : Fintype.card x.ι > 0 := Nat.pos_of_ne_zero hn0
      let x_sub : PosSquareUniverse R := ⟨x, hnpos⟩
      exact hnot x_sub rfl
  | inr hle =>
      exact Nat.eq_zero_of_le_zero hle

/--
Framework-level zero-dimensional base skeleton for rectangular subtype
induction. At base measure, at least one side is empty.
-/
theorem rectSubtypeBaseDimEqZero
    (x : RectUniverse R)
    (hx :
      (∀ x_sub : PosRectUniverse R, (x_sub : RectUniverse R) ≠ x) ∨
        rectSubtypeμ x ≤ rectSubtypeμBase) :
    Fintype.card x.ι = 0 ∨ Fintype.card x.κ = 0 := by
  cases hx with
  | inl hnot =>
      by_contra hne
      rw [not_or] at hne
      have hrow : 0 < Fintype.card x.ι := Nat.pos_of_ne_zero hne.1
      have hcol : 0 < Fintype.card x.κ := Nat.pos_of_ne_zero hne.2
      let x_sub : PosRectUniverse R := ⟨x, ⟨hrow, hcol⟩⟩
      exact hnot x_sub rfl
  | inr hle =>
      have hmin : min (Fintype.card x.ι) (Fintype.card x.κ) = 0 :=
        Nat.eq_zero_of_le_zero hle
      omega

end MatDecompFormal.Framework
