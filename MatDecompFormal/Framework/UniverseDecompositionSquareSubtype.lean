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

end MatDecompFormal.Framework
