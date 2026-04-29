import Mathlib.Order.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Algebra.Ring.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Block


namespace MatDecompFormal.Framework
open Matrix


/-!
### Fin n Utilities

This section defines project-specific higher-level `Fin n` equivalences built on
basic `Mathlib` tools.
These are framework-specific glue code used to simplify proofs in `Components`.
-/

/--
An equivalence specialized for splitting `Fin (n + 1)` into `Fin 1 ⊕ Fin n`.
This definition is computational: it is constructed by pattern matching
(`Fin.cases`) rather than type casts (`cast`), so it works well with Lean’s
`simp` automation.

- `0` maps to `Sum.inl 0`.
- `i.succ` maps to `Sum.inr i`.
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
  -- Reuse the toFun / invFun from finSuccEquivSum.
  -- Note that the codomain is changed to ⊕ₗ
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

/-- Strict monotonicity of `finSuccEquivSumLex`. -/
lemma finSuccEquivSumLex_strictMono (k : ℕ) :
    StrictMono (finSuccEquivSumLex k) := by
  intro x y hxy
  cases x using Fin.cases with
  | zero =>
      cases y using Fin.cases with
      | zero =>
          exact (lt_irrefl _ hxy).elim
      | succ y_val =>
          -- `e 0 = inl 0`, `e (succ y) = inr y`
          -- and `inl _ < inr _` for lex order
          simp [finSuccEquivSumLex]
          apply Sum.Lex.inl_lt_inr
  | succ x_val =>
      cases y using Fin.cases with
      | zero =>
          exact (not_lt_of_ge (Fin.zero_le _) hxy).elim
      | succ y_val =>
          -- `inr x < inr y` iff `x < y`
          have : x_val < y_val := (Fin.succ_lt_succ_iff.mp hxy)
          simp [finSuccEquivSumLex]
          exact Sum.Lex.inr_lt_inr_iff.mpr this

/--
An equivalence for viewing `Fin n` as `Fin 0 ⊕ Fin n`.
This definition is computational: it directly maps every element `i` of
`Fin n` to `Sum.inr i`.

This is useful when a trivial row or column block split is needed to fit the
`fromBlocks` API, for example in `ZeroColumnMethod`.
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
A key glue lemma proving that slicing through `Fin.succ` is equivalent to
taking `toBlocks₂₂` after reindexing by `finSuccEquivSum`.
-/
lemma submatrix_succ_eq_toBlocks₂₂ {n m : ℕ} {R : Type*}
    (A : Matrix (Fin (n + 1)) (Fin (m + 1)) R) :
    A.submatrix Fin.succ Fin.succ =
      (reindex (finSuccEquivSum n) (finSuccEquivSum m) A).toBlocks₂₂ := by
  rfl

end MatDecompFormal.Framework
