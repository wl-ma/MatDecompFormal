import MatDecompFormal.Framework.Universe

namespace MatDecompFormal.Framework

open Matrix

/-!
# Universe Decomposition Fin Square Subtype Support

This file contains the square-`Fin` support layer used by the universe
decomposition driver:

1. square cast tools;
2. square subtype predicate/measure glue.

It does not define the induction driver packaging itself.
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
  cases h₁
  cases h₂
  rfl

lemma castSq_trans {m n p : ℕ} (h₁ : m = n) (h₂ : n = p) (A : Matrix (Fin m) (Fin m) R) :
    castSq (R := R) h₂ (castSq (R := R) h₁ A) = castSq (R := R) (h₁.trans h₂) A := by
  cases h₁
  cases h₂
  rfl

@[simp] lemma castSq_symm {m n : ℕ} (h : m = n) (A : Matrix (Fin m) (Fin m) R) :
    castSq (R := R) h.symm (castSq (R := R) h A) = A := by
  cases h
  rfl

/--
Any square-matrix predicate family is invariant under `castSq`.
-/
theorem squarePred_castSq_iff
    {Q : {n : ℕ} → Matrix (Fin n) (Fin n) R → Prop}
    {n n' : ℕ} (h : n = n') (A : Matrix (Fin n) (Fin n) R) :
    Q (castSq (R := R) h A) ↔ Q A := by
  cases h
  simp [castSq]

/--
For `n > 0`, cast `n × n` to `(n - 1 + 1) × (n - 1 + 1)`.
-/
def castToPredSucc {n : ℕ} (hn : n > 0) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin ((n - 1) + 1)) (Fin ((n - 1) + 1)) R := by
  cases n with
  | zero =>
      exact (False.elim ((lt_irrefl 0) hn))
  | succ k =>
      simpa using A

@[simp] lemma castToPredSucc_succ (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    castToPredSucc (R := R) (n := k + 1) (Nat.succ_pos _) A = A := by
  simp [castToPredSucc]

/--
For `n > 0`, `castToPredSucc` cancels the cast from `(n - 1 + 1)` to `n`.
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
      simp [castToPredSucc, castSq]

/--
Any square-matrix predicate family is invariant under the positive-square
subtype cast `n ↦ (n - 1) + 1`.
-/
theorem squarePred_castToPredSucc_iff
    {Q : {n : ℕ} → Matrix (Fin n) (Fin n) R → Prop}
    {n : ℕ} (hn : n > 0) (A : Matrix (Fin n) (Fin n) R) :
    Q (castToPredSucc (R := R) hn A) ↔ Q A := by
  cases n with
  | zero =>
      exact (False.elim ((lt_irrefl 0) hn))
  | succ k =>
      simp [castToPredSucc]

end CastTools

section SquareSubtypeGlue

variable {R : Type*}

/-- The standard square-universe measure: matrix dimension. -/
abbrev squareSubtypeμ (x : FinSqUniverse R) : Nat :=
  x.1

/-- The standard square subtype induction base measure. -/
abbrev squareSubtypeμBase : Nat := 0

/-- Lift a matrix-level square predicate family to the square universe. -/
abbrev squareSubtypeP
    (Q : {n : ℕ} → Matrix (Fin n) (Fin n) R → Prop)
    (x : FinSqUniverse R) : Prop :=
  Q x.2.A

/-- Lift a matrix-level square predicate family to the positive square subtype. -/
abbrev squareSubtypePSub
    (Q : {n : ℕ} → Matrix (Fin n) (Fin n) R → Prop)
    (x : PosFinSqUniverse R) : Prop :=
  Q x.val.2.A

/--
The universe-level and subtype-level square predicate wrappers are
definitionally compatible.
-/
theorem squareSubtypePCompat
    (Q : {n : ℕ} → Matrix (Fin n) (Fin n) R → Prop)
    (x : PosFinSqUniverse R) :
    squareSubtypePSub (R := R) Q x ↔ squareSubtypeP (R := R) Q x.val := by
  rfl

/--
Cast a positive-dimensional square-universe object into the `(n - 1) + 1`
world used by square subtype recursion.
-/
@[simp] def posSqCastToPredSucc (x : PosFinSqUniverse R) :
    Matrix (Fin ((x.val.1 - 1) + 1)) (Fin ((x.val.1 - 1) + 1)) R :=
  castToPredSucc (R := R) x.property x.val.2.A

/--
Package a `(k + 1) × (k + 1)` predicate as a subtype predicate on positive
square universe objects.
-/
abbrev squareSubtypeIsSliceable
    (Pred : ∀ k : ℕ, Matrix (Fin (k + 1)) (Fin (k + 1)) R → Prop)
    (x : PosFinSqUniverse R) : Prop :=
  Pred (x.val.1 - 1) (posSqCastToPredSucc (R := R) x)

/--
Package a `(k + 1) ↦ k` slice operator as a square-universe slice on positive
square objects.
-/
noncomputable def squareSubtypeSlice
    (Pred : ∀ k : ℕ, Matrix (Fin (k + 1)) (Fin (k + 1)) R → Prop)
    (slice :
      ∀ k : ℕ, (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) →
        Pred k A → Matrix (Fin k) (Fin k) R)
    (x : PosFinSqUniverse R)
    (hx : squareSubtypeIsSliceable (R := R) Pred x) : FinSqUniverse R :=
  let k : ℕ := x.val.1 - 1
  ⟨k, ⟨slice k (posSqCastToPredSucc (R := R) x) hx⟩⟩

/--
Cast-wrapper for square subtype lifting: move into the `(n - 1) + 1` world,
apply the matrix-level lifting theorem there, then transport the result back.
-/
theorem squareSubtypeLiftFromSlice
    (Pred : ∀ k : ℕ, Matrix (Fin (k + 1)) (Fin (k + 1)) R → Prop)
    (slice :
      ∀ k : ℕ, (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) →
        Pred k A → Matrix (Fin k) (Fin k) R)
    (Q : {n : ℕ} → Matrix (Fin n) (Fin n) R → Prop)
    (lift :
      ∀ k : ℕ, (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) →
        (hA : Pred k A) → Q (slice k A hA) → Q A)
    (cast_iff :
      ∀ {n : ℕ} (hn : n > 0) (A : Matrix (Fin n) (Fin n) R),
        Q (castToPredSucc (R := R) hn A) ↔ Q A)
    (x : PosFinSqUniverse R)
    (hx : squareSubtypeIsSliceable (R := R) Pred x)
    (hSlice : Q (slice (x.val.1 - 1) (posSqCastToPredSucc (R := R) x) hx)) :
    Q x.val.2.A := by
  have h_cast : Q (posSqCastToPredSucc (R := R) x) :=
    lift (x.val.1 - 1) (posSqCastToPredSucc (R := R) x) hx hSlice
  exact (cast_iff x.property x.val.2.A).1 (by simpa [posSqCastToPredSucc] using h_cast)

/--
Framework-level zero-dimensional base skeleton for square subtype induction.
-/
theorem squareSubtypeBaseDimEqZero
    (x : FinSqUniverse R)
    (hx :
      (∀ x_sub : PosFinSqUniverse R, (x_sub : FinSqUniverse R) ≠ x) ∨
        squareSubtypeμ (R := R) x ≤ squareSubtypeμBase) :
    x.1 = 0 := by
  cases hx with
  | inl hnot =>
      by_contra hn0
      have hnpos : x.1 > 0 := Nat.pos_of_ne_zero hn0
      let x_sub : PosFinSqUniverse R := ⟨x, hnpos⟩
      exact hnot x_sub rfl
  | inr hle =>
      exact Nat.eq_zero_of_le_zero hle

end SquareSubtypeGlue

end MatDecompFormal.Framework
