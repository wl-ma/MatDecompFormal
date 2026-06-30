/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Framework.UniverseDecomposition

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Hessenberg Details

This file contains the scalar-parametric target predicate for upper Hessenberg
reduction and the basic similarity transport lemma used by the descent driver.
-/

/-- Order rank of an index in a finite linear order. -/
noncomputable def finiteOrderRank (ι : Type*) [Fintype ι] [LinearOrder ι] (i : ι) : Nat :=
  Fintype.card { j : ι // j < i }

/--
Upper Hessenberg zero pattern: entries strictly below the first subdiagonal
vanish. The condition is phrased using the finite-order rank so it works for
arbitrary finite linearly ordered index types.
-/
def IsUpperHessenberg
    {ι R : Type*} [Fintype ι] [LinearOrder ι] [Zero R]
    (H : Matrix ι ι R) : Prop :=
  ∀ i j, finiteOrderRank ι j + 1 < finiteOrderRank ι i → H i j = 0

/-- A two-sided inverse witness for a square matrix. -/
def HasMatrixInverse
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    (P Pinv : Matrix ι ι R) : Prop :=
  Pinv * P = 1 ∧ P * Pinv = 1

/--
Hessenberg reduction target: `A` is similar to an upper Hessenberg matrix.

The target is stated over a semiring with an explicit inverse witness rather
than using a field-level matrix inverse operation. The step oracle can later
construct these witnesses from elementary field transformations.
-/
def HasHessenberg
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Semiring R]
    (A : Matrix ι ι R) : Prop :=
  ∃ P : Matrix ι ι R, ∃ Pinv : Matrix ι ι R, ∃ H : Matrix ι ι R,
    HasMatrixInverse P Pinv ∧
    IsUpperHessenberg H ∧
    A = P * H * Pinv

/-- Universe-level Hessenberg predicate used by the square subtype driver. -/
def Hessenberg_P {R : Type*} [Semiring R] (x : SquareUniverse R) : Prop :=
  HasHessenberg x.A

/--
Boundary-column universe for the oracle-free Hessenberg descent.

The extra column records the parent lower-left boundary column. A tail
similarity acts on both the tail matrix and this boundary column, which is the
invariant missing from the plain square-universe recursion.
-/
structure HessenbergBoundaryUniverse (R : Type*) where
  ι : Type u
  [fintype_ι : Fintype ι]
  [decEq_ι : DecidableEq ι]
  [linOrder_ι : LinearOrder ι]
  A : Matrix ι ι R
  c : Matrix ι Unit R

attribute [instance] HessenbergBoundaryUniverse.fintype_ι
attribute [instance] HessenbergBoundaryUniverse.decEq_ι
attribute [instance] HessenbergBoundaryUniverse.linOrder_ι

namespace HessenbergBoundaryUniverse

@[simp] def ofMatrixColumn {R : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) (c : Matrix ι Unit R) : HessenbergBoundaryUniverse R :=
  { ι := ι, A := A, c := c }

end HessenbergBoundaryUniverse

/-- Positive-dimensional boundary universes. -/
abbrev PosHessenbergBoundaryUniverse (R : Type*) :=
  { x : HessenbergBoundaryUniverse.{u} R // 0 < Fintype.card x.ι }

/--
Boundary-aware Hessenberg target.

Besides reducing `A` to Hessenberg form, the same similarity must transform the
boundary column into a first-entry-only shape. This is the invariant needed for
concrete recursive lifting.
-/
def HasHessenbergBoundary
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] [Semiring R]
    (A : Matrix ι ι R) (c : Matrix ι Unit R) : Prop :=
  ∃ P : Matrix ι ι R, ∃ Pinv : Matrix ι ι R, ∃ H : Matrix ι ι R,
    HasMatrixInverse P Pinv ∧
    IsUpperHessenberg H ∧
    A = P * H * Pinv ∧
    ∀ i : ι, i ≠ headElem (α := ι) → (Pinv * c) i () = 0

/-- Boundary-universe target predicate. -/
def HessenbergBoundary_P {R : Type*} [Semiring R]
    (x : HessenbergBoundaryUniverse R) : Prop :=
  ∀ (_h : Nonempty x.ι), @HasHessenbergBoundary x.ι R x.fintype_ι x.decEq_ι
    x.linOrder_ι _h _ x.A x.c

lemma isUpperHessenberg_subsingleton
    {ι R : Type*} [Fintype ι] [LinearOrder ι] [Zero R] [Subsingleton ι]
    (H : Matrix ι ι R) :
    IsUpperHessenberg H := by
  intro i j hij
  have hji : j = i := Subsingleton.elim j i
  rw [hji] at hij
  have hlt_self : finiteOrderRank ι i < finiteOrderRank ι i :=
    lt_trans (Nat.lt_succ_self _) hij
  exact False.elim (Nat.lt_irrefl _ hlt_self)

/-- Subsingleton matrices have the trivial Hessenberg decomposition. -/
theorem base_hessenberg_subsingleton
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Semiring R]
    [Subsingleton ι] (A : Matrix ι ι R) :
    HasHessenberg A := by
  refine ⟨1, 1, A, ?_, ?_, ?_⟩
  · constructor <;> simp
  · exact isUpperHessenberg_subsingleton A
  · simp

/-- Subsingleton matrices with a zero boundary column satisfy the boundary target. -/
theorem base_hessenbergBoundary_subsingleton
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Semiring R] [Subsingleton ι] (A : Matrix ι ι R) :
    HasHessenbergBoundary A (0 : Matrix ι Unit R) := by
  refine ⟨1, 1, A, ?_, ?_, ?_, ?_⟩
  · constructor <;> simp
  · exact isUpperHessenberg_subsingleton A
  · simp
  · intro i hi
    exact False.elim (hi (Subsingleton.elim _ _))

/--
Transport a Hessenberg witness backward across an invertible similarity.

If `B = Pinv * A * P` and `B` is Hessenberg-similar, then so is `A`.
-/
theorem hessenberg_transport_similarity
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Semiring R]
    (P Pinv : Matrix ι ι R) (A B : Matrix ι ι R)
    (hInv : HasMatrixInverse P Pinv)
    (hB : B = Pinv * A * P)
    (hHess : HasHessenberg B) :
    HasHessenberg A := by
  rcases hHess with ⟨S, Sinv, H, hSInv, hH, hEqB⟩
  refine ⟨P * S, Sinv * Pinv, H, ?_, hH, ?_⟩
  · constructor
    · calc
        (Sinv * Pinv) * (P * S) = Sinv * (Pinv * P) * S := by
          simp [Matrix.mul_assoc]
        _ = Sinv * S := by
          rw [hInv.1]
          simp
        _ = 1 := hSInv.1
    · calc
        (P * S) * (Sinv * Pinv) = P * (S * Sinv) * Pinv := by
          simp [Matrix.mul_assoc]
        _ = P * Pinv := by
          rw [hSInv.2]
          simp
        _ = 1 := hInv.2
  · have hA_back : A = P * B * Pinv := by
      calc
        A = (P * Pinv) * A * (P * Pinv) := by
          simp [hInv.2]
        _ = P * (Pinv * A * P) * Pinv := by
          simp [Matrix.mul_assoc]
        _ = P * B * Pinv := by
          rw [← hB]
    calc
      A = P * B * Pinv := hA_back
      _ = P * (S * H * Sinv) * Pinv := by
        rw [hEqB]
      _ = (P * S) * H * (Sinv * Pinv) := by
        simp [Matrix.mul_assoc]

end MatDecompFormal.Instances
