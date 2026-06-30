/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Hessenberg.Boundary
import Mathlib.LinearAlgebra.Matrix.Swap

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Concrete Hessenberg Boundary Step

This file discharges the boundary-column step oracle over a division ring. The
step is intentionally minimal: choose a nonzero entry of the active boundary
column, swap it to the head, then use a lower block factor to clear every tail
entry. The rest of the Hessenberg proof still runs through the boundary descent
driver in `Boundary.lean`.
-/

section PlainColumnStep

variable {R : Type v} [DivisionRing R]
variable {β : Type u} [Fintype β] [DecidableEq β]

/-- Head entry of a head-tail column as a `1 × 1` block. -/
noncomputable def hessenbergColumnHead
    (c : Matrix (Unit ⊕ β) Unit R) : Matrix Unit Unit R :=
  fun _ _ => c (Sum.inl ()) ()

/-- Tail entries of a head-tail column. -/
noncomputable def hessenbergColumnTail
    (c : Matrix (Unit ⊕ β) Unit R) : Matrix β Unit R :=
  fun i _ => c (Sum.inr i) ()

/-- Inverse of the head entry, as a `1 × 1` block. -/
noncomputable def hessenbergColumnHeadInv
    (c : Matrix (Unit ⊕ β) Unit R) : Matrix Unit Unit R :=
  fun _ _ => (c (Sum.inl ()) ())⁻¹

/-- Lower block factor that scales the head and clears the tail of a column. -/
noncomputable def hessenbergColumnClearPinv
    (c : Matrix (Unit ⊕ β) Unit R) : Matrix (Unit ⊕ β) (Unit ⊕ β) R :=
  let H : Matrix Unit Unit R := hessenbergColumnHeadInv c
  fromBlocks H 0 (-(hessenbergColumnTail c * H)) 1

/-- Explicit inverse of `hessenbergColumnClearPinv`. -/
noncomputable def hessenbergColumnClearP
    (c : Matrix (Unit ⊕ β) Unit R) : Matrix (Unit ⊕ β) (Unit ⊕ β) R :=
  fromBlocks (hessenbergColumnHead c) 0 (hessenbergColumnTail c) 1

omit [Fintype β] [DecidableEq β] in
lemma hessenbergColumnHeadInv_mul_head
    (c : Matrix (Unit ⊕ β) Unit R)
    (h : c (Sum.inl ()) () ≠ 0) :
    hessenbergColumnHeadInv c * hessenbergColumnHead c = 1 := by
  ext i j
  cases i
  cases j
  simp [Matrix.mul_apply, hessenbergColumnHeadInv, hessenbergColumnHead, h]

omit [Fintype β] [DecidableEq β] in
lemma hessenbergColumnHead_mul_inv
    (c : Matrix (Unit ⊕ β) Unit R)
    (h : c (Sum.inl ()) () ≠ 0) :
    hessenbergColumnHead c * hessenbergColumnHeadInv c = 1 := by
  ext i j
  cases i
  cases j
  simp [Matrix.mul_apply, hessenbergColumnHeadInv, hessenbergColumnHead, h]

/-- The column-clearing factor has the displayed inverse. -/
lemma hessenbergColumnClear_inverse
    (c : Matrix (Unit ⊕ β) Unit R)
    (h : c (Sum.inl ()) () ≠ 0) :
    HasMatrixInverse (hessenbergColumnClearP c) (hessenbergColumnClearPinv c) := by
  constructor
  · have h21 :
        -(hessenbergColumnTail c * hessenbergColumnHeadInv c *
            hessenbergColumnHead c) + hessenbergColumnTail c = 0 := by
      rw [Matrix.mul_assoc, hessenbergColumnHeadInv_mul_head c h, Matrix.mul_one]
      simp
    simp [hessenbergColumnClearPinv, hessenbergColumnClearP, fromBlocks_multiply,
      hessenbergColumnHeadInv_mul_head c h, h21]
  · simp [hessenbergColumnClearPinv, hessenbergColumnClearP, fromBlocks_multiply,
      hessenbergColumnHead_mul_inv c h]

/-- After column clearing, all tail entries vanish. -/
lemma hessenbergColumnClear_tail_zero
    (c : Matrix (Unit ⊕ β) Unit R)
    (h : c (Sum.inl ()) () ≠ 0) (i : β) :
    (hessenbergColumnClearPinv c * c) (Sum.inr i) () = 0 := by
  have htail :
      (∑ x : β, (1 : Matrix β β R) i x * c (Sum.inr x) ()) =
        c (Sum.inr i) () := by
    have hmat :
        (1 : Matrix β β R) * hessenbergColumnTail c =
          hessenbergColumnTail c := by
      simp
    have happ := congrFun₂ hmat i ()
    simpa [hessenbergColumnTail, Matrix.mul_apply] using happ
  simp [hessenbergColumnClearPinv, hessenbergColumnTail, hessenbergColumnHeadInv,
    Matrix.mul_apply, h, htail]

/-- A nonzero head-tail column has a chosen nonzero row, defaulting to the head if zero. -/
noncomputable def hessenbergFirstNonzeroOrHead
    (c : Matrix (Unit ⊕ β) Unit R) : Unit ⊕ β := by
  classical
  exact
    if h : c = 0 then Sum.inl ()
    else
      Classical.choose
        (by
          by_contra hnone
          apply h
          ext i j
          cases j
          by_contra hz
          exact hnone ⟨i, hz⟩)

omit [DecidableEq β] in
lemma hessenbergFirstNonzeroOrHead_ne_zero
    (c : Matrix (Unit ⊕ β) Unit R) (h : c ≠ 0) :
    c (hessenbergFirstNonzeroOrHead c) () ≠ 0 := by
  classical
  let w : ∃ i : Unit ⊕ β, c i () ≠ 0 := by
    by_contra hnone
    apply h
    ext i j
    cases j
    by_contra hz
    exact hnone ⟨i, hz⟩
  have hp : hessenbergFirstNonzeroOrHead c = Classical.choose w := by
    simp [hessenbergFirstNonzeroOrHead, h]
  rw [hp]
  exact Classical.choose_spec w

/-- Same-index inverse-side factor for a plain head-tail boundary column. -/
noncomputable def hessenbergPlainStepPinv
    (c : Matrix (Unit ⊕ β) Unit R) : Matrix (Unit ⊕ β) (Unit ⊕ β) R := by
  classical
  exact
    if h : c = 0 then 1
    else
      hessenbergColumnClearPinv
          (Matrix.swap R (Sum.inl ()) (hessenbergFirstNonzeroOrHead c) * c) *
        Matrix.swap R (Sum.inl ()) (hessenbergFirstNonzeroOrHead c)

/-- Same-index inverse of `hessenbergPlainStepPinv`. -/
noncomputable def hessenbergPlainStepP
    (c : Matrix (Unit ⊕ β) Unit R) : Matrix (Unit ⊕ β) (Unit ⊕ β) R := by
  classical
  exact
    if h : c = 0 then 1
    else
      Matrix.swap R (Sum.inl ()) (hessenbergFirstNonzeroOrHead c) *
        hessenbergColumnClearP
          (Matrix.swap R (Sum.inl ()) (hessenbergFirstNonzeroOrHead c) * c)

/-- The plain head-tail column step is invertible. -/
lemma hessenbergPlainStep_inverse
    (c : Matrix (Unit ⊕ β) Unit R) :
    HasMatrixInverse (hessenbergPlainStepP c) (hessenbergPlainStepPinv c) := by
  classical
  by_cases hc : c = 0
  · constructor <;> simp [hessenbergPlainStepP, hessenbergPlainStepPinv, hc]
  · let S : Matrix (Unit ⊕ β) (Unit ⊕ β) R :=
      Matrix.swap R (Sum.inl ()) (hessenbergFirstNonzeroOrHead c)
    let cs : Matrix (Unit ⊕ β) Unit R := S * c
    have hhead : cs (Sum.inl ()) () ≠ 0 := by
      have hswap :
          (S * c) (Sum.inl ()) () =
            c (hessenbergFirstNonzeroOrHead c) () := by
        simpa [S] using
          (Matrix.swap_mul_apply_left
            (i := Sum.inl ()) (j := hessenbergFirstNonzeroOrHead c)
            (a := ()) (g := c))
      exact hswap.trans_ne (hessenbergFirstNonzeroOrHead_ne_zero c hc)
    have hclear := hessenbergColumnClear_inverse cs hhead
    constructor
    · calc
        hessenbergPlainStepPinv c * hessenbergPlainStepP c =
            (hessenbergColumnClearPinv cs * S) *
              (S * hessenbergColumnClearP cs) := by
              simp [hessenbergPlainStepPinv, hessenbergPlainStepP, hc, S, cs,
                Matrix.mul_assoc]
        _ = hessenbergColumnClearPinv cs * (S * S) *
              hessenbergColumnClearP cs := by
              simp [Matrix.mul_assoc]
        _ = hessenbergColumnClearPinv cs * hessenbergColumnClearP cs := by
              rw [Matrix.swap_mul_self]
              simp
        _ = 1 := hclear.1
    · calc
        hessenbergPlainStepP c * hessenbergPlainStepPinv c =
            (S * hessenbergColumnClearP cs) *
              (hessenbergColumnClearPinv cs * S) := by
              simp [hessenbergPlainStepPinv, hessenbergPlainStepP, hc, S, cs,
                Matrix.mul_assoc]
        _ = S * (hessenbergColumnClearP cs *
              hessenbergColumnClearPinv cs) * S := by
              simp [Matrix.mul_assoc]
        _ = S * S := by
              rw [hclear.2]
              simp
        _ = 1 := Matrix.swap_mul_self
          (R := R) (Sum.inl ()) (hessenbergFirstNonzeroOrHead c)

/-- The plain step makes the boundary column ready. -/
lemma hessenbergPlainStep_ready
    (c : Matrix (Unit ⊕ β) Unit R) :
    ∀ i : β, (hessenbergPlainStepPinv c * c) (Sum.inr i) () = 0 := by
  classical
  by_cases hc : c = 0
  · intro i
    simp [hessenbergPlainStepPinv, hc]
  · let S : Matrix (Unit ⊕ β) (Unit ⊕ β) R :=
      Matrix.swap R (Sum.inl ()) (hessenbergFirstNonzeroOrHead c)
    let cs : Matrix (Unit ⊕ β) Unit R := S * c
    have hhead : cs (Sum.inl ()) () ≠ 0 := by
      have hswap :
          (S * c) (Sum.inl ()) () =
            c (hessenbergFirstNonzeroOrHead c) () := by
        simpa [S] using
          (Matrix.swap_mul_apply_left
            (i := Sum.inl ()) (j := hessenbergFirstNonzeroOrHead c)
            (a := ()) (g := c))
      exact hswap.trans_ne (hessenbergFirstNonzeroOrHead_ne_zero c hc)
    intro i
    simpa [hessenbergPlainStepPinv, hc, S, cs, Matrix.mul_assoc] using
      hessenbergColumnClear_tail_zero cs hhead i

end PlainColumnStep

section BoundaryStep

variable {R : Type v} [DivisionRing R]

/-- Boundary inverse-side step factor, obtained by reindexing to head-tail form. -/
noncomputable def hessenbergBoundaryStepPinv
    (x_sub : PosHessenbergBoundaryUniverse.{u} R) :
    Matrix x_sub.1.ι x_sub.1.ι R := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  let e := headTailEquiv (α := x_sub.1.ι)
  exact Matrix.reindex e.symm e.symm
    (hessenbergPlainStepPinv (Matrix.reindex e (Equiv.refl Unit) x_sub.1.c))

/-- Explicit inverse of `hessenbergBoundaryStepPinv`. -/
noncomputable def hessenbergBoundaryStepP
    (x_sub : PosHessenbergBoundaryUniverse.{u} R) :
    Matrix x_sub.1.ι x_sub.1.ι R := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  let e := headTailEquiv (α := x_sub.1.ι)
  exact Matrix.reindex e.symm e.symm
    (hessenbergPlainStepP (Matrix.reindex e (Equiv.refl Unit) x_sub.1.c))

/-- The concrete boundary step has a two-sided inverse. -/
lemma hessenbergBoundaryStep_inverse
    (x_sub : PosHessenbergBoundaryUniverse.{u} R) :
    HasMatrixInverse (hessenbergBoundaryStepP x_sub)
      (hessenbergBoundaryStepPinv x_sub) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  let e := headTailEquiv (α := x_sub.1.ι)
  simpa [hessenbergBoundaryStepP, hessenbergBoundaryStepPinv, e] using
    hasMatrixInverse_reindex e.symm
      (hessenbergPlainStep_inverse
        (Matrix.reindex e (Equiv.refl Unit) x_sub.1.c))

/-- The concrete boundary step makes the transformed boundary column ready. -/
lemma hessenbergBoundaryStep_ready
    (x_sub : PosHessenbergBoundaryUniverse.{u} R) :
    HessenbergBoundaryReady
      (hessenbergBoundarySimilarityObject
        (x_sub : HessenbergBoundaryUniverse.{u} R)
        (hessenbergBoundaryStepP x_sub) (hessenbergBoundaryStepPinv x_sub)) := by
  intro _h i hi
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  let e := headTailEquiv (α := x_sub.1.ι)
  let cplain : Matrix (Unit ⊕ HessenbergTailIdx x_sub.1.ι) Unit R :=
    Matrix.reindex e (Equiv.refl Unit) x_sub.1.c
  have hplain := hessenbergPlainStep_ready cplain ⟨i, hi⟩
  have hmul := reindex_mul_column e (hessenbergPlainStepPinv cplain) x_sub.1.c
  have happ := congrFun₂ hmul i ()
  have hentry :
      (Matrix.reindex e.symm (Equiv.refl Unit)
          (hessenbergPlainStepPinv cplain *
            Matrix.reindex e (Equiv.refl Unit) x_sub.1.c)) i () =
        (hessenbergPlainStepPinv cplain * cplain) (e i) () := by
    rfl
  have hei : e i = Sum.inr ⟨i, hi⟩ := by
    simpa [e] using headTailEquiv_apply_tail (α := x_sub.1.ι) ⟨i, hi⟩
  calc
    (hessenbergBoundarySimilarityObject
        (x_sub : HessenbergBoundaryUniverse.{u} R)
        (hessenbergBoundaryStepP x_sub) (hessenbergBoundaryStepPinv x_sub)).c i () =
        (hessenbergBoundaryStepPinv x_sub * x_sub.1.c) i () := by
          rfl
    _ =
        ((Matrix.reindex e.symm e.symm (hessenbergPlainStepPinv cplain)) *
          x_sub.1.c) i () := by
          simp [hessenbergBoundaryStepPinv, e, cplain]
    _ =
        (Matrix.reindex e.symm (Equiv.refl Unit)
          (hessenbergPlainStepPinv cplain *
            Matrix.reindex e (Equiv.refl Unit) x_sub.1.c)) i () := by
          exact happ.symm
    _ = (hessenbergPlainStepPinv cplain * cplain) (e i) () := hentry
    _ = 0 := by
          rw [hei]
          exact hplain

/-- Concrete boundary-column step oracle over a division ring. -/
noncomputable def hessenbergBoundaryStepOracle_divisionRing
    (R : Type v) [DivisionRing R] :
    HessenbergBoundaryStepOracle.{u, v} R where
  P := hessenbergBoundaryStepP
  Pinv := hessenbergBoundaryStepPinv
  inverse_P := hessenbergBoundaryStep_inverse
  ready := hessenbergBoundaryStep_ready

/--
Oracle-free Hessenberg reduction over a division ring, routed through the
boundary-column descent driver.
-/
theorem exists_hessenberg_reduction_divisionRing
    {R : Type v} [DivisionRing R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) :
    HasHessenberg A :=
  exists_hessenberg_reduction_boundary_framework
    (hessenbergBoundaryStepOracle_divisionRing R) A

/--
Primary plan-facing Hessenberg reduction theorem. The assumption is kept at
`[DivisionRing R]`, so it applies in particular over every field without
defaulting to `ℝ` or `ℂ`.
-/
theorem exists_hessenberg_reduction
    {R : Type v} [DivisionRing R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) :
    HasHessenberg A :=
  exists_hessenberg_reduction_divisionRing A

end BoundaryStep

end MatDecompFormal.Instances
