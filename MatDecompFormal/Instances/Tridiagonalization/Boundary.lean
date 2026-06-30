/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Tridiagonalization.Strategy
import MatDecompFormal.Instances.Hessenberg.Boundary

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Boundary-Aware Tridiagonalization

The ordinary tail predicate is not strong enough for a concrete block lift:
a tail unitary can mix the protected first tail coordinate back into lower
entries of the parent first column.  This file records the boundary-aware target
needed by the strict descent implementation.
-/

variable {ι : Type*}

/-- A tridiagonal matrix is, in particular, upper Hessenberg. -/
theorem isUpperHessenberg_of_isTridiagonal
    [Fintype ι] [LinearOrder ι]
    {T : Matrix ι ι ℂ} (hT : IsTridiagonal T) :
    IsUpperHessenberg T := by
  intro i j hij
  exact hT i j (Or.inl hij)

/--
Boundary-aware unitary tridiagonalization.

Besides tridiagonalizing `A`, the unitary factor must send the protected
boundary column `c` to a vector supported only at the head coordinate.
-/
def HasUnitaryTridiagonalizationBoundary
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (c : Matrix ι Unit ℂ) : Prop :=
  ∃ Q : Matrix ι ι ℂ, ∃ T : Matrix ι ι ℂ,
    IsUnitaryMatrix Q ∧
    IsTridiagonal T ∧
    T.IsHermitian ∧
    A = Q * T * Qᴴ ∧
    ∀ i : ι, 0 < finiteOrderRank ι i → (Qᴴ * c) i () = 0

/-- Forget the protected boundary column. -/
theorem hasUnitaryTridiagonalization_of_boundary
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ} {c : Matrix ι Unit ℂ} :
    HasUnitaryTridiagonalizationBoundary A c →
      HasUnitaryTridiagonalization A := by
  intro h
  rcases h with ⟨Q, T, hQ, hT, hHerm, hEq, _hBoundary⟩
  exact ⟨Q, T, hQ, hT, hHerm, hEq⟩

/-- Transport a boundary-aware witness backward across a unitary similarity. -/
theorem unitaryTridiagonalizationBoundary_transport_unitarySimilarity
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (Q A : Matrix ι ι ℂ) (c : Matrix ι Unit ℂ)
    (hQ : IsUnitaryMatrix Q)
    (hTri : HasUnitaryTridiagonalizationBoundary (Qᴴ * A * Q) (Qᴴ * c)) :
    HasUnitaryTridiagonalizationBoundary A c := by
  rcases hTri with ⟨S, T, hS, hT, hHerm, hEq, hBoundary⟩
  refine ⟨Q * S, T, isUnitaryMatrix_mul hQ hS, hT, hHerm, ?_, ?_⟩
  · calc
      A = (Q * Qᴴ) * A * (Q * Qᴴ) := by
        simp [hQ.2]
      _ = Q * (Qᴴ * A * Q) * Qᴴ := by
        simp [Matrix.mul_assoc]
      _ = Q * (S * T * Sᴴ) * Qᴴ := by
        rw [hEq]
      _ = (Q * S) * T * (Q * S)ᴴ := by
        rw [Matrix.conjTranspose_mul]
        simp [Matrix.mul_assoc]
  · intro i hi
    have hb := hBoundary i hi
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hb

/-- Non-head elements have positive finite-order rank. -/
theorem finiteOrderRank_pos_of_ne_headElem
    (α : Type*) [Fintype α] [LinearOrder α] [Nonempty α]
    {i : α} (hi : i ≠ headElem (α := α)) :
    0 < finiteOrderRank α i := by
  classical
  have hlt : headElem (α := α) < i :=
    lt_of_le_of_ne (headElem_le (α := α) i) hi.symm
  unfold finiteOrderRank
  rw [Fintype.card_pos_iff]
  exact ⟨⟨headElem (α := α), hlt⟩⟩

/-- Boundary support away from positive rank implies the Hessenberg tail-head condition. -/
lemma boundary_zero_of_ne_head
    {β : Type*} [Fintype β] [LinearOrder β] [Nonempty β]
    {c : Matrix β Unit ℂ}
    (hc : ∀ i : β, 0 < finiteOrderRank β i → c i () = 0) :
    ∀ i : β, i ≠ headElem (α := β) → c i () = 0 := by
  intro i hi
  exact hc i (finiteOrderRank_pos_of_ne_headElem β hi)

/-- Reindex a concrete tridiagonalization witness along an order-preserving equivalence. -/
theorem hasUnitaryTridiagonalization_reindex_strictMono
    {α β : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    [Fintype β] [DecidableEq β] [LinearOrder β]
    (e : α ≃ β) (h_mono : StrictMono e)
    {A : Matrix α α ℂ} :
    HasUnitaryTridiagonalization A →
      HasUnitaryTridiagonalization (Matrix.reindex e e A) := by
  intro h
  rcases h with ⟨Q, T, hQ, hT, hHerm, hEq⟩
  refine ⟨Matrix.reindex e e Q, Matrix.reindex e e T,
    isUnitaryMatrix_reindex e hQ, ?_, ?_, ?_⟩
  · intro i j hij
    have hij' :
        finiteOrderRank α (e.symm j) + 1 < finiteOrderRank α (e.symm i) ∨
          finiteOrderRank α (e.symm i) + 1 < finiteOrderRank α (e.symm j) := by
      rcases hij with hij | hij
      · left
        rw [finiteOrderRank_equiv_symm e h_mono j,
          finiteOrderRank_equiv_symm e h_mono i]
        exact hij
      · right
        rw [finiteOrderRank_equiv_symm e h_mono i,
          finiteOrderRank_equiv_symm e h_mono j]
        exact hij
    simpa [Matrix.reindex_apply] using hT (e.symm i) (e.symm j) hij'
  · rw [Matrix.IsHermitian]
    simpa [Matrix.conjTranspose_reindex] using congrArg (Matrix.reindex e e) hHerm.eq
  · simpa [Matrix.conjTranspose_reindex, Matrix.submatrix_mul_equiv,
      Matrix.mul_assoc] using congrArg (Matrix.reindex e e) hEq

/-- Boundary-aware tridiagonalization transports along strictly monotone reindexing. -/
theorem hasUnitaryTridiagonalizationBoundary_reindex_strictMono
    {α β : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    [Fintype β] [DecidableEq β] [LinearOrder β]
    (e : α ≃ β) (h_mono : StrictMono e)
    {A : Matrix α α ℂ} {c : Matrix α Unit ℂ} :
    HasUnitaryTridiagonalizationBoundary A c →
      HasUnitaryTridiagonalizationBoundary
        (Matrix.reindex e e A) (Matrix.reindex e (Equiv.refl Unit) c) := by
  intro h
  rcases h with ⟨Q, T, hQ, hT, hHerm, hEq, hBoundary⟩
  refine ⟨Matrix.reindex e e Q, Matrix.reindex e e T,
    isUnitaryMatrix_reindex e hQ, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hij' :
        finiteOrderRank α (e.symm j) + 1 < finiteOrderRank α (e.symm i) ∨
          finiteOrderRank α (e.symm i) + 1 < finiteOrderRank α (e.symm j) := by
      rcases hij with hij | hij
      · left
        rw [finiteOrderRank_equiv_symm e h_mono j,
          finiteOrderRank_equiv_symm e h_mono i]
        exact hij
      · right
        rw [finiteOrderRank_equiv_symm e h_mono i,
          finiteOrderRank_equiv_symm e h_mono j]
        exact hij
    simpa [Matrix.reindex_apply] using hT (e.symm i) (e.symm j) hij'
  · rw [Matrix.IsHermitian]
    simpa [Matrix.conjTranspose_reindex] using congrArg (Matrix.reindex e e) hHerm.eq
  · simpa [Matrix.conjTranspose_reindex, Matrix.submatrix_mul_equiv,
      Matrix.mul_assoc] using congrArg (Matrix.reindex e e) hEq
  · intro i hi
    have hi' : 0 < finiteOrderRank α (e.symm i) := by
      rw [finiteOrderRank_equiv_symm e h_mono i]
      exact hi
    have hb := hBoundary (e.symm i) hi'
    have hmul := reindex_mul_column e (Matrix.reindex e e Q)ᴴ c
    have hb_re := congrFun (congrFun hmul (e.symm i)) ()
    have hentry :
        ((Matrix.reindex e e Q)ᴴ *
            Matrix.reindex e (Equiv.refl Unit) c) i () =
          (Qᴴ * c) (e.symm i) () := by
      simpa [Matrix.conjTranspose_reindex, Matrix.reindex_apply] using hb_re.symm
    rw [hentry]
    exact hb

/-- Pull a boundary-aware witness back along a strictly monotone equivalence. -/
theorem hasUnitaryTridiagonalizationBoundary_reindex_strictMono_symm
    {α β : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    (e : α ≃ β) (h_mono : StrictMono e)
    {A : Matrix α α ℂ} {c : Matrix α Unit ℂ}
    (h :
      HasUnitaryTridiagonalizationBoundary
        (Matrix.reindex e e A) (Matrix.reindex e (Equiv.refl Unit) c)) :
    HasUnitaryTridiagonalizationBoundary A c := by
  have hback := hasUnitaryTridiagonalizationBoundary_reindex_strictMono
    e.symm
    (by
      intro x y hxy
      have hxy' : e (e.symm x) < e (e.symm y) := by simpa using hxy
      exact (h_mono.lt_iff_lt).1 hxy')
    h
  simpa [reindex_reindex, Matrix.reindex_apply] using hback

/--
Boundary lift obligation for the concrete descent.

This is the mathematically correct local block theorem still to be discharged:
the recursive tail witness must protect the parent lower-left block as a
boundary column.
-/
def TridiagonalizationBoundaryBlockLift : Prop :=
  ∀ {β : Type*} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β],
    ∀ (A₁₁ : Matrix Unit Unit ℂ) (A₁₂ : Matrix Unit β ℂ)
      (A₂₁ : Matrix β Unit ℂ) (A₂₂ : Matrix β β ℂ),
      (Matrix.reindex (sumToLexEquiv Unit β) (sumToLexEquiv Unit β)
        (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ :
          Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ)).IsHermitian →
        HasUnitaryTridiagonalizationBoundary A₂₂ A₂₁ →
          HasUnitaryTridiagonalization
            (Matrix.reindex (sumToLexEquiv Unit β) (sumToLexEquiv Unit β)
              (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ :
                Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ))

/-- Concrete block-diagonal lift for the boundary-aware tridiagonal target. -/
theorem tridiagonalization_boundary_block_lift :
    TridiagonalizationBoundaryBlockLift := by
  intro β _fβ _dβ _oβ _nβ A₁₁ A₁₂ A₂₁ A₂₂ hHerm hTail
  rcases hTail with ⟨Qtail, Ttail, hQtail, hTtail, _hTtailHerm, hEqTail, hBoundary⟩
  let Ablk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℂ :=
    fromBlocks A₁₁ A₁₂ A₂₁ A₂₂
  let Qblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℂ :=
    fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 Qtail
  let Tblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℂ :=
    fromBlocks A₁₁ (A₁₂ * Qtail) (Qtailᴴ * A₂₁) Ttail
  have hHermBlk : Ablk.IsHermitian := by
    simpa [Ablk, reindex_sumToLex_fromBlocks] using hHerm
  have hQblk : IsUnitaryMatrix Qblk := by
    simpa [Qblk, hessenbergBlockDiagOne] using
      (isUnitaryMatrix_blockDiag_one (β := β) hQtail)
  have hInvTail : HasMatrixInverse Qtail Qtailᴴ :=
    hasMatrixInverse_of_isUnitaryMatrix hQtail
  have hQblk_conj :
      Qblkᴴ = fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 Qtailᴴ := by
    change
      (fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 Qtail :
        Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℂ)ᴴ =
          fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 Qtailᴴ
    rw [Matrix.fromBlocks_conjTranspose]
    simp
  have hEqBlk : Ablk = Qblk * Tblk * Qblkᴴ := by
    rw [hQblk_conj]
    simpa [Ablk, Qblk, Tblk, hessenbergBlockDiagOne] using
      hessenbergBlockDiagOne_parentBlock_eq
        A₁₁ A₁₂ A₂₁ A₂₂ Ttail Qtail Qtailᴴ hInvTail hEqTail
  have hHermT : Tblk.IsHermitian := by
    have hT_eq : Tblk = Qblkᴴ * Ablk * Qblk :=
      unitary_similarity_target_eq hQblk hEqBlk
    rw [hT_eq]
    exact isHermitian_unitarySimilarity hHermBlk
  have hHessT : IsUpperHessenberg Tblk := by
    simpa [Tblk] using
      isUpperHessenberg_fromBlocks_ready
        A₁₁ (A₁₂ * Qtail) (Qtailᴴ * A₂₁) Ttail
        (boundary_zero_of_ne_head hBoundary)
        (isUpperHessenberg_of_isTridiagonal hTtail)
  have hTriT : IsTridiagonal Tblk :=
    isTridiagonal_of_isUpperHessenberg_of_isHermitian hHessT hHermT
  rw [reindex_sumToLex_fromBlocks]
  exact ⟨Qblk, Tblk, hQblk, hTriT, hHermT, hEqBlk⟩

/--
Boundary-column version of the block lift.

The parent boundary column must already be zero away from the head in the
lexicographic head-tail coordinates; the block-diagonal tail unitary then
preserves that support.
-/
theorem tridiagonalization_boundary_block_lift_with_column
    {β : Type*} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    (A₁₁ : Matrix Unit Unit ℂ) (A₁₂ : Matrix Unit β ℂ)
    (A₂₁ : Matrix β Unit ℂ) (A₂₂ : Matrix β β ℂ)
    (c : Matrix (Unit ⊕ₗ β) Unit ℂ)
    (hHerm :
      (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ :
        Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℂ).IsHermitian)
    (hc : ∀ i : Unit ⊕ₗ β,
      0 < finiteOrderRank (Unit ⊕ₗ β) i → c i () = 0)
    (hTail : HasUnitaryTridiagonalizationBoundary A₂₂ A₂₁) :
    HasUnitaryTridiagonalizationBoundary
      (Matrix.reindex (sumToLexEquiv Unit β) (sumToLexEquiv Unit β)
        (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ :
          Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ))
      c := by
  rcases hTail with ⟨Qtail, Ttail, hQtail, hTtail, _hTtailHerm, hEqTail, hBoundary⟩
  let Ablk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℂ :=
    fromBlocks A₁₁ A₁₂ A₂₁ A₂₂
  let Qblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℂ :=
    fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 Qtail
  let Tblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℂ :=
    fromBlocks A₁₁ (A₁₂ * Qtail) (Qtailᴴ * A₂₁) Ttail
  have hQblk : IsUnitaryMatrix Qblk := by
    simpa [Qblk, hessenbergBlockDiagOne] using
      (isUnitaryMatrix_blockDiag_one (β := β) hQtail)
  have hInvTail : HasMatrixInverse Qtail Qtailᴴ :=
    hasMatrixInverse_of_isUnitaryMatrix hQtail
  have hQblk_conj :
      Qblkᴴ = fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 Qtailᴴ := by
    change
      (fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 Qtail :
        Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℂ)ᴴ =
          fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 Qtailᴴ
    rw [Matrix.fromBlocks_conjTranspose]
    simp
  have hEqBlk : Ablk = Qblk * Tblk * Qblkᴴ := by
    rw [hQblk_conj]
    simpa [Ablk, Qblk, Tblk, hessenbergBlockDiagOne] using
      hessenbergBlockDiagOne_parentBlock_eq
        A₁₁ A₁₂ A₂₁ A₂₂ Ttail Qtail Qtailᴴ hInvTail hEqTail
  have hHermT : Tblk.IsHermitian := by
    have hT_eq : Tblk = Qblkᴴ * Ablk * Qblk :=
      unitary_similarity_target_eq hQblk hEqBlk
    rw [hT_eq]
    exact isHermitian_unitarySimilarity hHerm
  have hHessT : IsUpperHessenberg Tblk := by
    simpa [Tblk] using
      isUpperHessenberg_fromBlocks_ready
        A₁₁ (A₁₂ * Qtail) (Qtailᴴ * A₂₁) Ttail
        (boundary_zero_of_ne_head hBoundary)
        (isUpperHessenberg_of_isTridiagonal hTtail)
  have hTriT : IsTridiagonal Tblk :=
    isTridiagonal_of_isUpperHessenberg_of_isHermitian hHessT hHermT
  rw [reindex_sumToLex_fromBlocks]
  refine ⟨Qblk, Tblk, hQblk, hTriT, hHermT, hEqBlk, ?_⟩
  intro i hi
  cases h : ofLex i with
  | inl u =>
      cases u
      have hi_eq : i = (Sum.inlₗ () : Unit ⊕ₗ β) := by
        rw [← toLex_ofLex i, h]
      rw [hi_eq, finiteOrderRank_sumLex_inl_unit] at hi
      exact False.elim (Nat.lt_irrefl 0 hi)
  | inr j =>
      have hi_eq : i = (Sum.inrₗ j : Unit ⊕ₗ β) := by
        rw [← toLex_ofLex i, h]
      subst i
      rw [hQblk_conj]
      have hzero_tail : ∀ k : β, c (Sum.inrₗ k) () = 0 := by
        intro k
        exact hc (Sum.inrₗ k) (by
          rw [finiteOrderRank_sumLex_inr]
          omega)
      simpa [hessenbergBlockDiagOne] using
        hessenbergBlockDiagOne_mul_readyColumn_tail Qtailᴴ c hzero_tail j

/--
Boundary-aware one-step oracle.  A concrete Householder/Givens construction
should build this oracle and then use `TridiagonalizationBoundaryBlockLift` to
produce the ordinary square-framework `TridiagonalizationStepOracle`.
-/
structure TridiagonalizationBoundaryStepOracle where
  Q :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℂ,
      Matrix x_sub.1.ι x_sub.1.ι ℂ
  unitary_Q :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℂ,
      IsUnitaryMatrix (Q x_sub)
  ready_matrix :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℂ,
      ∀ (_hne : Nonempty x_sub.1.ι),
      TridiagonalizationReady x_sub.1.ι ((Q x_sub)ᴴ * x_sub.1.A * Q x_sub)
  ready_boundary :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℂ,
      ∀ i : x_sub.1.ι, 0 < finiteOrderRank x_sub.1.ι i →
        ((Q x_sub)ᴴ * x_sub.1.c) i () = 0

/-- Universe-level boundary predicate for tridiagonalization. -/
def TridiagonalizationBoundary_P (x : HessenbergBoundaryUniverse.{u} ℂ) : Prop :=
  x.A.IsHermitian →
    HasUnitaryTridiagonalizationBoundary x.A x.c

/-- Boundary-universe measure reused from the Hessenberg boundary driver. -/
abbrev tridiagonalizationBoundaryμ (x : HessenbergBoundaryUniverse.{u} ℂ) : Nat :=
  hessenbergBoundaryμ x

/-- Boundary-universe base measure. -/
abbrev tridiagonalizationBoundaryμBase : Nat :=
  hessenbergBoundaryμBase

/-- The recursive boundary subproblem removes the head index. -/
noncomputable abbrev tridiagonalizationBoundarySliceSub
    (x_sub : PosHessenbergBoundaryUniverse ℂ) :
    HessenbergBoundaryUniverse.{u} ℂ :=
  hessenbergBoundarySliceSub x_sub

/-- The boundary slice strictly decreases the dimension measure. -/
theorem tridiagonalizationBoundarySliceProgress
    (x_sub : PosHessenbergBoundaryUniverse ℂ) :
    tridiagonalizationBoundaryμ (tridiagonalizationBoundarySliceSub x_sub) <
      tridiagonalizationBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} ℂ) :=
  hessenbergBoundarySliceProgress x_sub

/-- Boundary object obtained by applying a unitary similarity. -/
noncomputable def tridiagonalizationBoundarySimilarityObject
    (x : HessenbergBoundaryUniverse.{u} ℂ)
    (Q : Matrix x.ι x.ι ℂ) : HessenbergBoundaryUniverse.{u} ℂ :=
  { ι := x.ι
    A := Qᴴ * x.A * Q
    c := Qᴴ * x.c }

/-- Unitarly transformed positive boundary object. -/
noncomputable def tridiagonalizationBoundaryStepObject
    (oracle : TridiagonalizationBoundaryStepOracle.{u})
    (x_sub : PosHessenbergBoundaryUniverse ℂ) :
    PosHessenbergBoundaryUniverse ℂ :=
  ⟨tridiagonalizationBoundarySimilarityObject
      (x_sub : HessenbergBoundaryUniverse.{u} ℂ) (oracle.Q x_sub),
    by simpa [tridiagonalizationBoundarySimilarityObject] using x_sub.2⟩

/-- Relation generated by one oracle-provided unitary similarity step. -/
def tridiagonalizationBoundaryStepRel
    (oracle : TridiagonalizationBoundaryStepOracle.{u})
    (y_sub x_sub : PosHessenbergBoundaryUniverse ℂ) : Prop :=
  y_sub = tridiagonalizationBoundaryStepObject oracle x_sub

/-- Boundary predicate transport across a same-index unitary similarity. -/
theorem tridiagonalizationBoundary_transport_unitarySimilarity
    (x : HessenbergBoundaryUniverse.{u} ℂ)
    (Q : Matrix x.ι x.ι ℂ)
    (hQ : IsUnitaryMatrix Q)
    (hY :
      TridiagonalizationBoundary_P
        (tridiagonalizationBoundarySimilarityObject x Q)) :
    TridiagonalizationBoundary_P x := by
  intro hHerm
  have hYHerm : (Qᴴ * x.A * Q).IsHermitian :=
    isHermitian_unitarySimilarity hHerm
  exact unitaryTridiagonalizationBoundary_transport_unitarySimilarity
    Q x.A x.c hQ (hY hYHerm)

/-- Correct proof obligation for a boundary-aware lift step. -/
def TridiagonalizationBoundaryLiftReady
    (x_sub : PosHessenbergBoundaryUniverse ℂ) : Prop :=
  let x : HessenbergBoundaryUniverse.{u} ℂ := x_sub
  (∀ (_hne : Nonempty x.ι), TridiagonalizationReady x.ι x.A) →
    (∀ i : x.ι, 0 < finiteOrderRank x.ι i → x.c i () = 0) →
      TridiagonalizationBoundary_P (tridiagonalizationBoundarySliceSub x_sub) →
        TridiagonalizationBoundary_P x

/-- Concrete lift theorem for the boundary-aware tridiagonalization descent. -/
theorem tridiagonalizationBoundary_lift_ready
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    TridiagonalizationBoundaryLiftReady x_sub := by
  intro hReady hBoundary hTail hHerm
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  let β := TridiagonalTailIdx x_sub.1.ι
  let Aplain : Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ :=
    tridiagonalHeadTailMatrix x_sub.1.ι x_sub.1.A
  let cLex : Matrix (Unit ⊕ₗ β) Unit ℂ :=
    Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι)) (Equiv.refl Unit) x_sub.1.c
  by_cases hβ : Nonempty β
  · letI : Nonempty β := hβ
    have hTailHerm : Aplain.toBlocks₂₂.IsHermitian := by
      simpa [Aplain, tridiagonalTailSlice_eq_lowerRightBlock] using
        tridiagonalTailSlice_isHermitian x_sub.1.ι hHerm
    have hTailBoundary :
        HasUnitaryTridiagonalizationBoundary Aplain.toBlocks₂₂ Aplain.toBlocks₂₁ := by
      have hP := hTail hTailHerm
      simpa [tridiagonalizationBoundarySliceSub, hessenbergBoundarySliceSub,
        hessenbergTailSlice_eq_boundaryLowerRightBlock,
        hessenbergBoundaryLowerLeftColumn, hessenbergBoundaryHeadTailMatrix,
        Aplain, TridiagonalTailIdx, HessenbergTailIdx] using hP
    have hLexHerm :
        (Matrix.reindex (sumToLexEquiv Unit β) (sumToLexEquiv Unit β)
          (fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂
            Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ :
            Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ)).IsHermitian := by
      have hLexEq :
          Matrix.reindex (sumToLexEquiv Unit β) (sumToLexEquiv Unit β)
            (fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂
              Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ :
              Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ) =
            Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι))
              (headTailLexEquiv (α := x_sub.1.ι)) x_sub.1.A := by
        rw [reindex_sumToLex_fromBlocks]
        exact (hessenbergBoundaryHeadTailLex_fromBlocks x_sub.1.ι x_sub.1.A).symm
      rw [hLexEq]
      rw [Matrix.IsHermitian]
      simpa [Matrix.conjTranspose_reindex] using
        congrArg (Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι))
          (headTailLexEquiv (α := x_sub.1.ι))) hHerm.eq
    have hcLex : ∀ i : Unit ⊕ₗ β,
        0 < finiteOrderRank (Unit ⊕ₗ β) i → cLex i () = 0 := by
      intro i hi
      have hpre : 0 < finiteOrderRank x_sub.1.ι
          ((headTailLexEquiv (α := x_sub.1.ι)).symm i) := by
        rw [finiteOrderRank_equiv_symm
          (headTailLexEquiv (α := x_sub.1.ι))
          (headTailLexEquiv_strictMono (α := x_sub.1.ι)) i]
        exact hi
      simpa [cLex, Matrix.reindex_apply] using
        hBoundary ((headTailLexEquiv (α := x_sub.1.ι)).symm i) hpre
    have hBlock :
        HasUnitaryTridiagonalizationBoundary
          (Matrix.reindex (sumToLexEquiv Unit β) (sumToLexEquiv Unit β)
            (fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂
              Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ :
              Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ))
          cLex :=
      tridiagonalization_boundary_block_lift_with_column
        Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₂₁ Aplain.toBlocks₂₂
        cLex hLexHerm hcLex hTailBoundary
    have hLexEq :
        Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι))
          (headTailLexEquiv (α := x_sub.1.ι)) x_sub.1.A =
        Matrix.reindex (sumToLexEquiv Unit β) (sumToLexEquiv Unit β)
          (fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂
            Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ :
            Matrix (Unit ⊕ β) (Unit ⊕ β) ℂ) := by
      rw [reindex_sumToLex_fromBlocks]
      exact hessenbergBoundaryHeadTailLex_fromBlocks x_sub.1.ι x_sub.1.A
    have hLexBoundary :
        HasUnitaryTridiagonalizationBoundary
          (Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι))
            (headTailLexEquiv (α := x_sub.1.ι)) x_sub.1.A)
          (Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι)) (Equiv.refl Unit)
            x_sub.1.c) := by
      simpa [hLexEq, cLex]
        using hBlock
    exact hasUnitaryTridiagonalizationBoundary_reindex_strictMono_symm
      (headTailLexEquiv (α := x_sub.1.ι))
      (headTailLexEquiv_strictMono (α := x_sub.1.ι))
      hLexBoundary
  · have hsub : Subsingleton x_sub.1.ι := by
      refine ⟨?_⟩
      intro a b
      by_cases ha : a = headElem (α := x_sub.1.ι)
      · by_cases hb : b = headElem (α := x_sub.1.ι)
        · rw [ha, hb]
        · exact False.elim (hβ ⟨⟨b, hb⟩⟩)
      · exact False.elim (hβ ⟨⟨a, ha⟩⟩)
    letI : Subsingleton x_sub.1.ι := hsub
    refine ⟨1, x_sub.1.A, isUnitaryMatrix_one,
      isTridiagonal_subsingleton x_sub.1.A, hHerm, by simp, ?_⟩
    intro i hi
    have hzero : finiteOrderRank x_sub.1.ι i = 0 := by
      have hi_head : i = headElem (α := x_sub.1.ι) := Subsingleton.elim _ _
      rw [hi_head, finiteOrderRank_headElem]
    rw [hzero] at hi
    exact False.elim (Nat.lt_irrefl 0 hi)

/-- Proof-side data for the boundary-aware tridiagonalization descent. -/
structure TridiagonalizationBoundaryProofData where
  r_sub :
    PosHessenbergBoundaryUniverse.{u} ℂ →
      PosHessenbergBoundaryUniverse.{u} ℂ → Prop
  IsSliceable_sub : PosHessenbergBoundaryUniverse.{u} ℂ → Prop
  slice_sub :
    ∀ x_sub : PosHessenbergBoundaryUniverse.{u} ℂ,
      IsSliceable_sub x_sub → HessenbergBoundaryUniverse.{u} ℂ
  transport_sub :
    ∀ {x_sub y_sub : PosHessenbergBoundaryUniverse.{u} ℂ},
      r_sub y_sub x_sub →
        TridiagonalizationBoundary_P (y_sub : HessenbergBoundaryUniverse.{u} ℂ) →
          TridiagonalizationBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
  lift_from_slice_sub :
    ∀ (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) (hx : IsSliceable_sub x_sub),
      TridiagonalizationBoundary_P (slice_sub x_sub hx) →
        TridiagonalizationBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
  reach_sub :
    ∀ x_sub : PosHessenbergBoundaryUniverse.{u} ℂ,
      tridiagonalizationBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} ℂ) >
        tridiagonalizationBoundaryμBase →
        Σ' (y_sub : PosHessenbergBoundaryUniverse.{u} ℂ),
          Σ' (hy : IsSliceable_sub y_sub),
            r_sub y_sub x_sub ∧
              tridiagonalizationBoundaryμ (slice_sub y_sub hy) <
                tridiagonalizationBoundaryμ
                  (x_sub : HessenbergBoundaryUniverse.{u} ℂ)

/-- Convert a one-step boundary oracle and local lift theorem into proof-side data. -/
noncomputable def tridiagonalizationBoundaryProofDataOfStepOracle
    (oracle : TridiagonalizationBoundaryStepOracle.{u})
    (liftReady : ∀ x_sub : PosHessenbergBoundaryUniverse.{u} ℂ,
      TridiagonalizationBoundaryLiftReady x_sub) :
    TridiagonalizationBoundaryProofData.{u} where
  r_sub := tridiagonalizationBoundaryStepRel oracle
  IsSliceable_sub := fun x_sub =>
    (∀ (_hne : Nonempty x_sub.1.ι),
        TridiagonalizationReady x_sub.1.ι x_sub.1.A) ∧
      (∀ i : x_sub.1.ι, 0 < finiteOrderRank x_sub.1.ι i →
        x_sub.1.c i () = 0) ∧
      TridiagonalizationBoundaryLiftReady x_sub
  slice_sub := fun x_sub _ => tridiagonalizationBoundarySliceSub x_sub
  transport_sub := by
    intro x_sub y_sub hrel hP
    subst hrel
    exact
      tridiagonalizationBoundary_transport_unitarySimilarity
        (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
        (oracle.Q x_sub) (oracle.unitary_Q x_sub) hP
  lift_from_slice_sub := by
    intro y_sub hx hP
    exact hx.2.2 hx.1 hx.2.1 hP
  reach_sub := by
    intro x_sub hgt
    let y_sub := tridiagonalizationBoundaryStepObject oracle x_sub
    have hslice :
        (∀ (_hne : Nonempty y_sub.1.ι),
            TridiagonalizationReady y_sub.1.ι y_sub.1.A) ∧
          (∀ i : y_sub.1.ι, 0 < finiteOrderRank y_sub.1.ι i →
            y_sub.1.c i () = 0) ∧
          TridiagonalizationBoundaryLiftReady y_sub := by
      refine ⟨?_, ?_, liftReady y_sub⟩
      · intro hne
        simpa [y_sub, tridiagonalizationBoundaryStepObject,
          tridiagonalizationBoundarySimilarityObject] using
          oracle.ready_matrix x_sub hne
      · intro i hi
        simpa [y_sub, tridiagonalizationBoundaryStepObject,
          tridiagonalizationBoundarySimilarityObject] using
          oracle.ready_boundary x_sub i hi
    have hmono :
        tridiagonalizationBoundaryμ
            (y_sub : HessenbergBoundaryUniverse.{u} ℂ) ≤
          tridiagonalizationBoundaryμ
            (x_sub : HessenbergBoundaryUniverse.{u} ℂ) := by
      simp [y_sub, tridiagonalizationBoundaryStepObject,
        tridiagonalizationBoundarySimilarityObject, tridiagonalizationBoundaryμ,
        hessenbergBoundaryμ]
    exact
      ⟨y_sub, hslice, rfl,
        lt_of_lt_of_le (tridiagonalizationBoundarySliceProgress y_sub) hmono⟩

/-- Boundary base case for the tridiagonalization target. -/
theorem tridiagonalizationBoundary_base_univ
    (x : HessenbergBoundaryUniverse.{u} ℂ) :
    ((∀ x_sub : PosHessenbergBoundaryUniverse.{u} ℂ,
        (x_sub : HessenbergBoundaryUniverse ℂ) ≠ x) ∨
      tridiagonalizationBoundaryμ x ≤ tridiagonalizationBoundaryμBase) →
      TridiagonalizationBoundary_P x := by
  intro hx hHerm
  have hzero : Fintype.card x.ι = 0 :=
    hessenbergBoundaryBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  letI : Subsingleton x.ι := by infer_instance
  refine ⟨1, x.A, isUnitaryMatrix_one, ?_, hHerm, by simp, ?_⟩
  · exact isTridiagonal_subsingleton x.A
  · intro i _hi
    exact False.elim (IsEmpty.false i)

/-- Subtype-induction instance for boundary-aware tridiagonalization. -/
noncomputable def tridiagonalizationBoundary_framework_inst
    (proofData : TridiagonalizationBoundaryProofData.{u}) :
    SubtypeInductionInstance
      (HessenbergBoundaryUniverse.{u} ℂ)
      (PosHessenbergBoundaryUniverse.{u} ℂ)
      (fun x => (x : HessenbergBoundaryUniverse.{u} ℂ)) where
  μ := tridiagonalizationBoundaryμ
  μ_base := tridiagonalizationBoundaryμBase
  P := TridiagonalizationBoundary_P
  P_sub := fun x_sub =>
    TridiagonalizationBoundary_P
      (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
  P_compat := by
    intro x_sub
    rfl
  r_sub := proofData.r_sub
  IsSliceable_sub := proofData.IsSliceable_sub
  slice_sub := proofData.slice_sub
  transport_sub := by
    intro x_sub y_sub hrel hP
    exact proofData.transport_sub hrel hP
  lift_from_slice_sub := by
    intro x_sub hx hP
    exact proofData.lift_from_slice_sub x_sub hx hP
  reach_sub := by
    intro x_sub hgt
    exact proofData.reach_sub x_sub hgt
  base_univ := tridiagonalizationBoundary_base_univ

/-- Boundary-column framework theorem for unitary tridiagonalization. -/
theorem exists_unitaryTridiagonalizationBoundary_framework
    (proofData : TridiagonalizationBoundaryProofData.{u})
    (x : HessenbergBoundaryUniverse.{u} ℂ) :
    TridiagonalizationBoundary_P x := by
  let inst :
      SubtypeInductionInstance
        (HessenbergBoundaryUniverse.{u} ℂ)
        (PosHessenbergBoundaryUniverse.{u} ℂ)
        (fun x => (x : HessenbergBoundaryUniverse.{u} ℂ)) :=
    tridiagonalizationBoundary_framework_inst proofData
  exact
    (SubtypeInductionInstance.prove inst) x

/-- Conditional boundary-framework theorem stated with a step oracle and local lift theorem. -/
theorem exists_unitaryTridiagonalizationBoundary_framework_stepOracle
    (oracle : TridiagonalizationBoundaryStepOracle.{u})
    (liftReady : ∀ x_sub : PosHessenbergBoundaryUniverse.{u} ℂ,
      TridiagonalizationBoundaryLiftReady x_sub)
    (x : HessenbergBoundaryUniverse.{u} ℂ) :
    TridiagonalizationBoundary_P x := by
  let proofData : TridiagonalizationBoundaryProofData.{u} :=
    tridiagonalizationBoundaryProofDataOfStepOracle
      (oracle := oracle)
      (liftReady := liftReady)
  exact exists_unitaryTridiagonalizationBoundary_framework proofData x

/--
Conditional public boundary-framework theorem for ordinary Hermitian
tridiagonalization.  This keeps the theorem on the subtype-descent route and
forgets the auxiliary protected zero boundary column at the end.
-/
theorem exists_unitary_tridiagonalization_boundary_framework_stepOracle
    (oracle : TridiagonalizationBoundaryStepOracle.{u})
    (liftReady : ∀ x_sub : PosHessenbergBoundaryUniverse.{u} ℂ,
      TridiagonalizationBoundaryLiftReady x_sub)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A := by
  by_cases hne : Nonempty ι
  · let x : HessenbergBoundaryUniverse.{u} ℂ :=
      { ι := ι
        A := A
        c := 0 }
    have hP : TridiagonalizationBoundary_P x :=
      exists_unitaryTridiagonalizationBoundary_framework_stepOracle
        oracle liftReady x
    have hBoundary : HasUnitaryTridiagonalizationBoundary A (0 : Matrix ι Unit ℂ) := by
      simpa [x] using hP hA
    exact hasUnitaryTridiagonalization_of_boundary hBoundary
  · letI : IsEmpty ι := not_nonempty_iff.mp hne
    letI : Subsingleton ι := by infer_instance
    exact base_unitaryTridiagonalization_subsingleton A hA

/-- Proof-side data from a boundary step oracle, using the proved local lift theorem. -/
noncomputable def tridiagonalizationBoundaryProofDataOfStepOracle_proved
    (oracle : TridiagonalizationBoundaryStepOracle.{u}) :
    TridiagonalizationBoundaryProofData.{u} :=
  tridiagonalizationBoundaryProofDataOfStepOracle oracle
    tridiagonalizationBoundary_lift_ready

/-- Boundary framework theorem from only the step oracle. -/
theorem exists_unitaryTridiagonalizationBoundary_framework_oracle
    (oracle : TridiagonalizationBoundaryStepOracle.{u})
    (x : HessenbergBoundaryUniverse.{u} ℂ) :
    TridiagonalizationBoundary_P x :=
  exists_unitaryTridiagonalizationBoundary_framework
    (tridiagonalizationBoundaryProofDataOfStepOracle_proved oracle) x

/-- Ordinary Hermitian tridiagonalization routed through the boundary descent template. -/
theorem exists_unitary_tridiagonalization_boundary_framework_oracle
    (oracle : TridiagonalizationBoundaryStepOracle.{u})
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A := by
  by_cases hne : Nonempty ι
  · let x : HessenbergBoundaryUniverse.{u} ℂ :=
      { ι := ι
        A := A
        c := 0 }
    have hP : TridiagonalizationBoundary_P x :=
      exists_unitaryTridiagonalizationBoundary_framework_oracle oracle x
    have hBoundary : HasUnitaryTridiagonalizationBoundary A (0 : Matrix ι Unit ℂ) := by
      simpa [x] using hP hA
    exact hasUnitaryTridiagonalization_of_boundary hBoundary
  · letI : IsEmpty ι := not_nonempty_iff.mp hne
    letI : Subsingleton ι := by infer_instance
    exact base_unitaryTridiagonalization_subsingleton A hA

end MatDecompFormal.Instances
