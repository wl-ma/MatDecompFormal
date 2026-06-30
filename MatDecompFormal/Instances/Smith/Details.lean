/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Gauss.Details

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Smith Normal Form Details

This file contains the data-oriented Smith target predicate and the proof-side
algebra needed by the rectangular descent framework. The algebraic Smith step
itself is intentionally isolated in `SmithStepOracle` in `Strategy.lean`.
-/

variable {R : Type v} {m n : Type u}

/-- Data-oriented rectangular diagonal payload, without invariant-factor order. -/
structure SmithDiagonalData
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n R) where
  r : Type u
  fintype_r : Fintype r
  row : r → m
  col : r → n
  diag : r → R
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  entry_diag : ∀ k, D (row k) (col k) = diag k
  entry_zero : ∀ i j, (∀ k, row k ≠ i ∨ col k ≠ j) → D i j = 0

attribute [instance] SmithDiagonalData.fintype_r

/-- Predicate saying a matrix has the old data-oriented rectangular diagonal shape. -/
def IsSmithDiagonalForm
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n R) : Prop :=
  Nonempty (SmithDiagonalData D)

/-- Two-sided equivalence to a data-oriented rectangular diagonal matrix. -/
def HasSmithDiagonalForm
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n R) : Prop :=
  ∃ P : Matrix m m R, ∃ Q : Matrix n n R, ∃ D : Matrix m n R,
    GaussInvertibleMatrix P ∧
    GaussInvertibleMatrix Q ∧
    IsSmithDiagonalForm D ∧
    D = P * A * Q

/-- Data-oriented Smith normal-form payload with an ordered invariant-factor chain. -/
structure SmithNormalFormData
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n R) where
  r : Type u
  fintype_r : Fintype r
  order : Fin (Fintype.card r) ≃ r
  row : r → m
  col : r → n
  diag : r → R
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  entry_diag : ∀ k, D (row k) (col k) = diag k
  entry_zero : ∀ i j, (∀ k, row k ≠ i ∨ col k ≠ j) → D i j = 0
  divides_chain : ∀ k : Fin (Fintype.card r),
    (hnext : (k : Nat) + 1 < Fintype.card r) →
      diag (order k) ∣ diag (order ⟨(k : Nat) + 1, hnext⟩)

attribute [instance] SmithNormalFormData.fintype_r

namespace SmithNormalFormData

noncomputable def defaultOrder (r : Type u) [Fintype r] :
    Fin (Fintype.card r) ≃ r :=
  (Fintype.equivFin r).symm

noncomputable def consOrder {r : Type u} [Fintype r]
    (order : Fin (Fintype.card r) ≃ r) :
    Fin (Fintype.card (Option r)) ≃ Option r :=
  (finCongr (Fintype.card_option (α := r))).trans
    ((finSuccEquiv (Fintype.card r)).trans (Equiv.optionCongr order))

@[simp] lemma consOrder_zero {r : Type u} [Fintype r]
    (order : Fin (Fintype.card r) ≃ r)
    (h : 0 < Fintype.card (Option r)) :
    consOrder order ⟨0, h⟩ = none := by
  simp [consOrder]

lemma consOrder_succ {r : Type u} [Fintype r]
    (order : Fin (Fintype.card r) ≃ r)
    (k : Fin (Fintype.card r))
    (h : (k : Nat) + 1 < Fintype.card (Option r)) :
    consOrder order ⟨(k : Nat) + 1, h⟩ = some (order k) := by
  have hcast :
      (finCongr (Fintype.card_option (α := r)) ⟨(k : Nat) + 1, h⟩) = k.succ := by
    ext
    simp [finCongr]
  simp [consOrder, hcast]

end SmithNormalFormData

/-- Predicate saying a matrix is in data-oriented Smith normal form. -/
def IsSmithNormalForm
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n R) : Prop :=
  Nonempty (SmithNormalFormData D)

/-- Strong Smith data forgets to the old rectangular diagonal-shape payload. -/
noncomputable def SmithNormalFormData.toDiagonalData
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {D : Matrix m n R} (data : SmithNormalFormData D) :
    SmithDiagonalData D where
  r := data.r
  fintype_r := data.fintype_r
  row := data.row
  col := data.col
  diag := data.diag
  row_injective := data.row_injective
  col_injective := data.col_injective
  entry_diag := data.entry_diag
  entry_zero := data.entry_zero

/-- Strong Smith normal form implies the old rectangular diagonal-shape predicate. -/
theorem isSmithDiagonalForm_of_smith
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {D : Matrix m n R} (hD : IsSmithNormalForm D) :
    IsSmithDiagonalForm D := by
  rcases hD with ⟨data⟩
  exact ⟨data.toDiagonalData⟩

/-- Two-sided equivalence to a Smith normal-form matrix.
The equation direction is `D = P * A * Q` (structured matrix on left),
not the alternative `A = P⁻¹ * D * Q⁻¹`. -/
def HasSmithNormalForm
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n R) : Prop :=
  ∃ P : Matrix m m R, ∃ Q : Matrix n n R, ∃ D : Matrix m n R,
    GaussInvertibleMatrix P ∧
    GaussInvertibleMatrix Q ∧
    IsSmithNormalForm D ∧
    D = P * A * Q

/-- Strong Smith witnesses forget to rectangular diagonal-form witnesses. -/
theorem hasSmithDiagonalForm_of_smith
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m n R} (hA : HasSmithNormalForm A) :
    HasSmithDiagonalForm A := by
  rcases hA with ⟨P, Q, D, hP, hQ, hD, hEq⟩
  exact ⟨P, Q, D, hP, hQ, isSmithDiagonalForm_of_smith hD, hEq⟩

/-- Universe-level predicate used by the rectangular driver. -/
def Smith_P [Semiring R] (x : RectUniverse R) : Prop :=
  HasSmithNormalForm x.A

def Smith_P_sub [Semiring R] (x_sub : PosRectUniverse R) : Prop :=
  Smith_P (x_sub : RectUniverse R)

@[simp] theorem smith_P_compat [Semiring R] (x_sub : PosRectUniverse R) :
    Smith_P_sub x_sub ↔ Smith_P (x_sub : RectUniverse R) :=
  Iff.rfl

/-- Empty Smith payload for a zero matrix. -/
noncomputable def smithNormalFormData_zero
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n R) (hD : D = 0) :
    SmithNormalFormData D where
  r := ULift Empty
  fintype_r := inferInstance
  order := SmithNormalFormData.defaultOrder (ULift Empty)
  row := fun k => Empty.elim k.down
  col := fun k => Empty.elim k.down
  diag := fun k => Empty.elim k.down
  row_injective := by intro k; cases k.down
  col_injective := by intro k; cases k.down
  entry_diag := by intro k; cases k.down
  entry_zero := by
    intro i j _h
    simp [hD]
  divides_chain := by
    intro k
    cases (SmithNormalFormData.defaultOrder (ULift Empty) k).down

lemma isSmithNormalForm_zero
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    IsSmithNormalForm (0 : Matrix m n R) :=
  ⟨smithNormalFormData_zero 0 rfl⟩

/-- Zero matrices have a trivial Smith witness. -/
theorem hasSmithNormalForm_zero
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    HasSmithNormalForm (0 : Matrix m n R) := by
  refine ⟨1, 1, 0, gaussInvertibleMatrix_one, gaussInvertibleMatrix_one,
    isSmithNormalForm_zero, ?_⟩
  simp

/-- Base witness for matrices with empty row type. -/
theorem base_smith_empty_rows
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [IsEmpty m] (A : Matrix m n R) :
    HasSmithNormalForm A := by
  rw [gauss_matrix_eq_zero_of_isEmpty_rows A]
  exact hasSmithNormalForm_zero

/-- Base witness for matrices with empty column type. -/
theorem base_smith_empty_cols
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [IsEmpty n] (A : Matrix m n R) :
    HasSmithNormalForm A := by
  rw [gauss_matrix_eq_zero_of_isEmpty_cols A]
  exact hasSmithNormalForm_zero

/-- Reindexing preserves Smith normal form. -/
theorem isSmithNormalForm_reindex
    [Semiring R] {m' n' : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype m'] [DecidableEq m'] [Fintype n'] [DecidableEq n']
    (em : m ≃ m') (en : n ≃ n') {D : Matrix m n R}
    (hD : IsSmithNormalForm D) :
    IsSmithNormalForm (Matrix.reindex em en D) := by
  rcases hD with ⟨data⟩
  refine ⟨{
    r := data.r
    fintype_r := data.fintype_r
    order := data.order
    row := fun k => em (data.row k)
    col := fun k => en (data.col k)
    diag := data.diag
    row_injective := ?_
    col_injective := ?_
    entry_diag := ?_
    entry_zero := ?_
    divides_chain := data.divides_chain
  }⟩
  · intro a b h
    exact data.row_injective (em.injective h)
  · intro a b h
    exact data.col_injective (en.injective h)
  · intro k
    simpa [Matrix.reindex_apply] using data.entry_diag k
  · intro i j h
    have hzero := data.entry_zero (em.symm i) (en.symm j) ?_
    · simpa [Matrix.reindex_apply] using hzero
    · intro k
      specialize h k
      rcases h with hrow | hcol
      · exact Or.inl (fun hk => hrow (by simp [hk]))
      · exact Or.inr (fun hk => hcol (by simp [hk]))

/-- Reindexing preserves Smith witnesses. -/
theorem hasSmithNormalForm_reindex
    [Semiring R] {m' n' : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype m'] [DecidableEq m'] [Fintype n'] [DecidableEq n']
    (em : m ≃ m') (en : n ≃ n') {A : Matrix m n R}
    (hA : HasSmithNormalForm A) :
    HasSmithNormalForm (Matrix.reindex em en A) := by
  rcases hA with ⟨P, Q, D, hP, hQ, hD, hEq⟩
  refine ⟨Matrix.reindex em em P, Matrix.reindex en en Q,
    Matrix.reindex em en D, gaussInvertibleMatrix_reindex em hP,
    gaussInvertibleMatrix_reindex en hQ,
    isSmithNormalForm_reindex em en hD, ?_⟩
  have hEq' := congrArg (Matrix.reindex em en) hEq
  simpa [Matrix.submatrix_mul_equiv, Matrix.mul_assoc] using hEq'

/-- Gauss/rank-normal-form data is a Smith payload with all diagonal entries `1`. -/
noncomputable def smithNormalFormData_of_gaussRankBlockData
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {G : Matrix m n R} (data : GaussRankBlockData G) :
    SmithNormalFormData G where
  r := data.r
  fintype_r := data.fintype_r
  order := SmithNormalFormData.defaultOrder data.r
  row := data.row
  col := data.col
  diag := fun _ => 1
  row_injective := data.row_injective
  col_injective := data.col_injective
  entry_diag := by
    intro k
    simpa using data.entry_one k
  entry_zero := by
    intro i j h
    exact data.entry_zero i j h
  divides_chain := by
    intro k hnext
    exact one_dvd _

/-- Rank normal form is a special case of the Smith predicate. -/
theorem isSmithNormalForm_of_gauss
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {G : Matrix m n R} (hG : IsGaussRankNormalForm G) :
    IsSmithNormalForm G := by
  rcases hG with ⟨data⟩
  exact ⟨smithNormalFormData_of_gaussRankBlockData data⟩

/-- A Gauss/rank-normal-form witness gives a Smith normal-form witness. -/
theorem hasSmithNormalForm_of_gauss
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m n R} (hA : HasGaussRankNormalForm A) :
    HasSmithNormalForm A := by
  rcases hA with ⟨P, Q, G, hP, hQ, hG, hEq⟩
  exact ⟨P, Q, G, hP, hQ, isSmithNormalForm_of_gauss hG, hEq⟩

/-- Transport a Smith witness across a two-sided invertible transformation. -/
theorem smith_transport_twoSidedUnits
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P₀ : Matrix m m R) (Q₀ : Matrix n n R)
    (A B : Matrix m n R)
    (hP₀ : GaussInvertibleMatrix P₀) (hQ₀ : GaussInvertibleMatrix Q₀)
    (hB : B = P₀ * A * Q₀)
    (hNF : HasSmithNormalForm B) :
    HasSmithNormalForm A := by
  rcases hNF with ⟨PB, QB, D, hPB, hQB, hD, hEqB⟩
  refine ⟨PB * P₀, Q₀ * QB, D, hPB.mul hP₀, hQ₀.mul hQB, hD, ?_⟩
  calc
    D = PB * B * QB := hEqB
    _ = PB * (P₀ * A * Q₀) * QB := by rw [hB]
    _ = (PB * P₀) * A * (Q₀ * QB) := by simp [Matrix.mul_assoc]

section DvdMatrix

variable [CommSemiring R]

lemma dvd_sum_finset {α : Type*} (s : Finset α) {a : R} (f : α → R)
    (h : ∀ x ∈ s, a ∣ f x) :
    a ∣ ∑ x ∈ s, f x := by
  exact Finset.dvd_sum h

lemma dvd_matrix_mul_left
    [Fintype m] [Fintype n] {p : Type u} [Fintype p]
    (a : R) (P : Matrix p m R) {A : Matrix m n R}
    (hA : ∀ i j, a ∣ A i j) :
    ∀ i j, a ∣ (P * A) i j := by
  intro i j
  classical
  rw [Matrix.mul_apply]
  apply dvd_sum_finset
  intro k _hk
  rcases hA k j with ⟨c, hc⟩
  refine ⟨P i k * c, ?_⟩
  rw [hc]
  ring

lemma dvd_matrix_mul_right
    [Fintype m] [Fintype n] {p : Type u} [Fintype p]
    (a : R) {A : Matrix m n R} (Q : Matrix n p R)
    (hA : ∀ i j, a ∣ A i j) :
    ∀ i j, a ∣ (A * Q) i j := by
  intro i j
  classical
  rw [Matrix.mul_apply]
  apply dvd_sum_finset
  intro k _hk
  rcases hA i k with ⟨c, hc⟩
  refine ⟨c * Q k j, ?_⟩
  rw [hc]
  ring

end DvdMatrix

section BlockLift

variable [CommSemiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Prepend one Smith pivot to Smith-normal-form data. -/
noncomputable def smithNormalFormData_blockDiag
    (d : R) {D : Matrix m n R} (hdiv : ∀ i j, d ∣ D i j)
    (data : SmithNormalFormData D) :
    SmithNormalFormData
      (fromBlocks (fun _ _ : Unit => d) 0 0 D :
        Matrix (Unit ⊕ m) (Unit ⊕ n) R) where
  r := Option data.r
  fintype_r := inferInstance
  order := SmithNormalFormData.consOrder data.order
  row := fun k =>
    match k with
    | none => Sum.inl ()
    | some k => Sum.inr (data.row k)
  col := fun k =>
    match k with
    | none => Sum.inl ()
    | some k => Sum.inr (data.col k)
  diag := fun k =>
    match k with
    | none => d
    | some k => data.diag k
  row_injective := by
    intro a b h
    cases a <;> cases b
    · rfl
    · cases h
    · cases h
    · simp only at h
      exact congrArg some (data.row_injective (Sum.inr.inj h))
  col_injective := by
    intro a b h
    cases a <;> cases b
    · rfl
    · cases h
    · cases h
    · simp only at h
      exact congrArg some (data.col_injective (Sum.inr.inj h))
  entry_diag := by
    intro k
    cases k with
    | none => simp
    | some k => simpa using data.entry_diag k
  entry_zero := by
    intro i j h
    cases i with
    | inl iu =>
        cases j with
        | inl ju =>
            exfalso
            exact (h none).elim (by simp) (by simp)
        | inr jn => simp
    | inr im =>
        cases j with
        | inl ju => simp
        | inr jn =>
            apply data.entry_zero
            intro k
            specialize h (some k)
            rcases h with hrow | hcol
            · exact Or.inl (fun hk => hrow (by simp [hk]))
            · exact Or.inr (fun hk => hcol (by simp [hk]))
  divides_chain := by
    intro k hnext
    let e : Fin (Fintype.card (Option data.r)) ≃
        Fin (Fintype.card data.r + 1) :=
      finCongr (Fintype.card_option (α := data.r))
    have hkval : (e k : Nat) = (k : Nat) := by
      simp [e, finCongr]
    have hnext' : (e k : Nat) + 1 < Fintype.card data.r + 1 := by
      simpa [e, finCongr] using hnext
    cases hcase : e k using Fin.cases with
    | zero =>
        have hkval0 : (k : Nat) = 0 := by
          rw [← hkval, hcase]
          rfl
        have hk : k = e.symm 0 := by
          apply e.injective
          simp [hcase]
        have htail0 : 0 < Fintype.card data.r := by
          have hnext0 : 0 + 1 < Fintype.card data.r + 1 := by
            simpa [hcase] using hnext'
          exact Nat.succ_lt_succ_iff.mp hnext0
        have hnext_eq :
            (⟨(k : Nat) + 1, hnext⟩ : Fin (Fintype.card (Option data.r))) =
              e.symm (Fin.succ ⟨0, htail0⟩) := by
          apply e.injective
          ext
          simp [e, finCongr, hkval0]
        have hdvd := hdiv (data.row (data.order ⟨0, htail0⟩))
          (data.col (data.order ⟨0, htail0⟩))
        simpa [hk, hnext_eq, e, SmithNormalFormData.consOrder,
          data.entry_diag (data.order ⟨0, htail0⟩)] using hdvd
    | succ ktail =>
        have hkvalSucc : (k : Nat) = (ktail : Nat) + 1 := by
          rw [← hkval, hcase]
          simp [Fin.val_succ]
        have hk : k = e.symm (Fin.succ ktail) := by
          apply e.injective
          simp [hcase]
        have htail : (ktail : Nat) + 1 < Fintype.card data.r := by
          have hnextSucc : (ktail : Nat) + 1 + 1 < Fintype.card data.r + 1 := by
            simpa [hcase, Fin.val_succ, Nat.add_assoc] using hnext'
          exact Nat.succ_lt_succ_iff.mp (by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hnextSucc)
        have hnext_eq :
            (⟨(k : Nat) + 1, hnext⟩ : Fin (Fintype.card (Option data.r))) =
              e.symm (Fin.succ ⟨(ktail : Nat) + 1, htail⟩) := by
          apply e.injective
          ext
          simp [e, finCongr, hkvalSucc, Nat.add_assoc]
        simpa [hk, hnext_eq, e, SmithNormalFormData.consOrder] using
          data.divides_chain ktail htail

lemma isSmithNormalForm_blockDiag
    (d : R) {D : Matrix m n R} (hdiv : ∀ i j, d ∣ D i j)
    (hD : IsSmithNormalForm D) :
    IsSmithNormalForm
      (fromBlocks (fun _ _ : Unit => d) 0 0 D :
        Matrix (Unit ⊕ m) (Unit ⊕ n) R) := by
  rcases hD with ⟨data⟩
  exact ⟨smithNormalFormData_blockDiag d hdiv data⟩

/-- Lift a tail Smith witness through a block diagonal head pivot. -/
theorem smith_blockDiag_pivot
    (d : R) {A : Matrix m n R} (hdivA : ∀ i j, d ∣ A i j)
    (hA : HasSmithNormalForm A) :
    HasSmithNormalForm
      (fromBlocks (fun _ _ : Unit => d) 0 0 A :
        Matrix (Unit ⊕ m) (Unit ⊕ n) R) := by
  rcases hA with ⟨P, Q, D, hP, hQ, hD, hEq⟩
  let Pblk : Matrix (Unit ⊕ m) (Unit ⊕ m) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 P
  let Qblk : Matrix (Unit ⊕ n) (Unit ⊕ n) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 Q
  let Dblk : Matrix (Unit ⊕ m) (Unit ⊕ n) R :=
    fromBlocks (fun _ _ : Unit => d) 0 0 D
  have hdivD : ∀ i j, d ∣ D i j := by
    rw [hEq]
    exact dvd_matrix_mul_right d Q (dvd_matrix_mul_left d P hdivA)
  refine ⟨Pblk, Qblk, Dblk, ?_, ?_, ?_, ?_⟩
  · exact gaussInvertibleMatrix_blockDiag_one hP
  · exact gaussInvertibleMatrix_blockDiag_one hQ
  · exact isSmithNormalForm_blockDiag d hdivD hD
  · calc
      Dblk = fromBlocks (fun _ _ : Unit => d) 0 0 (P * A * Q) := by
        simp [Dblk, hEq]
      _ = Pblk *
            (fromBlocks (fun _ _ : Unit => d) 0 0 A :
              Matrix (Unit ⊕ m) (Unit ⊕ n) R) * Qblk := by
        simp [Pblk, Qblk, fromBlocks_multiply, Matrix.mul_assoc]

/-- Lift from an isolated-pivot Smith-ready matrix in head-tail coordinates. -/
theorem smith_of_blockReady_reindex
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R)
    (d : R)
    (h₁₁ : A.toBlocks₁₁ = fun _ _ : Unit => d)
    (h₁₂ : A.toBlocks₁₂ = 0) (h₂₁ : A.toBlocks₂₁ = 0)
    (hdiv : ∀ i j, d ∣ A.toBlocks₂₂ i j)
    (hTail : HasSmithNormalForm A.toBlocks₂₂) :
    HasSmithNormalForm A := by
  have hA :
      A =
        fromBlocks (fun _ _ : Unit => d) 0 0 A.toBlocks₂₂ := by
    exact (Matrix.ext_iff_blocks).2 ⟨h₁₁, h₁₂, h₂₁, rfl⟩
  rw [hA]
  exact smith_blockDiag_pivot d hdiv hTail

theorem smith_reindex
    {m' n' : Type u} [Fintype m'] [DecidableEq m'] [Fintype n'] [DecidableEq n']
    (em : m ≃ m') (en : n ≃ n') {A : Matrix m n R}
    (hA : HasSmithNormalForm A) :
    HasSmithNormalForm (Matrix.reindex em en A) :=
  hasSmithNormalForm_reindex em en hA

section AppendZeroCols

variable {κ : Type u} [Fintype κ] [DecidableEq κ]

/-- Append a zero column block to the right of a rectangular matrix. -/
def smithAppendZeroCols (A : Matrix m n R) : Matrix m (n ⊕ κ) R :=
  fun i j =>
    match j with
    | Sum.inl j' => A i j'
    | Sum.inr _ => 0

/-- The rectangular projection matrix `[I 0]`. -/
def smithLeftProjection : Matrix n (n ⊕ κ) R :=
  fun i j =>
    match j with
    | Sum.inl j' => if i = j' then 1 else 0
    | Sum.inr _ => 0

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype κ] [DecidableEq κ] in
@[simp] lemma smithAppendZeroCols_inl (A : Matrix m n R) (i : m) (j : n) :
    smithAppendZeroCols (κ := κ) A i (Sum.inl j) = A i j :=
  rfl

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype κ] [DecidableEq κ] in
@[simp] lemma smithAppendZeroCols_inr (A : Matrix m n R) (i : m) (j : κ) :
    smithAppendZeroCols (κ := κ) A i (Sum.inr j) = 0 :=
  rfl

/-- Smith-normal-form data remains valid after appending zero columns. -/
noncomputable def smithNormalFormData_appendZeroCols
    {D : Matrix m n R} (data : SmithNormalFormData D) :
    SmithNormalFormData (smithAppendZeroCols (κ := κ) D) where
  r := data.r
  fintype_r := data.fintype_r
  order := data.order
  row := data.row
  col := fun k => Sum.inl (data.col k)
  diag := data.diag
  row_injective := data.row_injective
  col_injective := by
    intro a b h
    exact data.col_injective (Sum.inl.inj h)
  entry_diag := by
    intro k
    exact data.entry_diag k
  entry_zero := by
    intro i j h
    cases j with
    | inl jn =>
        apply data.entry_zero
        intro k
        specialize h k
        rcases h with hrow | hcol
        · exact Or.inl hrow
        · exact Or.inr (fun hk => hcol (by simp [hk]))
    | inr jk =>
        rfl
  divides_chain := data.divides_chain

lemma isSmithNormalForm_appendZeroCols
    {D : Matrix m n R} (hD : IsSmithNormalForm D) :
    IsSmithNormalForm (smithAppendZeroCols (κ := κ) D) := by
  rcases hD with ⟨data⟩
  exact ⟨smithNormalFormData_appendZeroCols (κ := κ) data⟩

lemma gaussInvertibleMatrix_blockDiag_right_one
    {Q : Matrix n n R} (hQ : GaussInvertibleMatrix Q) :
    GaussInvertibleMatrix
      (fromBlocks Q 0 0 (1 : Matrix κ κ R) :
        Matrix (n ⊕ κ) (n ⊕ κ) R) := by
  rcases hQ with ⟨Qinv, hleft, hright⟩
  refine ⟨fromBlocks Qinv 0 0 (1 : Matrix κ κ R), ?_, ?_⟩
  · calc
      (fromBlocks Qinv 0 0 (1 : Matrix κ κ R) :
          Matrix (n ⊕ κ) (n ⊕ κ) R) *
          fromBlocks Q 0 0 (1 : Matrix κ κ R) =
          fromBlocks (Qinv * Q) 0 0 (1 : Matrix κ κ R) := by
        simp [fromBlocks_multiply]
      _ = 1 := by
        rw [hleft]
        exact Matrix.fromBlocks_one
  · calc
      (fromBlocks Q 0 0 (1 : Matrix κ κ R) :
          Matrix (n ⊕ κ) (n ⊕ κ) R) *
          fromBlocks Qinv 0 0 (1 : Matrix κ κ R) =
          fromBlocks (Q * Qinv) 0 0 (1 : Matrix κ κ R) := by
        simp [fromBlocks_multiply]
      _ = 1 := by
        rw [hright]
        exact Matrix.fromBlocks_one

omit [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ] in
lemma matrix_mul_appendZeroCols
    {ℓ : Type u} [Fintype ℓ]
    (P : Matrix ℓ m R) (A : Matrix m n R) :
    P * smithAppendZeroCols (κ := κ) A =
      smithAppendZeroCols (κ := κ) (P * A) := by
  ext i j
  cases j <;> simp [smithAppendZeroCols, Matrix.mul_apply]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
lemma appendZeroCols_mul_blockDiag_right
    (A : Matrix m n R) (Q : Matrix n n R) :
    smithAppendZeroCols (κ := κ) A *
        (fromBlocks Q 0 0 (1 : Matrix κ κ R) :
          Matrix (n ⊕ κ) (n ⊕ κ) R) =
      smithAppendZeroCols (κ := κ) (A * Q) := by
  ext i j
  cases j with
  | inl jn =>
      simp [smithAppendZeroCols, Matrix.mul_apply, Matrix.fromBlocks]
  | inr jk =>
      simp [smithAppendZeroCols, Matrix.mul_apply, Matrix.fromBlocks]

omit [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ] in
lemma matrix_mul_smithLeftProjection (A : Matrix m n R) :
    A * smithLeftProjection (κ := κ) =
      smithAppendZeroCols (κ := κ) A := by
  ext i j
  cases j with
  | inl jn =>
      simp [smithLeftProjection, smithAppendZeroCols, Matrix.mul_apply]
  | inr jk =>
      simp [smithLeftProjection, smithAppendZeroCols, Matrix.mul_apply]

/-- Appending zero columns preserves the project-level Smith witness. -/
theorem hasSmithNormalForm_appendZeroCols
    {A : Matrix m n R} (hA : HasSmithNormalForm A) :
    HasSmithNormalForm (smithAppendZeroCols (κ := κ) A) := by
  rcases hA with ⟨P, Q, D, hP, hQ, hD, hEq⟩
  let Qblk : Matrix (n ⊕ κ) (n ⊕ κ) R :=
    fromBlocks Q 0 0 (1 : Matrix κ κ R)
  refine ⟨P, Qblk, smithAppendZeroCols (κ := κ) D, hP,
    gaussInvertibleMatrix_blockDiag_right_one (κ := κ) hQ,
    isSmithNormalForm_appendZeroCols (κ := κ) hD, ?_⟩
  calc
    smithAppendZeroCols (κ := κ) D =
        smithAppendZeroCols (κ := κ) (P * A * Q) := by
      rw [hEq]
    _ = smithAppendZeroCols (κ := κ) (P * (A * Q)) := by
      rw [Matrix.mul_assoc]
    _ = P * smithAppendZeroCols (κ := κ) (A * Q) := by
      rw [matrix_mul_appendZeroCols]
    _ = P * (smithAppendZeroCols (κ := κ) A * Qblk) := by
      rw [appendZeroCols_mul_blockDiag_right]
    _ = P * smithAppendZeroCols (κ := κ) A * Qblk := by
      rw [Matrix.mul_assoc]

end AppendZeroCols

end BlockLift

end MatDecompFormal.Instances
