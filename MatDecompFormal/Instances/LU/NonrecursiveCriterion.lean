import MatDecompFormal.Instances.LU.Direct
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Order.Fin.Tuple

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Components.Properties

/-!
# LU Nonrecursive No-Pivot Criterion

This file exposes a non-recursive public no-pivot condition for LU.  Instead of
defining the hypothesis by recursively calling itself on the Schur complement,
we quantify over the finite Schur-complement descent relation and ask that every
nontrivial descendant have a nonzero head pivot.
-/

variable {R : Type*}

section ReindexLU

variable {ι κ : Type*} [Semiring R]
variable [Fintype ι] [DecidableEq ι] [LinearOrder ι]
variable [Fintype κ] [DecidableEq κ] [LinearOrder κ]

/-- LU witnesses transport across order-preserving reindexing. -/
theorem hasLU_reindex_orderIso
    (e : ι ≃o κ) {A : Matrix ι ι R} (hA : HasLU A) :
    HasLU (Matrix.reindex e.toEquiv e.toEquiv A) := by
  rcases hA with ⟨⟨L, U⟩, ⟨hL, hU⟩, hEq⟩
  refine ⟨(Matrix.reindex e.toEquiv e.toEquiv L,
    Matrix.reindex e.toEquiv e.toEquiv U), ?_, ?_⟩
  · constructor
    · exact (isUnitLowerTriangular_reindex
        (e := e.toEquiv) (h_mono := e.strictMono) (A := L)).1 hL
    · exact (isUpperTriangular_reindex
        (e := e.toEquiv) (h_mono := e.strictMono) (A := U)).1 hU
  · change Matrix.reindex e.toEquiv e.toEquiv A =
      Matrix.reindex e.toEquiv e.toEquiv L *
        Matrix.reindex e.toEquiv e.toEquiv U
    rw [hEq]
    exact (Matrix.submatrix_mul_equiv L U e.symm e.symm.toEquiv e.symm).symm

lemma reindex_symm_eq_of_reindex_eq
    {α β : Type*} (e : α ≃ β) {A : Matrix α α R} {B : Matrix β β R}
    (h : Matrix.reindex e e A = B) :
    Matrix.reindex e.symm e.symm B = A := by
  rw [← h]
  ext i j
  simp [Matrix.reindex_apply]

end ReindexLU

section LeadingPrincipalBlocks

variable {τ : Type*}
variable [Field R] [Fintype τ] [DecidableEq τ]

/-- The Schur complement of the head block in a `Unit ⊕ τ` head-tail matrix. -/
noncomputable def headTailSchurComplement
    (A : Matrix (Unit ⊕ τ) (Unit ⊕ τ) R)
    [Invertible A.toBlocks₁₁] :
    Matrix τ τ R :=
  A.toBlocks₂₂ - A.toBlocks₂₁ * ⅟(A.toBlocks₁₁) * A.toBlocks₁₂

/--
The principal block containing the head and the tail indices satisfying `p`,
written in head-tail coordinates.
-/
noncomputable def headTailPrincipalBlock
    (A : Matrix (Unit ⊕ τ) (Unit ⊕ τ) R)
    (p : τ → Prop) [DecidablePred p] :
    Matrix (Unit ⊕ { i : τ // p i }) (Unit ⊕ { i : τ // p i }) R :=
  Matrix.fromBlocks
    A.toBlocks₁₁
    (A.toBlocks₁₂.submatrix id Subtype.val)
    (A.toBlocks₂₁.submatrix Subtype.val id)
    (A.toBlocks₂₂.submatrix Subtype.val Subtype.val)

/-- The `p`-tail principal block of the head Schur complement. -/
noncomputable def schurPrincipalBlock
    (A : Matrix (Unit ⊕ τ) (Unit ⊕ τ) R)
    (p : τ → Prop) [DecidablePred p]
    [Invertible A.toBlocks₁₁] :
    Matrix { i : τ // p i } { i : τ // p i } R :=
  (headTailSchurComplement A).submatrix Subtype.val Subtype.val

lemma headTailPrincipalBlock_schur_eq
    (A : Matrix (Unit ⊕ τ) (Unit ⊕ τ) R)
    (p : τ → Prop) [DecidablePred p]
    [Invertible A.toBlocks₁₁] :
    (A.toBlocks₂₂.submatrix Subtype.val Subtype.val -
        A.toBlocks₂₁.submatrix Subtype.val id *
          ⅟(A.toBlocks₁₁) *
          A.toBlocks₁₂.submatrix id Subtype.val) =
      schurPrincipalBlock A p := by
  ext i j
  simp [schurPrincipalBlock, headTailSchurComplement, Matrix.mul_apply]

/--
Schur-complement determinant product formula for a head-containing principal
block.  Taking `p` to be the first `k` tail indices gives the usual relation
between consecutive leading principal minors:

`det Δ(head ∪ p) = det A₁₁ * det Δ_p(Schur(A))`.
-/
theorem det_headTailPrincipalBlock_eq_det_mul_schurPrincipalBlock
    (A : Matrix (Unit ⊕ τ) (Unit ⊕ τ) R)
    (p : τ → Prop) [DecidablePred p]
    [Invertible A.toBlocks₁₁] :
    (headTailPrincipalBlock A p).det =
      A.toBlocks₁₁.det * (schurPrincipalBlock A p).det := by
  rw [headTailPrincipalBlock]
  rw [Matrix.det_fromBlocks₁₁]
  rw [headTailPrincipalBlock_schur_eq (A := A) (p := p)]

end LeadingPrincipalBlocks

section FinLeadingPrincipalMinors

variable [Field R]

/-- The canonical head-tail equivalence for `Fin (n + 1)`, splitting off `0`. -/
noncomputable def finHeadTailEquiv (n : Nat) :
    Fin (n + 1) ≃ Unit ⊕ Fin n :=
  (Equiv.sumCompl (fun i : Fin (n + 1) => i = 0)).symm.trans
    (Equiv.sumCongr
      ({ toFun := fun _ => (),
         invFun := fun _ => ⟨0, rfl⟩,
         left_inv := by
           intro x
           rcases x with ⟨x, hx⟩
           subst hx
           rfl,
         right_inv := by
           intro u
           cases u
           rfl } : { i : Fin (n + 1) // i = 0 } ≃ Unit)
      ((finSuccAboveOrderIso (0 : Fin (n + 1))).symm.toEquiv))

/-- The leading `k × k` principal block of a `Fin n` indexed matrix. -/
noncomputable def leadingPrincipalBlock
    {n : Nat} (A : Matrix (Fin n) (Fin n) R)
    (k : Nat) (hk : k ≤ n) :
    Matrix (Fin k) (Fin k) R :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

/-- The leading principal minor of order `k`. -/
noncomputable def leadingPrincipalMinor
    {n : Nat} (A : Matrix (Fin n) (Fin n) R)
    (k : Nat) (hk : k ≤ n) : R :=
  (leadingPrincipalBlock A k hk).det

@[simp] lemma finHeadTailEquiv_symm_inl (n : Nat) :
    (finHeadTailEquiv n).symm (Sum.inl ()) = (0 : Fin (n + 1)) := by
  rfl

@[simp] lemma finHeadTailEquiv_symm_inr (n : Nat) (i : Fin n) :
    (finHeadTailEquiv n).symm (Sum.inr i) = Fin.succ i := by
  rfl

@[simp] lemma finHeadTailEquiv_apply_zero (n : Nat) :
    finHeadTailEquiv n (0 : Fin (n + 1)) = Sum.inl () := by
  apply (finHeadTailEquiv n).symm.injective
  simp

@[simp] lemma finHeadTailEquiv_apply_succ (n : Nat) (i : Fin n) :
    finHeadTailEquiv n (Fin.succ i) = Sum.inr i := by
  apply (finHeadTailEquiv n).symm.injective
  simp

@[simp] lemma Fin.castLE_castLEOrderIso_symm
    {n k : Nat} (hk : k ≤ n)
    (i : { i : Fin n // (i : Nat) < k }) :
    Fin.castLE hk ((Fin.castLEOrderIso hk).symm i) = (i : Fin n) := by
  apply Fin.ext
  simp [Fin.castLEOrderIso]

@[simp] lemma headElem_fin_succ (n : Nat) :
    headElem (α := Fin (n + 1)) = 0 := by
  apply le_antisymm
  · exact headElem_le (α := Fin (n + 1)) 0
  · exact Fin.zero_le _

/--
The leading `(k + 1) × (k + 1)` block of a `Fin (n + 1)` matrix is the same,
up to reindexing, as the head-containing head-tail principal block formed from
the first `k` tail indices.
-/
theorem det_leadingPrincipalBlock_succ_eq_headTailPrincipalBlock
    {n k : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hk : k ≤ n) :
    (leadingPrincipalBlock A (k + 1) (Nat.succ_le_succ hk)).det =
      (headTailPrincipalBlock
        (Matrix.reindex (finHeadTailEquiv n) (finHeadTailEquiv n) A)
        (fun i : Fin n => (i : Nat) < k)).det := by
  let eSmall : Fin (k + 1) ≃ Unit ⊕ { i : Fin n // (i : Nat) < k } :=
    (finHeadTailEquiv k).trans
      (Equiv.sumCongr (Equiv.refl Unit)
        ((Fin.castLEOrderIso hk).toEquiv))
  rw [show (leadingPrincipalBlock A (k + 1) (Nat.succ_le_succ hk)).det =
      (Matrix.reindex eSmall eSmall
        (leadingPrincipalBlock A (k + 1) (Nat.succ_le_succ hk))).det by
        rw [Matrix.det_reindex_self]]
  congr 1
  ext i j
  cases i with
  | inl u =>
      cases u
      cases j with
      | inl v =>
          cases v
          simp [leadingPrincipalBlock, headTailPrincipalBlock, eSmall,
            Matrix.toBlocks₁₁, Matrix.reindex_apply]
      | inr jj =>
          simp [leadingPrincipalBlock, headTailPrincipalBlock, eSmall,
            Matrix.toBlocks₁₂, Matrix.reindex_apply]
  | inr ii =>
      cases j with
      | inl v =>
          cases v
          simp [leadingPrincipalBlock, headTailPrincipalBlock, eSmall,
            Matrix.toBlocks₂₁, Matrix.reindex_apply]
      | inr jj =>
          simp [leadingPrincipalBlock, headTailPrincipalBlock, eSmall,
            Matrix.toBlocks₂₂, Matrix.reindex_apply]

lemma det_schurPrincipalBlock_eq_leadingPrincipalMinor
    {n k : Nat}
    (A : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) R)
    (hk : k ≤ n)
    [Invertible A.toBlocks₁₁] :
    (schurPrincipalBlock A (fun i : Fin n => (i : Nat) < k)).det =
      leadingPrincipalMinor (headTailSchurComplement A) k hk := by
  rw [leadingPrincipalMinor, leadingPrincipalBlock, schurPrincipalBlock]
  rw [show
      (headTailSchurComplement A).submatrix Subtype.val Subtype.val =
        Matrix.reindex ((Fin.castLEOrderIso hk).toEquiv)
          ((Fin.castLEOrderIso hk).toEquiv)
          ((headTailSchurComplement A).submatrix
            (Fin.castLE hk) (Fin.castLE hk)) by
    ext i j
    simp [Matrix.reindex_apply]]
  rw [Matrix.det_reindex_self]

/--
Schur-complement determinant product formula for consecutive leading principal
minors of a `Fin (n + 1)` indexed matrix.  After splitting off index `0`, the
leading `(k + 1)` minor is the head pivot determinant times the leading `k`
minor of the Schur complement.
-/
theorem leadingPrincipalMinor_succ_eq_head_det_mul_schur
    {n k : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hk : k ≤ n)
    [Invertible
      (Matrix.reindex (finHeadTailEquiv n) (finHeadTailEquiv n) A).toBlocks₁₁] :
    leadingPrincipalMinor A (k + 1) (Nat.succ_le_succ hk) =
      (Matrix.reindex (finHeadTailEquiv n) (finHeadTailEquiv n) A).toBlocks₁₁.det *
        leadingPrincipalMinor
          (headTailSchurComplement
            (Matrix.reindex (finHeadTailEquiv n) (finHeadTailEquiv n) A))
          k hk := by
  rw [leadingPrincipalMinor]
  rw [det_leadingPrincipalBlock_succ_eq_headTailPrincipalBlock (A := A) hk]
  rw [det_headTailPrincipalBlock_eq_det_mul_schurPrincipalBlock]
  congr 1
  rw [det_schurPrincipalBlock_eq_leadingPrincipalMinor]

/-- All proper nonzero-order leading principal minors of a `Fin n` matrix are nonzero. -/
noncomputable def HasNonzeroProperLeadingPrincipalMinors
    {n : Nat} (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ k, 0 < k → ∀ hk : k < n, leadingPrincipalMinor A k (Nat.le_of_lt hk) ≠ 0

lemma leadingPrincipalMinor_one_eq_head_det
    {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    leadingPrincipalMinor A 1 (Nat.succ_le_succ (Nat.zero_le n)) =
      (Matrix.reindex (finHeadTailEquiv n) (finHeadTailEquiv n) A).toBlocks₁₁.det := by
  rw [leadingPrincipalMinor]
  rw [det_leadingPrincipalBlock_succ_eq_headTailPrincipalBlock
    (A := A) (k := 0) (hk := Nat.zero_le n)]
  rw [headTailPrincipalBlock]
  haveI : Subsingleton (Unit ⊕ { i : Fin n // (i : Nat) < 0 }) := by
    constructor
    intro x y
    cases x with
    | inl ux =>
        cases ux
        cases y with
        | inl uy =>
            cases uy
            rfl
        | inr iy =>
            exact (Nat.not_lt_zero _ iy.2).elim
    | inr ix =>
        exact (Nat.not_lt_zero _ ix.2).elim
  rw [Matrix.det_eq_elem_of_subsingleton _ (Sum.inl ())]
  rw [Matrix.det_eq_elem_of_subsingleton _ ()]
  simp [Matrix.toBlocks₁₁]

lemma head_det_ne_zero_of_nonzeroProperLeadingPrincipalMinors
    {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : HasNonzeroProperLeadingPrincipalMinors A)
    (hn : 0 < n) :
    (Matrix.reindex (finHeadTailEquiv n) (finHeadTailEquiv n) A).toBlocks₁₁.det ≠ 0 := by
  rw [← leadingPrincipalMinor_one_eq_head_det A]
  exact hA 1 Nat.succ_pos' (Nat.succ_lt_succ hn)

lemma luPivotReady_iff_leadingPrincipalMinor_one_ne_zero
    {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    LUPivotReady (Fin (n + 1)) A ↔
      leadingPrincipalMinor A 1 (Nat.succ_le_succ (Nat.zero_le n)) ≠ 0 := by
  rw [leadingPrincipalMinor_one_eq_head_det]
  rw [Matrix.det_eq_elem_of_subsingleton _ ()]
  simp [LUPivotReady, PLUPivotReady, Matrix.toBlocks₁₁, Matrix.reindex_apply]

lemma schur_nonzeroProperLeadingPrincipalMinors_of_nonzeroProperLeadingPrincipalMinors
    {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : HasNonzeroProperLeadingPrincipalMinors A)
    [Invertible
      (Matrix.reindex (finHeadTailEquiv n) (finHeadTailEquiv n) A).toBlocks₁₁] :
    HasNonzeroProperLeadingPrincipalMinors
      (headTailSchurComplement
        (Matrix.reindex (finHeadTailEquiv n) (finHeadTailEquiv n) A)) := by
  intro k _hkpos hk
  have hk_le : k ≤ n := Nat.le_of_lt hk
  have hprod := leadingPrincipalMinor_succ_eq_head_det_mul_schur
    (A := A) (k := k) (hk := hk_le)
  have hsucc_ne :
      leadingPrincipalMinor A (k + 1) (Nat.succ_le_succ hk_le) ≠ 0 :=
    hA (k + 1) (Nat.succ_pos k) (Nat.succ_lt_succ hk)
  intro hzero
  apply hsucc_ne
  rw [hprod, hzero, mul_zero]

end FinLeadingPrincipalMinors

section FinLUSchurSlice

variable [Field R]

/-- Reindex the project tail subtype for `Fin (n + 1)` back to `Fin n`. -/
noncomputable def luFinTailEquiv (n : Nat) :
    LUTailIdx (Fin (n + 1)) ≃ Fin n :=
  (Equiv.subtypeEquivRight
      (fun x : Fin (n + 1) => by simp [headElem_fin_succ])).trans
    ((finSuccAboveOrderIso (0 : Fin (n + 1))).symm.toEquiv)

noncomputable def luFinTailCastOrderIso (n : Nat) :
    LUTailIdx (Fin (n + 1)) ≃o { x : Fin (n + 1) // x ≠ 0 } where
  toEquiv := Equiv.subtypeEquivRight
    (fun x : Fin (n + 1) => by simp [headElem_fin_succ])
  map_rel_iff' := by
    intro _ _
    rfl

/-- The project tail subtype for `Fin (n + 1)` is order-isomorphic to `Fin n`. -/
noncomputable def luFinTailOrderIso (n : Nat) :
    LUTailIdx (Fin (n + 1)) ≃o Fin n :=
  (luFinTailCastOrderIso n).trans
    (finSuccAboveOrderIso (0 : Fin (n + 1))).symm

/--
The project `luSchurSlice` on `Fin (n + 1)` agrees, after the canonical tail
reindexing, with the head-tail Schur complement used in the leading-minor
formula.
-/
theorem reindex_luSchurSlice_fin_eq_headTailSchurComplement
    {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    [Invertible
      (Matrix.reindex (finHeadTailEquiv n) (finHeadTailEquiv n) A).toBlocks₁₁] :
    Matrix.reindex (luFinTailEquiv n) (luFinTailEquiv n)
        (luSchurSlice (Fin (n + 1)) A) =
      headTailSchurComplement
        (Matrix.reindex (finHeadTailEquiv n) (finHeadTailEquiv n) A) := by
  ext i j
  simp [luFinTailEquiv, luSchurSlice, pluSchurSlice, pluHeadTailPlain,
    headTailSchurComplement, pluPivotLowerFactor, pluHeadInv,
    Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁,
    Matrix.reindex_apply, Matrix.mul_apply, finSuccAboveOrderIso_apply]

end FinLUSchurSlice


/-- One Schur-complement descent step in the LU no-pivot strategy. -/
noncomputable def LUSchurStep [DivisionRing R]
    (x y : SquareUniverse R) : Prop :=
  ∃ hcard : 1 < Fintype.card x.ι,
    haveI : Nonempty x.ι :=
      Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
    y = SquareUniverse.ofMatrix (luSchurSlice x.ι x.A)

/-- The current matrix has a nonzero LU head pivot whenever it is nontrivial. -/
def LUSchurPivotNonzero [Zero R] (x : SquareUniverse R) : Prop :=
  ∀ hcard : 1 < Fintype.card x.ι,
    haveI : Nonempty x.ι :=
      Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
    LUPivotReady x.ι x.A

/--
Non-recursive no-pivot condition from a universe object: every matrix reachable
by zero or more LU Schur-complement steps has a nonzero head pivot if its
dimension is at least two.
-/
noncomputable def HasNonzeroLUSchurPivotsFrom [DivisionRing R]
    (x₀ : SquareUniverse R) : Prop :=
  ∀ x, Relation.ReflTransGen (LUSchurStep (R := R)) x₀ x →
    LUSchurPivotNonzero x

/--
Non-recursive no-pivot condition for a concrete matrix: all Schur-complement
descendants encountered by the no-pivot LU descent have nonzero head pivots.
-/
noncomputable def HasNonzeroLUSchurPivots [DivisionRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) : Prop :=
  HasNonzeroLUSchurPivotsFrom (SquareUniverse.ofMatrix A)

theorem luRecursivePivotReady_of_nonzeroLUSchurPivotsFrom
    [DivisionRing R]
    (x : SquareUniverse R)
    (h : HasNonzeroLUSchurPivotsFrom x) :
    LURecursivePivotReady x.A := by
  classical
  by_cases hbase : Fintype.card x.ι ≤ 1
  · exact luRecursivePivotReady_of_card_le_one (A := x.A) hbase
  · have hcard : 1 < Fintype.card x.ι := Nat.lt_of_not_ge hbase
    haveI : Nonempty x.ι :=
      Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
    haveI : Nontrivial x.ι :=
      Fintype.one_lt_card_iff_nontrivial.mp hcard
    refine (luRecursivePivotReady_step_iff (A := x.A) hbase).2 ?_
    constructor
    · exact h x Relation.ReflTransGen.refl hcard
    · let y : SquareUniverse R :=
        SquareUniverse.ofMatrix (luSchurSlice x.ι x.A)
      have hxy : LUSchurStep (R := R) x y := by
        exact ⟨hcard, rfl⟩
      have hy : HasNonzeroLUSchurPivotsFrom y := by
        intro z hz
        exact h z (Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single hxy) hz)
      simpa [y] using
        luRecursivePivotReady_of_nonzeroLUSchurPivotsFrom y hy
termination_by Fintype.card x.ι
decreasing_by
  classical
  have hcard : 1 < Fintype.card x.ι := Nat.lt_of_not_ge hbase
  haveI : Nonempty x.ι :=
    Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
  have hlt : Fintype.card (LUTailIdx x.ι) < Fintype.card x.ι := by
    simpa [LUTailIdx, PLUTailIdx] using
      (Fintype.card_subtype_lt
        (p := fun a : x.ι => a ≠ headElem (α := x.ι))
        (x := headElem (α := x.ι))
        (by simp))
  simpa [SquareUniverse.ofMatrix, y] using hlt

theorem luRecursivePivotReady_of_nonzeroLUSchurPivots
    [DivisionRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R}
    (hA : HasNonzeroLUSchurPivots A) :
    LURecursivePivotReady A := by
  simpa [HasNonzeroLUSchurPivots] using
    luRecursivePivotReady_of_nonzeroLUSchurPivotsFrom
      (SquareUniverse.ofMatrix A) hA

theorem luRecursivePivotReady_of_reachable
    [DivisionRing R]
    {x y : SquareUniverse R}
    (hxy : Relation.ReflTransGen (LUSchurStep (R := R)) x y)
    (hx : LURecursivePivotReady x.A) :
    LURecursivePivotReady y.A := by
  classical
  induction hxy with
  | refl =>
      exact hx
  | @tail b c hxb hbc ih =>
      have hb : LURecursivePivotReady b.A := ih
      rcases hbc with ⟨hcard, rfl⟩
      have hbase : ¬ Fintype.card b.ι ≤ 1 := by
        exact Nat.not_le_of_gt hcard
      haveI : Nonempty b.ι :=
        Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
      haveI : Nontrivial b.ι :=
        Fintype.one_lt_card_iff_nontrivial.mp hcard
      exact (luRecursivePivotReady_step_iff (A := b.A) hbase).1 hb |>.2

theorem nonzeroLUSchurPivotsFrom_of_recursivePivotReady
    [DivisionRing R]
    (x : SquareUniverse R)
    (h : LURecursivePivotReady x.A) :
    HasNonzeroLUSchurPivotsFrom x := by
  classical
  intro y hxy hcard
  have hy : LURecursivePivotReady y.A :=
    luRecursivePivotReady_of_reachable hxy h
  have hbase : ¬ Fintype.card y.ι ≤ 1 := by
    exact Nat.not_le_of_gt hcard
  haveI : Nonempty y.ι :=
    Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hcard)
  haveI : Nontrivial y.ι :=
    Fintype.one_lt_card_iff_nontrivial.mp hcard
  exact (luRecursivePivotReady_step_iff (A := y.A) hbase).1 hy |>.1

theorem nonzeroLUSchurPivots_of_recursivePivotReady
    [DivisionRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R}
    (hA : LURecursivePivotReady A) :
    HasNonzeroLUSchurPivots A := by
  simpa [HasNonzeroLUSchurPivots] using
    nonzeroLUSchurPivotsFrom_of_recursivePivotReady
      (SquareUniverse.ofMatrix A) hA

/--
The Schur-descendant no-pivot API is equivalent to the internal recursive
pivot-readiness predicate consumed by the descent driver.
-/
theorem hasNonzeroLUSchurPivots_iff_recursivePivotReady
    [DivisionRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R} :
    HasNonzeroLUSchurPivots A ↔ LURecursivePivotReady A :=
  ⟨luRecursivePivotReady_of_nonzeroLUSchurPivots,
    nonzeroLUSchurPivots_of_recursivePivotReady⟩

/--
The determinant-style recursive criterion and the Schur-descendant criterion
describe the same no-pivot LU inputs.
-/
theorem hasNoZeroLUPivots_iff_nonzeroLUSchurPivots
    [Field R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R} :
    HasNoZeroLUPivots A ↔ HasNonzeroLUSchurPivots A := by
  rw [hasNoZeroLUPivots_iff_recursivePivotReady,
    hasNonzeroLUSchurPivots_iff_recursivePivotReady]


/--
The non-recursive Schur-descendant pivot criterion implies the existing
determinant-style recursive public criterion.
-/
theorem hasNoZeroLUPivots_of_nonzeroLUSchurPivots
    [Field R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι R}
    (hA : HasNonzeroLUSchurPivots A) :
    HasNoZeroLUPivots A :=
  (hasNoZeroLUPivots_iff_recursivePivotReady (A := A)).2
    (luRecursivePivotReady_of_nonzeroLUSchurPivots hA)

end MatDecompFormal.Instances
