import MatDecompFormal.Instances.Hessenberg.Strategy

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Hessenberg Boundary-Column Driver

This file starts the boundary-aware Hessenberg descent. It uses the generic
`SubtypeInductionInstance` directly because the universe is not merely square
matrices: it carries the parent boundary column needed for stable Hessenberg
lifting.
-/

/-- Boundary-universe measure: matrix dimension. -/
abbrev hessenbergBoundaryμ {R : Type*} (x : HessenbergBoundaryUniverse.{u} R) : Nat :=
  Fintype.card x.ι

/-- Boundary-universe base measure. -/
abbrev hessenbergBoundaryμBase : Nat := 0

/-- Positive-dimensional boundary universe objects have nonempty index types. -/
lemma posHessenbergBoundaryUniverse_nonempty {R : Type*}
    (x_sub : PosHessenbergBoundaryUniverse R) : Nonempty x_sub.1.ι := by
  classical
  exact Fintype.card_pos_iff.mp x_sub.2

/-- Head-tail view of a boundary-universe matrix. -/
noncomputable def hessenbergBoundaryHeadTailMatrix
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} (A : Matrix ι ι R) :
    Matrix (Unit ⊕ HessenbergTailIdx ι) (Unit ⊕ HessenbergTailIdx ι) R :=
  Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A

/--
The boundary column passed to the tail subproblem: the lower-left head-tail
block of the current matrix.
-/
noncomputable def hessenbergBoundaryLowerLeftColumn
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} (A : Matrix ι ι R) :
    Matrix (HessenbergTailIdx ι) Unit R :=
  (hessenbergBoundaryHeadTailMatrix ι A).toBlocks₂₁

/-- The recursive tail slice is the lower-right head-tail block. -/
theorem hessenbergTailSlice_eq_boundaryLowerRightBlock
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} (A : Matrix ι ι R) :
    hessenbergTailSlice ι A =
      (hessenbergBoundaryHeadTailMatrix ι A).toBlocks₂₂ := by
  rfl

/-- Lexicographic head-tail reindexing factors through the plain head-tail block view. -/
theorem hessenbergBoundaryHeadTailMatrix_reindex_sumToLex
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} (A : Matrix ι ι R) :
    Matrix.reindex (sumToLexEquiv Unit (HessenbergTailIdx ι))
        (sumToLexEquiv Unit (HessenbergTailIdx ι))
        (hessenbergBoundaryHeadTailMatrix ι A) =
      Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A := by
  simpa [hessenbergBoundaryHeadTailMatrix, headTailLexEquiv] using
    (reindex_reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι))
      (sumToLexEquiv Unit (HessenbergTailIdx ι))
      (sumToLexEquiv Unit (HessenbergTailIdx ι)) A)

/-- The lexicographic head-tail view is the block matrix of the plain head-tail blocks. -/
theorem hessenbergBoundaryHeadTailLex_fromBlocks
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} (A : Matrix ι ι R) :
    Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A =
      (fromBlocks
        (hessenbergBoundaryHeadTailMatrix ι A).toBlocks₁₁
        (hessenbergBoundaryHeadTailMatrix ι A).toBlocks₁₂
        (hessenbergBoundaryHeadTailMatrix ι A).toBlocks₂₁
        (hessenbergBoundaryHeadTailMatrix ι A).toBlocks₂₂ :
          Matrix (Unit ⊕ₗ HessenbergTailIdx ι) (Unit ⊕ₗ HessenbergTailIdx ι) R) := by
  rw [← hessenbergBoundaryHeadTailMatrix_reindex_sumToLex]
  rw [← reindex_sumToLex_fromBlocks]
  congr
  exact (fromBlocks_toBlocks (hessenbergBoundaryHeadTailMatrix ι A)).symm

/-- The concrete recursive boundary subproblem for a positive boundary universe. -/
noncomputable def hessenbergBoundarySliceSub
    {R : Type v} [Semiring R]
    (x_sub : PosHessenbergBoundaryUniverse R) :
    HessenbergBoundaryUniverse.{u} R := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact
    { ι := HessenbergTailIdx x_sub.1.ι
      A := hessenbergTailSlice x_sub.1.ι x_sub.1.A
      c := hessenbergBoundaryLowerLeftColumn x_sub.1.ι x_sub.1.A }

/-- Removing the head index strictly decreases the boundary-universe measure. -/
theorem hessenbergBoundarySliceProgress
    {R : Type v} [Semiring R]
    (x_sub : PosHessenbergBoundaryUniverse R) :
    hessenbergBoundaryμ (hessenbergBoundarySliceSub x_sub) <
      hessenbergBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} R) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  have hlt : Fintype.card (HessenbergTailIdx x_sub.1.ι) <
      Fintype.card x_sub.1.ι := by
    simpa [HessenbergTailIdx] using
      (Fintype.card_subtype_lt
        (p := fun i : x_sub.1.ι => i ≠ headElem (α := x_sub.1.ι))
        (x := headElem (α := x_sub.1.ι))
        (by simp))
  simpa [hessenbergBoundaryμ, hessenbergBoundarySliceSub] using hlt

/-- Block-diagonal extension by a one-dimensional head block. -/
def hessenbergBlockDiagOne
    {β R : Type*} [Zero R] [One R]
    (P : Matrix β β R) : Matrix (Unit ⊕ β) (Unit ⊕ β) R :=
  fromBlocks (1 : Matrix Unit Unit R) 0 0 P

/-- Explicit inverse witness for a block-diagonal one-head extension. -/
theorem hasMatrixInverse_blockDiagOne
    {β R : Type*} [Fintype β] [DecidableEq β] [Semiring R]
    {P Pinv : Matrix β β R} (hInv : HasMatrixInverse P Pinv) :
    HasMatrixInverse
      (hessenbergBlockDiagOne P : Matrix (Unit ⊕ β) (Unit ⊕ β) R)
      (hessenbergBlockDiagOne Pinv : Matrix (Unit ⊕ β) (Unit ⊕ β) R) := by
  constructor
  · simpa [hessenbergBlockDiagOne, Matrix.fromBlocks_multiply, hInv.1]
  · simpa [hessenbergBlockDiagOne, Matrix.fromBlocks_multiply, hInv.2]

/-- Explicit inverse witnesses are preserved by simultaneous reindexing. -/
theorem hasMatrixInverse_reindex
    {α β R : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Semiring R] (e : α ≃ β)
    {P Pinv : Matrix α α R} (hInv : HasMatrixInverse P Pinv) :
    HasMatrixInverse (Matrix.reindex e e P) (Matrix.reindex e e Pinv) := by
  constructor
  · have h := congrArg (Matrix.reindex e e) hInv.1
    simpa [Matrix.submatrix_mul_equiv] using h
  · have h := congrArg (Matrix.reindex e e) hInv.2
    simpa [Matrix.submatrix_mul_equiv] using h

/-- Same-index boundary object obtained by applying an invertible similarity. -/
def hessenbergBoundarySimilarityObject
    {R : Type*} [Semiring R]
    (x : HessenbergBoundaryUniverse.{u} R)
    (P Pinv : Matrix x.ι x.ι R) : HessenbergBoundaryUniverse.{u} R :=
  { ι := x.ι
    A := Pinv * x.A * P
    c := Pinv * x.c }

/--
Boundary readiness: the protected column already has the first-column shape
required for a parent Hessenberg lift.
-/
def HessenbergBoundaryReady
    {R : Type*} [Zero R] (x : HessenbergBoundaryUniverse.{u} R) : Prop :=
  ∀ (_h : Nonempty x.ι), ∀ i : x.ι,
    i ≠ headElem (α := x.ι) → x.c i () = 0

theorem hessenbergBoundaryReady_iff_identity_boundary
    {R : Type*} [Semiring R] (x : HessenbergBoundaryUniverse.{u} R)
    (h : Nonempty x.ι) :
    HessenbergBoundaryReady x ↔
      (∀ i : x.ι, i ≠ headElem (α := x.ι) → ((1 : Matrix x.ι x.ι R) * x.c) i () = 0) := by
  constructor
  · intro hready i hi
    simpa using hready h i hi
  · intro hready hne i hi
    simpa using hready i hi

/--
Under a block-diagonal tail similarity, the lower-left boundary column is
transformed exactly by the tail inverse.
-/
theorem hessenbergBlockDiagOne_lowerLeftColumn
    {β R : Type*} [Fintype β] [DecidableEq β] [Semiring R]
    (A₁₁ : Matrix Unit Unit R) (A₁₂ : Matrix Unit β R)
    (c : Matrix β Unit R) (A₂₂ : Matrix β β R)
    (P Pinv : Matrix β β R) :
    (hessenbergBlockDiagOne Pinv *
        (fromBlocks A₁₁ A₁₂ c A₂₂ : Matrix (Unit ⊕ β) (Unit ⊕ β) R) *
          hessenbergBlockDiagOne P).toBlocks₂₁ =
      Pinv * c := by
  simp [hessenbergBlockDiagOne, Matrix.fromBlocks_multiply, Matrix.mul_assoc]

/--
Under a block-diagonal tail similarity, the lower-right block is the tail
similarity of the lower-right block.
-/
theorem hessenbergBlockDiagOne_lowerRightBlock
    {β R : Type*} [Fintype β] [DecidableEq β] [Semiring R]
    (A₁₁ : Matrix Unit Unit R) (A₁₂ : Matrix Unit β R)
    (c : Matrix β Unit R) (A₂₂ : Matrix β β R)
    (P Pinv : Matrix β β R) :
    (hessenbergBlockDiagOne Pinv *
        (fromBlocks A₁₁ A₁₂ c A₂₂ : Matrix (Unit ⊕ β) (Unit ⊕ β) R) *
          hessenbergBlockDiagOne P).toBlocks₂₂ =
      Pinv * A₂₂ * P := by
  simp [hessenbergBlockDiagOne, Matrix.fromBlocks_multiply, Matrix.mul_assoc]

/--
The tail boundary condition is exactly the parent lower-left readiness condition
after a block-diagonal tail similarity.
-/
theorem hessenbergBlockDiagOne_ready_lowerLeft
    {β R : Type*} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [Semiring R]
    (A₁₁ : Matrix Unit Unit R) (A₁₂ : Matrix Unit β R)
    (c : Matrix β Unit R) (A₂₂ : Matrix β β R)
    (P Pinv : Matrix β β R)
    (hBoundary : ∀ i : β, i ≠ headElem (α := β) → (Pinv * c) i () = 0) :
    ∀ i : β, i ≠ headElem (α := β) →
      (hessenbergBlockDiagOne Pinv *
          (fromBlocks A₁₁ A₁₂ c A₂₂ : Matrix (Unit ⊕ β) (Unit ⊕ β) R) *
            hessenbergBlockDiagOne P).toBlocks₂₁ i () = 0 := by
  intro i hi
  rw [hessenbergBlockDiagOne_lowerLeftColumn]
  exact hBoundary i hi

/-- The distinguished head element has rank zero in any finite linear order. -/
theorem finiteOrderRank_headElem
    (α : Type*) [Fintype α] [LinearOrder α] [Nonempty α] :
    finiteOrderRank α (headElem (α := α)) = 0 := by
  classical
  unfold finiteOrderRank
  rw [Fintype.card_eq_zero_iff]
  refine ⟨?_⟩
  intro x
  exact (not_lt_of_ge (headElem_le (α := α) x.1) x.2).elim

/-- A positive finite-order rank cannot be the distinguished head element. -/
theorem ne_headElem_of_finiteOrderRank_pos
    (α : Type*) [Fintype α] [LinearOrder α] [Nonempty α]
    {i : α} (h : 0 < finiteOrderRank α i) :
    i ≠ headElem (α := α) := by
  intro hi
  rw [hi, finiteOrderRank_headElem α] at h
  exact Nat.lt_irrefl 0 h

/-- The lexicographic one-head block index has head rank zero. -/
theorem finiteOrderRank_sumLex_inl_unit
    (β : Type*) [Fintype β] [LinearOrder β] :
    finiteOrderRank (Unit ⊕ₗ β) (Sum.inlₗ ()) = 0 := by
  classical
  unfold finiteOrderRank
  rw [Fintype.card_eq_zero_iff]
  refine ⟨?_⟩
  intro x
  have hx := x.2
  cases h : ofLex x.1 with
  | inl u =>
      cases u
      have hx_eq : x.1 = (Sum.inlₗ () : Unit ⊕ₗ β) := by
        rw [← toLex_ofLex x.1, h]
      rw [hx_eq] at hx
      exact (lt_irrefl _ hx).elim
  | inr b =>
      have hx_eq : x.1 = (Sum.inrₗ b : Unit ⊕ₗ β) := by
        rw [← toLex_ofLex x.1, h]
      rw [hx_eq] at hx
      exact (Sum.Lex.not_inr_lt_inl hx).elim

/-- The head of a one-head lexicographic sum is the left unit element. -/
theorem headElem_sumLex_unit
    (β : Type*) [Fintype β] [LinearOrder β] :
    headElem (α := Unit ⊕ₗ β) = Sum.inlₗ () := by
  apply le_antisymm
  · exact headElem_le (α := Unit ⊕ₗ β) _
  · cases h : ofLex (headElem (α := Unit ⊕ₗ β)) with
    | inl u =>
        cases u
        rw [← toLex_ofLex (headElem (α := Unit ⊕ₗ β)), h]
    | inr b =>
        have hhead : headElem (α := Unit ⊕ₗ β) = Sum.inrₗ b := by
          rw [← toLex_ofLex (headElem (α := Unit ⊕ₗ β)), h]
        rw [hhead]
        exact Sum.Lex.inl_le_inr () b

/-- The strict lower set of the first tail index in a one-head lex block is a singleton. -/
noncomputable def lowerSetSumLexInrHeadEquivUnit
    (β : Type*) [Fintype β] [LinearOrder β] [Nonempty β] :
    {j : Unit ⊕ₗ β // j < (Sum.inrₗ (headElem (α := β)) : Unit ⊕ₗ β)} ≃
      Unit where
  toFun _ := ()
  invFun _ := ⟨Sum.inlₗ (), Sum.Lex.inl_lt_inr () (headElem (α := β))⟩
  left_inv := by
    intro x
    apply Subtype.ext
    have hx := x.2
    cases h : ofLex x.1 with
    | inl u =>
        cases u
        rw [← toLex_ofLex x.1, h]
    | inr b =>
        have hx_eq : x.1 = (Sum.inrₗ b : Unit ⊕ₗ β) := by
          rw [← toLex_ofLex x.1, h]
        rw [hx_eq] at hx
        have hb : b < headElem (α := β) := Sum.Lex.inr_lt_inr_iff.mp hx
        exact (not_lt_of_ge (headElem_le (α := β) b) hb).elim
  right_inv := by
    intro u
    cases u
    rfl

/-- The first tail index in a one-head lexicographic block has rank one. -/
theorem finiteOrderRank_sumLex_inr_head
    (β : Type*) [Fintype β] [LinearOrder β] [Nonempty β] :
    finiteOrderRank (Unit ⊕ₗ β) (Sum.inrₗ (headElem (α := β))) = 1 := by
  classical
  unfold finiteOrderRank
  rw [Fintype.card_congr (lowerSetSumLexInrHeadEquivUnit β)]
  simp

/-- Lower set of a tail element in a one-head lex block splits into head plus tail lower set. -/
theorem sumLex_lt_inr_iff
    (β : Type*) [Fintype β] [LinearOrder β] (i : β) :
    ∀ j : Unit ⊕ₗ β,
      j < (Sum.inrₗ i : Unit ⊕ₗ β) ↔
        j = Sum.inlₗ () ∨ ∃ b : β, b < i ∧ j = Sum.inrₗ b := by
  intro j
  constructor
  · intro hj
    cases h : ofLex j with
    | inl u =>
        cases u
        left
        rw [← toLex_ofLex j, h]
    | inr b =>
        right
        refine ⟨b, ?_, ?_⟩
        · have hj_eq : j = (Sum.inrₗ b : Unit ⊕ₗ β) := by
            rw [← toLex_ofLex j, h]
          have hj' : (Sum.inrₗ b : Unit ⊕ₗ β) < (Sum.inrₗ i : Unit ⊕ₗ β) := by
            simpa [hj_eq] using hj
          exact Sum.Lex.inr_lt_inr_iff.mp hj'
        · rw [← toLex_ofLex j, h]
  · intro hcase
    rcases hcase with hhead | ⟨b, hb, htail⟩
    · rw [hhead]
      exact Sum.Lex.inl_lt_inr () i
    · rw [htail]
      exact Sum.Lex.inr_lt_inr_iff.mpr hb

/-- The tail part of a one-head lex lower set is equivalent to the tail lower set. -/
noncomputable def sumLexTailLowerSetEquiv
    (β : Type*) [Fintype β] [LinearOrder β] (i : β) :
    {j : Unit ⊕ₗ β // ∃ b : β, b < i ∧ j = Sum.inrₗ b} ≃
      {b : β // b < i} where
  toFun x := ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  invFun b := ⟨Sum.inrₗ b.1, ⟨b.1, b.2, rfl⟩⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact (Classical.choose_spec x.2).2.symm
  right_inv := by
    intro b
    apply Subtype.ext
    have hspec := Classical.choose_spec
      (show ∃ b' : β, b' < i ∧ (Sum.inrₗ b.1 : Unit ⊕ₗ β) = Sum.inrₗ b' from
        ⟨b.1, b.2, rfl⟩)
    exact Sum.inr.inj (congrArg ofLex hspec.2.symm)

/-- The head singleton and tail lower-set parts of a one-head lex lower set are disjoint. -/
theorem sumLexHeadTailLowerSet_disjoint
    (β : Type*) [Fintype β] [LinearOrder β] (i : β) :
    Disjoint
      (fun j : Unit ⊕ₗ β => j = Sum.inlₗ ())
      (fun j : Unit ⊕ₗ β => ∃ b : β, b < i ∧ j = Sum.inrₗ b) := by
  rw [disjoint_iff]
  funext j
  apply propext
  constructor
  · intro h
    rcases h with ⟨hhead, htail⟩
    rcases htail with ⟨b, _hb, htail_eq⟩
    subst hhead
    have hraw := congrArg ofLex htail_eq
    cases hraw
  · intro hfalse
    exact False.elim hfalse

/-- Tail ranks in a one-head lex block are exactly shifted by the head. -/
theorem finiteOrderRank_sumLex_inr
    (β : Type*) [Fintype β] [LinearOrder β] (i : β) :
    finiteOrderRank (Unit ⊕ₗ β) (Sum.inrₗ i) =
      finiteOrderRank β i + 1 := by
  classical
  unfold finiteOrderRank
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (sumLex_lt_inr_iff β i))]
  rw [Fintype.card_subtype_or_disjoint]
  · rw [Fintype.card_subtype_eq]
    rw [Fintype.card_congr (sumLexTailLowerSetEquiv β i)]
    omega
  · exact sumLexHeadTailLowerSet_disjoint β i

/--
If a lower-left block entry of a one-head lexicographic block matrix is forced
by the Hessenberg rank condition, the row is not the tail head.
-/
theorem tail_ne_head_of_sumLex_lowerLeft_hessenberg_rank
    (β : Type*) [Fintype β] [LinearOrder β] [Nonempty β]
    {i : β}
    (h :
      finiteOrderRank (Unit ⊕ₗ β) (Sum.inlₗ ()) + 1 <
        finiteOrderRank (Unit ⊕ₗ β) (Sum.inrₗ i)) :
    i ≠ headElem (α := β) := by
  intro hi
  subst hi
  rw [finiteOrderRank_sumLex_inl_unit, finiteOrderRank_sumLex_inr_head] at h
  have hbad : 1 < 1 := by
    simpa using h
  exact (Nat.lt_irrefl 1 hbad).elim

/--
The lower-left block of a ready one-head block matrix satisfies every
Hessenberg zero condition whose column is the head block.
-/
theorem isUpperHessenberg_fromBlocks_lowerLeft
    {β R : Type*} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [Zero R]
    (A₁₁ : Matrix Unit Unit R) (A₁₂ : Matrix Unit β R)
    (c : Matrix β Unit R) (A₂₂ : Matrix β β R)
    (hc : ∀ i : β, i ≠ headElem (α := β) → c i () = 0) :
    ∀ i : β,
      finiteOrderRank (Unit ⊕ₗ β) (Sum.inlₗ ()) + 1 <
        finiteOrderRank (Unit ⊕ₗ β) (Sum.inrₗ i) →
      (fromBlocks A₁₁ A₁₂ c A₂₂ : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R)
        (Sum.inrₗ i) (Sum.inlₗ ()) = 0 := by
  intro i hrank
  exact hc i (tail_ne_head_of_sumLex_lowerLeft_hessenberg_rank β hrank)

/-- Tail-tail Hessenberg rank conditions in the block order descend to the tail order. -/
theorem sumLex_tail_tail_hessenberg_rank
    (β : Type*) [Fintype β] [LinearOrder β] {i j : β}
    (h :
      finiteOrderRank (Unit ⊕ₗ β) (Sum.inrₗ j) + 1 <
        finiteOrderRank (Unit ⊕ₗ β) (Sum.inrₗ i)) :
    finiteOrderRank β j + 1 < finiteOrderRank β i := by
  rw [finiteOrderRank_sumLex_inr, finiteOrderRank_sumLex_inr] at h
  omega

/--
The tail-tail block of a one-head block matrix inherits all Hessenberg zero
conditions from a Hessenberg tail block.
-/
theorem isUpperHessenberg_fromBlocks_tailTail
    {β R : Type*} [Fintype β] [DecidableEq β] [LinearOrder β] [Zero R]
    (A₁₁ : Matrix Unit Unit R) (A₁₂ : Matrix Unit β R)
    (c : Matrix β Unit R) (H : Matrix β β R)
    (hH : IsUpperHessenberg H) :
    ∀ i j : β,
      finiteOrderRank (Unit ⊕ₗ β) (Sum.inrₗ j) + 1 <
        finiteOrderRank (Unit ⊕ₗ β) (Sum.inrₗ i) →
      (fromBlocks A₁₁ A₁₂ c H : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R)
        (Sum.inrₗ i) (Sum.inrₗ j) = 0 := by
  intro i j hrank
  exact hH i j (sumLex_tail_tail_hessenberg_rank β hrank)

/--
A one-head block matrix is upper Hessenberg when its tail block is upper
Hessenberg and its lower-left column is zero below the tail head.
-/
theorem isUpperHessenberg_fromBlocks_ready
    {β R : Type*} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [Zero R]
    (A₁₁ : Matrix Unit Unit R) (A₁₂ : Matrix Unit β R)
    (c : Matrix β Unit R) (H : Matrix β β R)
    (hc : ∀ i : β, i ≠ headElem (α := β) → c i () = 0)
    (hH : IsUpperHessenberg H) :
    IsUpperHessenberg (ι := Unit ⊕ₗ β)
      (fromBlocks A₁₁ A₁₂ c H : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
  intro i j hij
  cases hi : ofLex i with
  | inl iu =>
      cases iu
      have i_eq : i = (Sum.inlₗ () : Unit ⊕ₗ β) := by
        rw [← toLex_ofLex i, hi]
      subst i
      rw [finiteOrderRank_sumLex_inl_unit] at hij
      exact (Nat.not_lt_zero _ hij).elim
  | inr ii =>
      have i_eq : i = (Sum.inrₗ ii : Unit ⊕ₗ β) := by
        rw [← toLex_ofLex i, hi]
      subst i
      cases hj : ofLex j with
      | inl ju =>
          cases ju
          have j_eq : j = (Sum.inlₗ () : Unit ⊕ₗ β) := by
            rw [← toLex_ofLex j, hj]
          subst j
          exact isUpperHessenberg_fromBlocks_lowerLeft A₁₁ A₁₂ c H hc ii hij
      | inr jj =>
          have j_eq : j = (Sum.inrₗ jj : Unit ⊕ₗ β) := by
            rw [← toLex_ofLex j, hj]
          subst j
          exact isUpperHessenberg_fromBlocks_tailTail A₁₁ A₁₂ c H hH ii jj hij

/-- Strictly monotone equivalences preserve lower-set ranks. -/
noncomputable def lowerSetEquivOfStrictMonoEquiv
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : α ≃ β) (h_mono : StrictMono e) (i : α) :
    {j : β // j < e i} ≃ {a : α // a < i} where
  toFun x := ⟨e.symm x.1, by
    have hx : e (e.symm x.1) < e i := by
      simpa using x.2
    exact (h_mono.lt_iff_lt).1 hx⟩
  invFun x := ⟨e x.1, h_mono x.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    simp
  right_inv := by
    intro x
    apply Subtype.ext
    simp

/-- Finite order rank is preserved by a strictly monotone equivalence. -/
theorem finiteOrderRank_equiv
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (e : α ≃ β) (h_mono : StrictMono e) (i : α) :
    finiteOrderRank β (e i) = finiteOrderRank α i := by
  unfold finiteOrderRank
  exact Fintype.card_congr (lowerSetEquivOfStrictMonoEquiv e h_mono i)

/-- Pull back finite order rank along a strictly monotone equivalence. -/
theorem finiteOrderRank_equiv_symm
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (e : α ≃ β) (h_mono : StrictMono e) (i : β) :
    finiteOrderRank α (e.symm i) = finiteOrderRank β i := by
  have h := finiteOrderRank_equiv e h_mono (e.symm i)
  simpa using h.symm

/-- Upper Hessenberg shape is invariant under strictly monotone reindexing. -/
theorem isUpperHessenberg_reindex_strictMono
    {α β R : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    [Zero R] (e : α ≃ β) (h_mono : StrictMono e) (A : Matrix α α R) :
    IsUpperHessenberg (Matrix.reindex e e A) ↔ IsUpperHessenberg A := by
  constructor
  · intro h i j hij
    have hij' : finiteOrderRank β (e j) + 1 < finiteOrderRank β (e i) := by
      rw [finiteOrderRank_equiv e h_mono j, finiteOrderRank_equiv e h_mono i]
      exact hij
    simpa [Matrix.reindex_apply] using h (e i) (e j) hij'
  · intro h i j hij
    have hij' :
        finiteOrderRank α (e.symm j) + 1 < finiteOrderRank α (e.symm i) := by
      rw [finiteOrderRank_equiv_symm e h_mono j,
        finiteOrderRank_equiv_symm e h_mono i]
      exact hij
    simpa [Matrix.reindex_apply] using h (e.symm i) (e.symm j) hij'

/-- A strictly monotone equivalence sends the distinguished head to the distinguished head. -/
theorem headElem_map_strictMono
    {α β : Type*} [Fintype α] [LinearOrder α] [Nonempty α]
    [Fintype β] [LinearOrder β] [Nonempty β]
    (e : α ≃ β) (h_mono : StrictMono e) :
    e (headElem (α := α)) = headElem (α := β) := by
  apply le_antisymm
  · by_contra hnot
    have hlt : headElem (α := β) < e (headElem (α := α)) := lt_of_not_ge hnot
    have hpre : e.symm (headElem (α := β)) < headElem (α := α) := by
      have hlt_image : e (e.symm (headElem (α := β))) < e (headElem (α := α)) := by
        simpa using hlt
      exact (h_mono.lt_iff_lt).1 hlt_image
    exact (not_lt_of_ge (headElem_le (α := α) _) hpre).elim
  · exact headElem_le (α := β) _

/-- Column multiplication commutes with simultaneous row reindexing. -/
theorem reindex_mul_column
    {α β R : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Semiring R]
    (e : α ≃ β) (Pinv : Matrix β β R) (c : Matrix α Unit R) :
    Matrix.reindex e.symm (Equiv.refl Unit)
        (Pinv * Matrix.reindex e (Equiv.refl Unit) c) =
      Matrix.reindex e.symm e.symm Pinv * c := by
  have h := Matrix.submatrix_mul_equiv
    (M := Pinv) (N := Matrix.reindex e (Equiv.refl Unit) c)
    (e₁ := e) (e₂ := e) (e₃ := id)
  ext i j
  have hentry := congrFun (congrFun h i) j
  simpa [Matrix.reindex_apply] using hentry.symm

/-- Boundary Hessenberg witnesses transport backward across strictly monotone reindexing. -/
theorem hasHessenbergBoundary_reindex_strictMono
    {α β R : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β] [Semiring R]
    (e : α ≃ β) (h_mono : StrictMono e)
    (A : Matrix α α R) (c : Matrix α Unit R)
    (hB : HasHessenbergBoundary
      (Matrix.reindex e e A) (Matrix.reindex e (Equiv.refl Unit) c)) :
    HasHessenbergBoundary A c := by
  rcases hB with ⟨P, Pinv, H, hInv, hH, hEq, hBoundary⟩
  let P0 : Matrix α α R := Matrix.reindex e.symm e.symm P
  let Pinv0 : Matrix α α R := Matrix.reindex e.symm e.symm Pinv
  let H0 : Matrix α α R := Matrix.reindex e.symm e.symm H
  refine ⟨P0, Pinv0, H0, ?_, ?_, ?_, ?_⟩
  · exact hasMatrixInverse_reindex e.symm hInv
  · exact
      (isUpperHessenberg_reindex_strictMono
        (e := e.symm)
        (h_mono := by
          intro x y hxy
          have hxy' : e (e.symm x) < e (e.symm y) := by
            simpa using hxy
          exact (h_mono.lt_iff_lt).1 hxy')
        (A := H)).2 hH
  · have hback := congrArg (Matrix.reindex e.symm e.symm) hEq
    simpa [P0, Pinv0, H0, Matrix.submatrix_mul_equiv, Matrix.mul_assoc] using hback
  · intro i hi
    have hb : (Pinv * Matrix.reindex e (Equiv.refl Unit) c) (e i) () = 0 := by
      apply hBoundary
      intro heq
      apply hi
      have hhead := headElem_map_strictMono e h_mono
      exact e.injective (by simpa [hhead] using heq)
    have hmul := reindex_mul_column e Pinv c
    have hb_re := congrFun (congrFun hmul i) ()
    rw [← hb_re]
    exact hb

/-- Block-diagonal tail extension realizes the expected parent block similarity. -/
theorem hessenbergBlockDiagOne_parentBlock_eq
    {β R : Type*} [Fintype β] [DecidableEq β] [Semiring R]
    (A₁₁ : Matrix Unit Unit R) (A₁₂ : Matrix Unit β R)
    (A₂₁ : Matrix β Unit R) (A₂₂ H : Matrix β β R)
    (P Pinv : Matrix β β R)
    (hInv : HasMatrixInverse P Pinv)
    (hA₂₂ : A₂₂ = P * H * Pinv) :
    let Pblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R := hessenbergBlockDiagOne P
    let Pinvblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R := hessenbergBlockDiagOne Pinv
    let Hblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R :=
      fromBlocks A₁₁ (A₁₂ * P) (Pinv * A₂₁) H
    fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ = Pblk * Hblk * Pinvblk := by
  intro Pblk Pinvblk Hblk
  have h₂₁ : P * (Pinv * A₂₁) = A₂₁ := by
    calc
      P * (Pinv * A₂₁) = (P * Pinv) * A₂₁ := by
        simp [Matrix.mul_assoc]
      _ = A₂₁ := by
        simp [hInv.2]
  subst hA₂₂
  ext i j <;> cases i <;> cases j <;>
    simp [Pblk, Pinvblk, Hblk, hessenbergBlockDiagOne, Matrix.fromBlocks_multiply,
      Matrix.mul_assoc, hInv.2, h₂₁]

/-- A block-diagonal tail inverse preserves a boundary column whose tail is zero. -/
theorem hessenbergBlockDiagOne_mul_readyColumn_tail
    {β R : Type*} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [Semiring R]
    (Pinv : Matrix β β R) (c : Matrix (Unit ⊕ₗ β) Unit R)
    (hc : ∀ i : β, c (Sum.inrₗ i) () = 0) :
    ∀ i : β,
      let Pinvblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R :=
        fromBlocks (1 : Matrix Unit Unit R) 0 0 Pinv
      (Pinvblk * c) (Sum.inrₗ i) () = 0 := by
  intro i
  dsimp
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro x _hx
  cases h : ofLex x with
  | inl u =>
      cases u
      have xeq : x = (Sum.inlₗ () : Unit ⊕ₗ β) := by
        rw [← toLex_ofLex x, h]
      rw [xeq]
      change (0 : R) * c (Sum.inlₗ ()) () = 0
      simp
  | inr j =>
      have xeq : x = (Sum.inrₗ j : Unit ⊕ₗ β) := by
        rw [← toLex_ofLex x, h]
      rw [xeq, hc j]
      simp

/--
Concrete block lift for the boundary target in one-head lexicographic block
form. The tail boundary witness protects the parent lower-left column.
-/
theorem hasHessenbergBoundary_fromBlocks_of_tail
    {β R : Type*} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [Semiring R]
    (A₁₁ : Matrix Unit Unit R) (A₁₂ : Matrix Unit β R)
    (A₂₁ : Matrix β Unit R) (A₂₂ : Matrix β β R)
    (c : Matrix (Unit ⊕ₗ β) Unit R)
    (hc : ∀ i : β, c (Sum.inrₗ i) () = 0)
    (hTail : HasHessenbergBoundary A₂₂ A₂₁) :
    HasHessenbergBoundary (ι := Unit ⊕ₗ β)
      (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R)
      c := by
  rcases hTail with ⟨Ptail, Pinvtail, Htail, hInvTail, hHTail, hEqTail, hBoundaryTail⟩
  let Pblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R := hessenbergBlockDiagOne Ptail
  let Pinvblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R := hessenbergBlockDiagOne Pinvtail
  let Hblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R :=
    fromBlocks A₁₁ (A₁₂ * Ptail) (Pinvtail * A₂₁) Htail
  refine ⟨Pblk, Pinvblk, Hblk, ?_, ?_, ?_, ?_⟩
  · exact hasMatrixInverse_blockDiagOne hInvTail
  · exact
      isUpperHessenberg_fromBlocks_ready
        A₁₁ (A₁₂ * Ptail) (Pinvtail * A₂₁) Htail hBoundaryTail hHTail
  · exact
      hessenbergBlockDiagOne_parentBlock_eq
        A₁₁ A₁₂ A₂₁ A₂₂ Htail Ptail Pinvtail hInvTail hEqTail
  · intro i hi
    cases h : ofLex i with
    | inl u =>
        cases u
        have hi_eq : i = (Sum.inlₗ () : Unit ⊕ₗ β) := by
          rw [← toLex_ofLex i, h]
        exact False.elim (hi (by simpa [headElem_sumLex_unit] using hi_eq))
    | inr j =>
        have hi_eq : i = (Sum.inrₗ j : Unit ⊕ₗ β) := by
          rw [← toLex_ofLex i, h]
        subst i
        simpa [Pinvblk, hessenbergBlockDiagOne] using
          hessenbergBlockDiagOne_mul_readyColumn_tail Pinvtail c hc j

/-- Concrete lift from a ready boundary object and its recursive tail boundary witness. -/
theorem hessenbergBoundary_lift_from_ready
    {R : Type v} [Semiring R]
    (x_sub : PosHessenbergBoundaryUniverse.{u} R)
    (hReady : HessenbergBoundaryReady (x_sub : HessenbergBoundaryUniverse.{u} R))
    (hTail : HessenbergBoundary_P (hessenbergBoundarySliceSub x_sub)) :
    HessenbergBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} R) := by
  intro hxNonempty
  letI : Nonempty x_sub.1.ι := hxNonempty
  let β := HessenbergTailIdx x_sub.1.ι
  let Aplain : Matrix (Unit ⊕ β) (Unit ⊕ β) R :=
    hessenbergBoundaryHeadTailMatrix x_sub.1.ι x_sub.1.A
  let cblk : Matrix (Unit ⊕ₗ β) Unit R :=
    Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι)) (Equiv.refl Unit) x_sub.1.c
  by_cases hβ : Nonempty β
  · letI : Nonempty β := hβ
    have hTailBoundary : HasHessenbergBoundary Aplain.toBlocks₂₂ Aplain.toBlocks₂₁ := by
      have hP := hTail hβ
      simpa [hessenbergBoundarySliceSub, hessenbergTailSlice_eq_boundaryLowerRightBlock,
        hessenbergBoundaryLowerLeftColumn, Aplain] using hP
    have hcblk : ∀ i : β, cblk (Sum.inrₗ i) () = 0 := by
      intro i
      simpa [cblk, headTailLexEquiv_symm_apply_inr] using
        hReady hxNonempty i i.2
    have hBlock : HasHessenbergBoundary (ι := Unit ⊕ₗ β)
        (fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ :
          Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R)
        cblk :=
      hasHessenbergBoundary_fromBlocks_of_tail Aplain.toBlocks₁₁ Aplain.toBlocks₁₂
        Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ cblk hcblk hTailBoundary
    have hLexEq :
        Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι))
          (headTailLexEquiv (α := x_sub.1.ι)) x_sub.1.A =
        (fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ :
          Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
      simpa [Aplain, β] using hessenbergBoundaryHeadTailLex_fromBlocks x_sub.1.ι x_sub.1.A
    have hLex : HasHessenbergBoundary
        (Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι))
          (headTailLexEquiv (α := x_sub.1.ι)) x_sub.1.A)
        cblk := by
      rw [hLexEq]
      exact hBlock
    exact
      hasHessenbergBoundary_reindex_strictMono
        (headTailLexEquiv (α := x_sub.1.ι))
        (headTailLexEquiv_strictMono (α := x_sub.1.ι))
        x_sub.1.A x_sub.1.c hLex
  · have hsub : Subsingleton x_sub.1.ι := by
      refine ⟨?_⟩
      intro a b
      by_cases ha : a = headElem (α := x_sub.1.ι)
      · by_cases hb : b = headElem (α := x_sub.1.ι)
        · rw [ha, hb]
        · have : Nonempty β := ⟨⟨b, hb⟩⟩
          exact False.elim (hβ this)
      · have : Nonempty β := ⟨⟨a, ha⟩⟩
        exact False.elim (hβ this)
    letI : Subsingleton x_sub.1.ι := hsub
    refine ⟨1, 1, x_sub.1.A, ?_, ?_, ?_, ?_⟩
    · constructor <;> simp
    · exact isUpperHessenberg_subsingleton x_sub.1.A
    · simp
    · intro i hi
      exact False.elim (hi (Subsingleton.elim _ _))

/--
Boundary target transport across a same-index boundary-aware invertible
similarity.
-/
theorem hessenbergBoundary_transport_similarity
    {R : Type*} [Semiring R]
    (x : HessenbergBoundaryUniverse.{u} R)
    (P Pinv : Matrix x.ι x.ι R)
    (hInv : HasMatrixInverse P Pinv)
    (hY : HessenbergBoundary_P (hessenbergBoundarySimilarityObject x P Pinv)) :
    HessenbergBoundary_P x := by
  intro hxNonempty
  have hY' :
      HasHessenbergBoundary (Pinv * x.A * P) (Pinv * x.c) := by
    simpa [hessenbergBoundarySimilarityObject] using hY hxNonempty
  rcases hY' with ⟨S, Sinv, H, hSInv, hH, hEqY, hBoundaryY⟩
  refine ⟨P * S, Sinv * Pinv, H, ?_, hH, ?_, ?_⟩
  · constructor
    · calc
        (Sinv * Pinv) * (P * S) =
            Sinv * (Pinv * P) * S := by
              simp [Matrix.mul_assoc]
        _ = Sinv * S := by
              rw [hInv.1]
              simp
        _ = 1 := hSInv.1
    · calc
        (P * S) * (Sinv * Pinv) =
            P * (S * Sinv) * Pinv := by
              simp [Matrix.mul_assoc]
        _ = P * Pinv := by
              rw [hSInv.2]
              simp
        _ = 1 := hInv.2
  · have hA_back : x.A = P * (Pinv * x.A * P) * Pinv := by
      calc
        x.A = (P * Pinv) * x.A * (P * Pinv) := by
          simp [hInv.2]
        _ = P * (Pinv * x.A * P) * Pinv := by
          simp [Matrix.mul_assoc]
    calc
      x.A = P * (Pinv * x.A * P) * Pinv := hA_back
      _ = P * (S * H * Sinv) * Pinv := by
        rw [hEqY]
      _ = (P * S) * H * (Sinv * Pinv) := by
        simp [Matrix.mul_assoc]
  · intro i hi
    have hboundary := hBoundaryY i hi
    simpa [Matrix.mul_assoc] using hboundary

/-- Boundary-driver proof-side data. -/
structure HessenbergBoundaryProofData (R : Type*) [Semiring R] where
  r_sub :
    PosHessenbergBoundaryUniverse R → PosHessenbergBoundaryUniverse R → Prop
  IsSliceable_sub : PosHessenbergBoundaryUniverse R → Prop
  slice_sub :
    ∀ x_sub : PosHessenbergBoundaryUniverse R,
      IsSliceable_sub x_sub → HessenbergBoundaryUniverse.{u} R
  transport_sub :
    ∀ {x_sub y_sub : PosHessenbergBoundaryUniverse R},
      r_sub y_sub x_sub →
        HessenbergBoundary_P (y_sub : HessenbergBoundaryUniverse.{u} R) →
          HessenbergBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} R)
  lift_from_slice_sub :
    ∀ (x_sub : PosHessenbergBoundaryUniverse R) (hx : IsSliceable_sub x_sub),
      HessenbergBoundary_P (slice_sub x_sub hx) →
        HessenbergBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} R)
  reach_sub :
    ∀ x_sub : PosHessenbergBoundaryUniverse R,
      hessenbergBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} R) >
        hessenbergBoundaryμBase →
        Σ' (y_sub : PosHessenbergBoundaryUniverse R),
          Σ' (hy : IsSliceable_sub y_sub),
            r_sub y_sub x_sub ∧
              hessenbergBoundaryμ (slice_sub y_sub hy) <
                hessenbergBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} R)

/--
Boundary-specific step hooks with the slice fixed to the mathematically correct
lower-right matrix plus lower-left boundary column.
-/
structure HessenbergBoundaryStepOracle (R : Type*) [Semiring R] where
  P :
    ∀ x_sub : PosHessenbergBoundaryUniverse R,
      Matrix x_sub.1.ι x_sub.1.ι R
  Pinv :
    ∀ x_sub : PosHessenbergBoundaryUniverse R,
      Matrix x_sub.1.ι x_sub.1.ι R
  inverse_P :
    ∀ x_sub : PosHessenbergBoundaryUniverse R,
      HasMatrixInverse (P x_sub) (Pinv x_sub)
  ready :
    ∀ x_sub : PosHessenbergBoundaryUniverse R,
      HessenbergBoundaryReady
        (hessenbergBoundarySimilarityObject
          (x_sub : HessenbergBoundaryUniverse.{u} R) (P x_sub) (Pinv x_sub))

noncomputable def hessenbergBoundaryStepObject
    {R : Type v} [Semiring R]
    (oracle : HessenbergBoundaryStepOracle.{u, v} R)
    (x_sub : PosHessenbergBoundaryUniverse R) :
    PosHessenbergBoundaryUniverse R :=
  ⟨hessenbergBoundarySimilarityObject
      (x_sub : HessenbergBoundaryUniverse.{u} R)
      (oracle.P x_sub) (oracle.Pinv x_sub),
    by simpa [hessenbergBoundarySimilarityObject] using x_sub.2⟩

def hessenbergBoundaryStepRel
    {R : Type v} [Semiring R]
    (oracle : HessenbergBoundaryStepOracle.{u, v} R)
    (y_sub x_sub : PosHessenbergBoundaryUniverse R) : Prop :=
  y_sub = hessenbergBoundaryStepObject oracle x_sub

noncomputable def hessenbergBoundaryProofDataOfStepOracle
    {R : Type v} [Semiring R]
    (oracle : HessenbergBoundaryStepOracle.{u, v} R) :
    HessenbergBoundaryProofData.{u, v} R where
  r_sub := hessenbergBoundaryStepRel oracle
  IsSliceable_sub := fun x_sub =>
    HessenbergBoundaryReady (x_sub : HessenbergBoundaryUniverse.{u} R)
  slice_sub := fun x_sub _ => hessenbergBoundarySliceSub x_sub
  transport_sub := by
    intro x_sub y_sub hrel hP
    subst hrel
    exact
      hessenbergBoundary_transport_similarity
        (x_sub : HessenbergBoundaryUniverse.{u} R)
        (oracle.P x_sub) (oracle.Pinv x_sub)
        (oracle.inverse_P x_sub) hP
  lift_from_slice_sub := by
    intro x_sub hx hP
    exact hessenbergBoundary_lift_from_ready x_sub hx hP
  reach_sub := by
    intro x_sub hgt
    let y_sub := hessenbergBoundaryStepObject oracle x_sub
    have hslice : HessenbergBoundaryReady (y_sub : HessenbergBoundaryUniverse.{u} R) := by
      simpa [y_sub, hessenbergBoundaryStepObject] using oracle.ready x_sub
    have hmono :
        hessenbergBoundaryμ (y_sub : HessenbergBoundaryUniverse.{u} R) ≤
          hessenbergBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} R) := by
      simp [y_sub, hessenbergBoundaryStepObject, hessenbergBoundarySimilarityObject,
        hessenbergBoundaryμ]
    exact
      ⟨y_sub, hslice, rfl,
        lt_of_lt_of_le (hessenbergBoundarySliceProgress y_sub) hmono⟩

/-- Base skeleton: at boundary base measure the index type is empty. -/
theorem hessenbergBoundaryBaseDimEqZero
    {R : Type*} (x : HessenbergBoundaryUniverse.{u} R)
    (hx :
      (∀ x_sub : PosHessenbergBoundaryUniverse R,
          (x_sub : HessenbergBoundaryUniverse R) ≠ x) ∨
        hessenbergBoundaryμ x ≤ hessenbergBoundaryμBase) :
    Fintype.card x.ι = 0 := by
  cases hx with
  | inl hnot =>
      by_contra hn0
      have hnpos : Fintype.card x.ι > 0 := Nat.pos_of_ne_zero hn0
      let x_sub : PosHessenbergBoundaryUniverse R := ⟨x, hnpos⟩
      exact hnot x_sub rfl
  | inr hle =>
      exact Nat.eq_zero_of_le_zero hle

/-- Boundary base case for the target predicate. -/
theorem hessenbergBoundary_base_univ {R : Type*} [Semiring R]
    (x : HessenbergBoundaryUniverse.{u} R) :
    ((∀ x_sub : PosHessenbergBoundaryUniverse R,
        (x_sub : HessenbergBoundaryUniverse R) ≠ x) ∨
      hessenbergBoundaryμ x ≤ hessenbergBoundaryμBase) →
      HessenbergBoundary_P x := by
  intro hx hne
  have hzero : Fintype.card x.ι = 0 :=
    hessenbergBoundaryBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  exact False.elim (IsEmpty.false (Classical.choice hne))

/-- Assemble a boundary-column subtype induction instance. -/
noncomputable def hessenbergBoundary_framework_inst
    {R : Type v} [Semiring R]
    (proofData : HessenbergBoundaryProofData.{u, v} R) :
    SubtypeInductionInstance
      (HessenbergBoundaryUniverse.{u} R)
      (PosHessenbergBoundaryUniverse R)
      (fun x => (x : HessenbergBoundaryUniverse.{u} R)) where
  μ := hessenbergBoundaryμ
  μ_base := hessenbergBoundaryμBase
  P := HessenbergBoundary_P
  P_sub := fun x_sub => HessenbergBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} R)
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
  base_univ := hessenbergBoundary_base_univ

/--
Boundary-column framework theorem.

This theorem is conditional on `HessenbergBoundaryProofData`, but it is routed
through the generic subtype-induction driver over the correct Hessenberg
boundary universe.
-/
theorem exists_hessenbergBoundary_framework
    {R : Type v} [Semiring R]
    (proofData : HessenbergBoundaryProofData.{u, v} R)
    (x : HessenbergBoundaryUniverse.{u} R) :
    HessenbergBoundary_P x := by
  let inst :
      SubtypeInductionInstance
        (HessenbergBoundaryUniverse.{u} R)
        (PosHessenbergBoundaryUniverse R)
        (fun x => (x : HessenbergBoundaryUniverse.{u} R)) :=
    hessenbergBoundary_framework_inst proofData
  exact
    (SubtypeInductionInstance.prove inst) x

/-- Forget the protected boundary-column condition from a boundary witness. -/
theorem hasHessenberg_of_hasHessenbergBoundary
    {R ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Semiring R] {A : Matrix ι ι R} {c : Matrix ι Unit R} :
    HasHessenbergBoundary A c → HasHessenberg A := by
  intro h
  rcases h with ⟨P, Pinv, H, hInv, hHess, hEq, _hBoundary⟩
  exact ⟨P, Pinv, H, hInv, hHess, hEq⟩

/--
Ordinary Hessenberg reduction obtained through the boundary-column descent
driver. The remaining hypothesis is the boundary-specific step oracle, whose
hooks are exactly the concrete transport/lift/reach obligations left by the
descent plan.
-/
theorem exists_hessenberg_reduction_boundary_framework
    {R : Type v} [Semiring R]
    (oracle : HessenbergBoundaryStepOracle.{u, v} R)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) :
    HasHessenberg A := by
  by_cases hne : Nonempty ι
  · let x : HessenbergBoundaryUniverse.{u} R :=
      { ι := ι
        A := A
        c := 0 }
    have hP : HessenbergBoundary_P x :=
      exists_hessenbergBoundary_framework
        (hessenbergBoundaryProofDataOfStepOracle oracle) x
    have hBoundary : HasHessenbergBoundary A (0 : Matrix ι Unit R) := by
      simpa [x] using hP hne
    exact hasHessenberg_of_hasHessenbergBoundary hBoundary
  · letI : IsEmpty ι := not_nonempty_iff.mp hne
    letI : Subsingleton ι := by infer_instance
    exact base_hessenberg_subsingleton A

end MatDecompFormal.Instances
