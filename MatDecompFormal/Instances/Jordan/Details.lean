import MatDecompFormal.Framework.UniverseDecompositionSquareSubtype
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Schur.Direct

universe u v w

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Jordan Form Details

This file contains the matrix-level target predicate for Jordan form.  The
descent driver and the one-step oracle are defined in later files.
-/

variable {K : Type v} {ι : Type u}

/-- Standard finite Jordan block with eigenvalue `lam` and size `n`. -/
def jordanBlock [Zero K] [One K] (lam : K) (n : Nat) :
    Matrix (Fin n) (Fin n) K :=
  fun i j =>
    if i = j then lam
    else if (i : Nat) + 1 = (j : Nat) then 1
    else 0

/--
Data witnessing that a matrix is a block diagonal matrix of Jordan blocks.

The predicate is intentionally data-bearing: it records the block family,
eigenvalues, block sizes, an ambient index equivalence, and the block-matrix
equation after reindexing.
-/
structure JordanMatrixData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (J : Matrix ι ι K) where
  block : Type u
  [fintype_block : Fintype block]
  [decEq_block : DecidableEq block]
  eigenvalue : block → K
  blockSize : block → Nat
  blockSize_pos : ∀ b, 0 < blockSize b
  total_size : (∑ b, blockSize b) = Fintype.card ι
  blockIndexEquiv : ι ≃ (b : block) × Fin (blockSize b)
  block_form :
    Matrix.reindex blockIndexEquiv blockIndexEquiv J =
      Matrix.blockDiagonal' fun b => jordanBlock (eigenvalue b) (blockSize b)

attribute [instance] JordanMatrixData.fintype_block
attribute [instance] JordanMatrixData.decEq_block

/-- Matrix-level Jordan predicate. -/
def IsJordanMatrix
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (J : Matrix ι ι K) : Prop :=
  Nonempty (JordanMatrixData J)

/-- Jordan similarity target for a concrete finite square matrix. -/
def HasJordanMatrix
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ P : Matrix ι ι K, ∃ J : Matrix ι ι K,
    InvertibleMatrix P ∧ IsJordanMatrix J ∧ A = P * J * P⁻¹

/--
Explicit block-data witness for ordinary Jordan form.

This exposes the final similarity matrix and an actual `JordanMatrixData`
payload for the Jordan matrix.  It is equivalent to `HasJordanMatrix`, but the
block decomposition is no longer hidden behind the `IsJordanMatrix` wrapper.
-/
def JordanBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ P : Matrix ι ι K, ∃ J : Matrix ι ι K,
    InvertibleMatrix P ∧
    (∃ _data : JordanMatrixData J, True) ∧
    A = P * J * P⁻¹

/-- Route-tagged ordinary Jordan block data. -/
def JordanBridgeBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (tag : String) (A : Matrix ι ι K) : Prop :=
  tag = tag ∧ JordanBlockData A

abbrev JordanBlockTrace
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  JordanBlockData A

theorem hasJordanMatrix_of_jordanBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K} :
    JordanBlockData A → HasJordanMatrix A := by
  intro hA
  rcases hA with ⟨P, J, hP, hData, hEq⟩
  rcases hData with ⟨data, _⟩
  exact ⟨P, J, hP, ⟨data⟩, hEq⟩

theorem jordanBlockData_of_hasJordanMatrix
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K} :
    HasJordanMatrix A → JordanBlockData A := by
  intro hA
  rcases hA with ⟨P, J, hP, hJ, hEq⟩
  rcases hJ with ⟨data⟩
  exact ⟨P, J, hP, ⟨data, trivial⟩, hEq⟩

theorem jordanBlockData_of_jordanBridgeBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {tag : String} {A : Matrix ι ι K} :
    JordanBridgeBlockData tag A → JordanBlockData A := by
  intro hA
  exact hA.2

theorem jordanBridgeBlockData_of_jordanBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (tag : String) {A : Matrix ι ι K} :
    JordanBlockData A → JordanBridgeBlockData tag A := by
  intro hA
  exact ⟨rfl, hA⟩

theorem hasJordanMatrix_of_jordanBridgeBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {tag : String} {A : Matrix ι ι K} :
    JordanBridgeBlockData tag A → HasJordanMatrix A :=
  hasJordanMatrix_of_jordanBlockData ∘ jordanBlockData_of_jordanBridgeBlockData

/--
Universe-level predicate used by the square-subtype induction framework.

The characteristic-polynomial splitting hypothesis is kept as a theorem input,
not as a field of `SquareUniverse`, so the ordinary square matrix driver can be
used unchanged.
-/
def Jordan_P [Field K] (x : SquareUniverse K) : Prop :=
  x.A.charpoly.Splits (RingHom.id K) → HasJordanMatrix x.A

def Jordan_P_sub [Field K] (x_sub : PosSquareUniverse K) : Prop :=
  Jordan_P (x_sub : SquareUniverse K)

@[simp] theorem jordan_P_compat [Field K] (x_sub : PosSquareUniverse K) :
    Jordan_P_sub x_sub ↔ Jordan_P (x_sub : SquareUniverse K) :=
  Iff.rfl

/-- Jordan matrix data is invariant under index reindexing. -/
theorem isJordanMatrix_reindex
    [Field K]
    {κ : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    (e : ι ≃ κ) {J : Matrix ι ι K}
    (hJ : IsJordanMatrix J) :
    IsJordanMatrix (Matrix.reindex e e J) := by
  rcases hJ with ⟨d⟩
  refine ⟨{
    block := d.block
    eigenvalue := d.eigenvalue
    blockSize := d.blockSize
    blockSize_pos := d.blockSize_pos
    total_size := ?_
    blockIndexEquiv := e.symm.trans d.blockIndexEquiv
    block_form := ?_
  }⟩
  · simpa [Fintype.card_congr e] using d.total_size
  · ext x y
    simpa [Matrix.reindex_apply] using congrFun (congrFun d.block_form x) y

/--
Jordan matrix data is invariant under index reindexing, allowing the source and
target index types to live in different universes.
-/
theorem isJordanMatrix_reindex_universe
    [Field K]
    {κ : Type w} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    (e : ι ≃ κ) {J : Matrix ι ι K}
    (hJ : IsJordanMatrix J) :
    IsJordanMatrix (Matrix.reindex e e J) := by
  classical
  rcases hJ with ⟨d⟩
  let eBlock : d.block ≃ ULift.{w, 0} (Fin (Fintype.card d.block)) :=
    (Fintype.equivFin d.block).trans Equiv.ulift.symm
  let eSigma :
      ((b : d.block) × Fin (d.blockSize b)) ≃
        ((b : ULift.{w, 0} (Fin (Fintype.card d.block))) ×
          Fin (d.blockSize (eBlock.symm b))) := {
    toFun x := ⟨eBlock x.1, Equiv.cast (by simp [eBlock]) x.2⟩
    invFun x := ⟨eBlock.symm x.1, x.2⟩
    left_inv := by
      intro x
      rcases x with ⟨b, i⟩
      simp [eBlock]
    right_inv := by
      intro x
      rcases x with ⟨b, i⟩
      simp [eBlock]
  }
  refine ⟨{
    block := ULift.{w, 0} (Fin (Fintype.card d.block))
    eigenvalue := fun b => d.eigenvalue (eBlock.symm b)
    blockSize := fun b => d.blockSize (eBlock.symm b)
    blockSize_pos := fun b => d.blockSize_pos (eBlock.symm b)
    total_size := ?_
    blockIndexEquiv :=
      e.symm.trans <|
        d.blockIndexEquiv.trans eSigma
    block_form := ?_
  }⟩
  · have hsum :
        (∑ b : ULift.{w, 0} (Fin (Fintype.card d.block)),
            d.blockSize (eBlock.symm b)) =
          ∑ b : d.block, d.blockSize b := by
      exact Fintype.sum_equiv eBlock.symm
        (fun b => d.blockSize (eBlock.symm b))
        (fun b => d.blockSize b)
        (fun b => rfl)
    simpa [hsum, Fintype.card_congr e] using d.total_size
  · ext x y
    rcases x with ⟨bx, ix⟩
    rcases y with ⟨bY, iy⟩
    have hentry :=
      congrFun (congrFun d.block_form ⟨eBlock.symm bx, ix⟩) ⟨eBlock.symm bY, iy⟩
    simpa [Matrix.reindex_apply, Matrix.blockDiagonal', eBlock, eSigma] using hentry

/-- Block-diagonal matrix on the lexicographic sum index used by head-tail descent. -/
noncomputable def jordanBlockDiagLex
    [Zero K] {α : Type u} {β : Type v}
    (A : Matrix α α K) (B : Matrix β β K) :
    Matrix (α ⊕ₗ β) (α ⊕ₗ β) K :=
  Matrix.reindex (sumToLexEquiv α β) (sumToLexEquiv α β)
    (Matrix.fromBlocks A 0 0 B : Matrix (α ⊕ β) (α ⊕ β) K)

/-- Block-diagonal matrices with invertible diagonal blocks are invertible. -/
lemma invertibleMatrix_blockDiag_plain
    {K : Type v} {α : Type u} {β : Type v} [Field K]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {P₁ : Matrix α α K} {P₂ : Matrix β β K}
    (hP₁ : InvertibleMatrix P₁) (hP₂ : InvertibleMatrix P₂) :
    InvertibleMatrix
      (Matrix.fromBlocks P₁ 0 0 P₂ : Matrix (α ⊕ β) (α ⊕ β) K) := by
  haveI : Invertible P₁ := hP₁.invertible
  haveI : Invertible P₂ := hP₂.invertible
  let Q : Matrix (α ⊕ β) (α ⊕ β) K :=
    Matrix.fromBlocks P₁⁻¹ 0 0 P₂⁻¹
  have hmul :
      (Matrix.fromBlocks P₁ 0 0 P₂ : Matrix (α ⊕ β) (α ⊕ β) K) * Q = 1 := by
    simp [Q, Matrix.fromBlocks_multiply, Matrix.mul_inv_of_invertible]
  have hmul' :
      Q * (Matrix.fromBlocks P₁ 0 0 P₂ : Matrix (α ⊕ β) (α ⊕ β) K) = 1 := by
    simp [Q, Matrix.fromBlocks_multiply, Matrix.inv_mul_of_invertible]
  exact ⟨⟨_, Q, hmul, hmul'⟩, rfl⟩

/-- Lexicographic block-diagonal matrices with invertible diagonal blocks are invertible. -/
lemma invertibleMatrix_blockDiag_lex
    {K : Type v} {α : Type u} {β : Type v} [Field K]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {P₁ : Matrix α α K} {P₂ : Matrix β β K}
    (hP₁ : InvertibleMatrix P₁) (hP₂ : InvertibleMatrix P₂) :
    InvertibleMatrix (jordanBlockDiagLex P₁ P₂) := by
  exact invertibleMatrix_reindex (sumToLexEquiv α β)
    (invertibleMatrix_blockDiag_plain hP₁ hP₂)

/--
Block-diagonal Jordan matrices combine to another Jordan matrix on the
lexicographic sum index.
-/
theorem isJordanMatrix_blockDiag_lex
    [Field K]
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [LinearOrder α] [LinearOrder β]
    (J₁ : Matrix α α K) (J₂ : Matrix β β K)
    (h₁ : IsJordanMatrix J₁) (h₂ : IsJordanMatrix J₂) :
    IsJordanMatrix (jordanBlockDiagLex J₁ J₂) := by
  classical
  rcases h₁ with ⟨d₁⟩
  rcases h₂ with ⟨d₂⟩
  refine ⟨{
    block := ULift.{max u v, u} d₁.block ⊕ ULift.{max u v, v} d₂.block
    eigenvalue := fun b => match b with
      | Sum.inl b => d₁.eigenvalue b.down
      | Sum.inr b => d₂.eigenvalue b.down
    blockSize := fun b => match b with
      | Sum.inl b => d₁.blockSize b.down
      | Sum.inr b => d₂.blockSize b.down
    blockSize_pos := ?_
    total_size := ?_
    blockIndexEquiv := ?_
    block_form := ?_
  }⟩
  · intro b
    cases b with
    | inl b => exact d₁.blockSize_pos b.down
    | inr b => exact d₂.blockSize_pos b.down
  · have hsum₁ : (∑ b : ULift.{max u v, u} d₁.block, d₁.blockSize b.down) =
        ∑ b : d₁.block, d₁.blockSize b := by
      exact Fintype.sum_equiv Equiv.ulift (fun b => d₁.blockSize b.down)
        (fun b => d₁.blockSize b) (fun b => rfl)
    have hsum₂ : (∑ b : ULift.{max u v, v} d₂.block, d₂.blockSize b.down) =
        ∑ b : d₂.block, d₂.blockSize b := by
      exact Fintype.sum_equiv Equiv.ulift (fun b => d₂.blockSize b.down)
        (fun b => d₂.blockSize b) (fun b => rfl)
    simp [Fintype.card_sum, Fintype.card_lex, hsum₁, hsum₂,
      d₁.total_size, d₂.total_size]
  · exact
      (sumToLexEquiv α β).symm.trans <|
        (Equiv.sumCongr d₁.blockIndexEquiv d₂.blockIndexEquiv).trans <|
        (Equiv.sumCongr
          (Equiv.sigmaCongr Equiv.ulift.symm
            (fun b => Equiv.cast (by simp)))
          (Equiv.sigmaCongr Equiv.ulift.symm
            (fun b => Equiv.cast (by simp)))).trans <|
          (Equiv.sumSigmaDistrib
            (fun b : ULift.{max u v, u} d₁.block ⊕
                ULift.{max u v, v} d₂.block =>
              Fin <|
                match b with
                | Sum.inl b => d₁.blockSize b.down
                | Sum.inr b => d₂.blockSize b.down)).symm
  · ext x y
    rcases x with ⟨bx, ix⟩
    rcases y with ⟨bY, iy⟩
    cases bx with
    | inl bx =>
      cases bY with
      | inl bY =>
        have hentry :=
          congrFun (congrFun d₁.block_form ⟨bx.down, ix⟩) ⟨bY.down, iy⟩
        simpa [jordanBlockDiagLex, Matrix.reindex_apply,
          Matrix.blockDiagonal'] using hentry
      | inr bY =>
        simp [jordanBlockDiagLex, Matrix.reindex_apply, Matrix.blockDiagonal']
    | inr bx =>
      cases bY with
      | inl bY =>
        simp [jordanBlockDiagLex, Matrix.reindex_apply, Matrix.blockDiagonal']
      | inr bY =>
        have hentry :=
          congrFun (congrFun d₂.block_form ⟨bx.down, ix⟩) ⟨bY.down, iy⟩
        simpa [jordanBlockDiagLex, Matrix.reindex_apply,
          Matrix.blockDiagonal'] using hentry

/-- Every one-dimensional block is a Jordan matrix. -/
theorem isJordanMatrix_unit
    [Field K] (J : Matrix Unit Unit K) :
    IsJordanMatrix J := by
  refine ⟨{
    block := PUnit
    eigenvalue := fun _ => J () ()
    blockSize := fun _ => 1
    blockSize_pos := fun _ => by decide
    total_size := ?_
    blockIndexEquiv := ?_
    block_form := ?_
  }⟩
  · simp
  · exact
      { toFun := fun _ => ⟨PUnit.unit, 0⟩
        invFun := fun _ => ()
        left_inv := by
          intro x
          cases x
          rfl
        right_inv := by
          intro x
          rcases x with ⟨bx, ix⟩
          cases bx
          have hix : ix = 0 := by
            apply Fin.ext
            omega
          subst ix
          rfl }
  · ext x y
    cases x with
    | mk bx ix =>
      cases y with
      | mk bY iy =>
        cases bx
        cases bY
        have hix : ix = 0 := by
          apply Fin.ext
          omega
        have hiy : iy = 0 := by
          apply Fin.ext
          omega
        subst ix
        subst iy
        simp [jordanBlock, Matrix.reindex_apply, Matrix.blockDiagonal']

/-- A standard Jordan block is a Jordan matrix. -/
theorem isJordanMatrix_jordanBlock
    [Field K] (lam : K) (n : Nat) (hpos : 0 < n) :
    IsJordanMatrix (jordanBlock lam n) := by
  classical
  refine ⟨{
    block := PUnit
    eigenvalue := fun _ => lam
    blockSize := fun _ => n
    blockSize_pos := fun _ => hpos
    total_size := ?_
    blockIndexEquiv := (Equiv.uniqueSigma (fun _ : PUnit => Fin n)).symm
    block_form := ?_
  }⟩
  · simp
  · ext x y
    cases x with
    | mk bx ix =>
      cases y with
      | mk bY iy =>
        cases bx
        cases bY
        simp [Matrix.reindex_apply, Matrix.blockDiagonal', Equiv.uniqueSigma_apply]

/-- A standard Jordan block has a trivial Jordan similarity witness. -/
theorem hasJordanMatrix_jordanBlock
    [Field K] (lam : K) (n : Nat) (hpos : 0 < n) :
    HasJordanMatrix (jordanBlock lam n) := by
  refine ⟨1, jordanBlock lam n, invertibleMatrix_one, ?_, ?_⟩
  · exact isJordanMatrix_jordanBlock lam n hpos
  · simp

/--
A reindexed standard Jordan block is a Jordan matrix, with the block type
chosen in the target index universe.
-/
theorem isJordanMatrix_reindex_jordanBlock
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (lam : K) (n : Nat) (hpos : 0 < n) (e : ι ≃ Fin n) :
    IsJordanMatrix
      ((Matrix.reindex e.symm e.symm (jordanBlock (K := K) lam n)) :
        Matrix ι ι K) := by
  classical
  refine ⟨{
    block := PUnit
    eigenvalue := fun _ => lam
    blockSize := fun _ => n
    blockSize_pos := fun _ => hpos
    total_size := ?_
    blockIndexEquiv := e.trans (Equiv.uniqueSigma (fun _ : PUnit => Fin n)).symm
    block_form := ?_
  }⟩
  · simpa [Fintype.card_congr e]
  · ext x y
    cases x with
    | mk bx ix =>
      cases y with
      | mk bY iy =>
        cases bx
        cases bY
        simp [Matrix.reindex_apply, Matrix.blockDiagonal', Equiv.uniqueSigma_apply]

/--
A matrix reindexed from a standard Jordan block has a trivial Jordan
similarity witness on the target index type.
-/
theorem hasJordanMatrix_reindex_jordanBlock
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (lam : K) (n : Nat) (hpos : 0 < n) (e : ι ≃ Fin n) :
    HasJordanMatrix
      ((Matrix.reindex e.symm e.symm (jordanBlock (K := K) lam n)) :
        Matrix ι ι K) := by
  refine ⟨1, ((Matrix.reindex e.symm e.symm (jordanBlock (K := K) lam n)) :
      Matrix ι ι K),
    invertibleMatrix_one, ?_, ?_⟩
  · exact isJordanMatrix_reindex_jordanBlock lam n hpos e
  · simp

/--
Jordan matrix data over `Fin n` can be transported to any equivalent target
index type.  This is the universe-changing transport needed by companion-block
leaves, where the concrete model is naturally indexed by `Fin n`.
-/
theorem isJordanMatrix_reindex_fin
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {n : Nat} (e : ι ≃ Fin n) {J : Matrix (Fin n) (Fin n) K}
    (hJ : IsJordanMatrix J) :
    IsJordanMatrix
      ((Matrix.reindex e.symm e.symm J) : Matrix ι ι K) := by
  classical
  rcases hJ with ⟨d⟩
  refine ⟨{
    block := ULift.{u, 0} d.block
    eigenvalue := fun b => d.eigenvalue b.down
    blockSize := fun b => d.blockSize b.down
    blockSize_pos := fun b => d.blockSize_pos b.down
    total_size := ?_
    blockIndexEquiv :=
      e.trans <|
        d.blockIndexEquiv.trans <|
          Equiv.sigmaCongr Equiv.ulift.symm
            (fun b => Equiv.cast (by rfl))
    block_form := ?_
  }⟩
  · have hsum :
        (∑ b : ULift.{u, 0} d.block, d.blockSize b.down) =
          ∑ b : d.block, d.blockSize b := by
      exact Fintype.sum_equiv Equiv.ulift
        (fun b => d.blockSize b.down)
        (fun b => d.blockSize b)
        (fun b => rfl)
    simpa [hsum, Fintype.card_congr e] using d.total_size
  · ext x y
    rcases x with ⟨bx, ix⟩
    rcases y with ⟨bY, iy⟩
    have hentry :=
      congrFun (congrFun d.block_form ⟨bx.down, ix⟩) ⟨bY.down, iy⟩
    simpa [Matrix.reindex_apply, Matrix.blockDiagonal'] using hentry

/--
Jordan similarity witnesses over `Fin n` can be transported to any equivalent
target index type.
-/
theorem hasJordanMatrix_reindex_fin
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {n : Nat} (e : ι ≃ Fin n) {A : Matrix (Fin n) (Fin n) K}
    (hA : HasJordanMatrix A) :
    HasJordanMatrix
      ((Matrix.reindex e.symm e.symm A) : Matrix ι ι K) := by
  rcases hA with ⟨P, J, hP, hJ, hEq⟩
  refine ⟨Matrix.reindex e.symm e.symm P,
    Matrix.reindex e.symm e.symm J, ?_, ?_, ?_⟩
  · exact invertibleMatrix_reindex e.symm hP
  · exact isJordanMatrix_reindex_fin e hJ
  · have h := congrArg (Matrix.reindex e.symm e.symm) hEq
    simpa [Matrix.submatrix_mul_equiv, Matrix.inv_reindex] using h

/-- Any matrix indexed by a one-element type is a Jordan matrix. -/
theorem isJordanMatrix_of_card_eq_one
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K} (hcard : Fintype.card ι = 1) :
    IsJordanMatrix A := by
  classical
  letI : Unique ι :=
    Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp hcard)
  let e : ι ≃ (b : PUnit) × Fin 1 := {
    toFun := fun _ => ⟨PUnit.unit, 0⟩
    invFun := fun _ => default
    left_inv := by
      intro i
      exact (Unique.eq_default i).symm
    right_inv := by
      intro x
      rcases x with ⟨b, ix⟩
      cases b
      have hix : ix = 0 := by
        apply Fin.ext
        omega
      subst ix
      rfl
  }
  have hpos1 : ∀ _ : PUnit, 0 < (1 : Nat) := fun _ => by decide
  refine ⟨{
    block := PUnit
    eigenvalue := fun _ => A default default
    blockSize := fun _ => 1
    blockSize_pos := hpos1
    total_size := ?_
    blockIndexEquiv := e
    block_form := ?_
  }⟩
  · simpa [hcard]
  · ext x y
    rcases x with ⟨bx, ix⟩
    rcases y with ⟨bY, iy⟩
    cases bx
    cases bY
    have hix : ix = 0 := by
      apply Fin.ext
      omega
    have hiy : iy = 0 := by
      apply Fin.ext
      omega
    subst ix
    subst iy
    simp [e, jordanBlock, Matrix.reindex_apply, Matrix.blockDiagonal']

/-- Any matrix indexed by a one-element type has Jordan form. -/
theorem hasJordanMatrix_of_card_eq_one
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K} (hcard : Fintype.card ι = 1) :
    HasJordanMatrix A := by
  refine ⟨1, A, invertibleMatrix_one, ?_, ?_⟩
  · exact isJordanMatrix_of_card_eq_one (A := A) hcard
  · simp

/-- Empty matrices have empty Jordan block data. -/
theorem isJordanMatrix_empty
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι] [IsEmpty ι]
    (J : Matrix ι ι K) :
    IsJordanMatrix J := by
  refine ⟨{
    block := ULift.{u} Empty
    eigenvalue := fun b => Empty.elim b.down
    blockSize := fun b => Empty.elim b.down
    blockSize_pos := fun b => Empty.elim b.down
    total_size := ?_
    blockIndexEquiv := ?_
    block_form := ?_
  }⟩
  · simp
  · exact
      { toFun := fun i => False.elim (IsEmpty.false i)
        invFun := fun x => Empty.elim x.1.down
        left_inv := fun i => False.elim (IsEmpty.false i)
        right_inv := fun x => Empty.elim x.1.down }
  · ext x
    exact Empty.elim x.1.down

/-- Empty matrices have a trivial Jordan similarity witness. -/
theorem base_jordan_empty
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι] [IsEmpty ι]
    (A : Matrix ι ι K) :
    HasJordanMatrix A := by
  refine ⟨1, A, invertibleMatrix_one, ?_, ?_⟩
  · exact isJordanMatrix_empty A
  · simp

/-- A Jordan matrix is trivially similar to itself. -/
theorem hasJordanMatrix_of_isJordanMatrix
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K} (hA : IsJordanMatrix A) :
    HasJordanMatrix A := by
  refine ⟨1, A, invertibleMatrix_one, hA, ?_⟩
  simp

/-- Jordan similarity witnesses are invariant under index reindexing. -/
theorem hasJordanMatrix_reindex
    [Field K]
    {κ : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    (e : ι ≃ κ) {A : Matrix ι ι K}
    (hA : HasJordanMatrix A) :
    HasJordanMatrix (Matrix.reindex e e A) := by
  rcases hA with ⟨P, J, hP, hJ, hEq⟩
  refine ⟨Matrix.reindex e e P, Matrix.reindex e e J, ?_, ?_, ?_⟩
  · exact invertibleMatrix_reindex e hP
  · exact isJordanMatrix_reindex e hJ
  · have h := congrArg (Matrix.reindex e e) hEq
    simpa [Matrix.submatrix_mul_equiv, Matrix.inv_reindex] using h

/--
Jordan similarity witnesses are invariant under index reindexing across
universes.
-/
theorem hasJordanMatrix_reindex_universe
    [Field K]
    {κ : Type w} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    (e : ι ≃ κ) {A : Matrix ι ι K}
    (hA : HasJordanMatrix A) :
    HasJordanMatrix (Matrix.reindex e e A) := by
  rcases hA with ⟨P, J, hP, hJ, hEq⟩
  refine ⟨Matrix.reindex e e P, Matrix.reindex e e J, ?_, ?_, ?_⟩
  · exact invertibleMatrix_reindex e hP
  · exact isJordanMatrix_reindex_universe e hJ
  · have h := congrArg (Matrix.reindex e e) hEq
    simpa [Matrix.submatrix_mul_equiv, Matrix.inv_reindex] using h

/--
Block-diagonal Jordan witnesses combine over the lexicographic sum index.
-/
theorem hasJordanMatrix_blockDiag_lex
    [Field K]
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [LinearOrder α] [LinearOrder β]
    (A₁ : Matrix α α K) (A₂ : Matrix β β K)
    (h₁ : HasJordanMatrix A₁) (h₂ : HasJordanMatrix A₂) :
    HasJordanMatrix (jordanBlockDiagLex A₁ A₂) := by
  classical
  rcases h₁ with ⟨P₁, J₁, hP₁, hJ₁, hEq₁⟩
  rcases h₂ with ⟨P₂, J₂, hP₂, hJ₂, hEq₂⟩
  let P := jordanBlockDiagLex P₁ P₂
  let J := jordanBlockDiagLex J₁ J₂
  refine ⟨P, J, ?_, ?_, ?_⟩
  · exact invertibleMatrix_blockDiag_lex hP₁ hP₂
  · exact isJordanMatrix_blockDiag_lex J₁ J₂ hJ₁ hJ₂
  · haveI : Invertible P₁ := hP₁.invertible
    haveI : Invertible P₂ := hP₂.invertible
    have hP : InvertibleMatrix P := invertibleMatrix_blockDiag_lex hP₁ hP₂
    haveI : Invertible P := hP.invertible
    have hPinv :
        P⁻¹ = jordanBlockDiagLex P₁⁻¹ P₂⁻¹ := by
      apply Matrix.inv_eq_right_inv
      simp [P, jordanBlockDiagLex, Matrix.submatrix_mul_equiv,
        Matrix.fromBlocks_multiply, Matrix.mul_inv_of_invertible]
    rw [hPinv]
    simp [P, J, jordanBlockDiagLex, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, hEq₁, hEq₂, Matrix.mul_assoc]

/-- Transport a Jordan witness backward across an invertible similarity. -/
theorem jordan_transport_similarity
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {P A B : Matrix ι ι K}
    (hP : InvertibleMatrix P)
    (hB : B = P⁻¹ * A * P)
    (hJordanB : HasJordanMatrix B) :
    HasJordanMatrix A := by
  rcases hJordanB with ⟨S, J, hS, hJ, hBJ⟩
  refine ⟨P * S, J, ?_, hJ, ?_⟩
  · exact hP.mul hS
  · haveI : Invertible P := hP.invertible
    haveI : Invertible S := hS.invertible
    calc
      A = P * B * P⁻¹ := by
        rw [hB]
        simp [Matrix.mul_assoc]
      _ = P * (S * J * S⁻¹) * P⁻¹ := by
        rw [hBJ]
      _ = (P * S) * J * (P * S)⁻¹ := by
        rw [Matrix.mul_inv_rev]
        simp [Matrix.mul_assoc]

/-- Characteristic polynomial is invariant under invertible similarity. -/
theorem jordan_similarity_charpoly
    [Field K] [Fintype ι] [DecidableEq ι]
    {P A : Matrix ι ι K}
    (hP : InvertibleMatrix P) :
    (P⁻¹ * A * P).charpoly = A.charpoly := by
  have h := Matrix.charpoly_units_conj' hP.unit A
  simpa [hP.unit_spec] using h

end MatDecompFormal.Instances
