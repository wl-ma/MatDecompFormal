import MatDecompFormal.Instances.Jordan.Details
import MatDecompFormal.Instances.RationalCanonical.Details

universe u v w

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open scoped Polynomial

/-!
# Generalized Jordan Block Data

This file contains the data-bearing matrix predicate for generalized Jordan
form.  It is local matrix infrastructure only: arbitrary-matrix existence
theorems are assembled later through the descent framework.
-/

variable {K : Type v} {ι : Type u}

/-- Coordinate type for one generalized Jordan block. -/
abbrev generalizedBlockCoord {K : Type v} [Field K] (p : K[X]) (k : Nat) :=
  (Fin k) × Fin p.natDegree

noncomputable instance generalizedBlockCoord.instLinearOrder
    {K : Type v} [Field K] (p : K[X]) (k : Nat) :
    LinearOrder (generalizedBlockCoord p k) :=
  inferInstanceAs (LinearOrder ((Fin k) ×ₗ Fin p.natDegree))

/-- The generalized Jordan connector with a single `1` in the top-right entry. -/
def generalizedJordanConnector
    {K : Type v} [Zero K] [One K] (m : Nat) :
    Matrix (Fin m) (Fin m) K :=
  fun i j =>
    if (i : Nat) = 0 ∧ (j : Nat) + 1 = m then 1 else 0

/--
Generalized Jordan block for the elementary factor `p ^ k`.

The diagonal blocks are the companion matrix of `p`; the subdiagonal block
connector is `generalizedJordanConnector p.natDegree`.
-/
def generalizedJordanBlock
    {K : Type v} [Field K] (p : K[X]) (k : Nat) :
    Matrix (generalizedBlockCoord p k) (generalizedBlockCoord p k) K :=
  fun i j =>
    if i.1 = j.1 then
      companionMatrixFin p i.2 j.2
    else if (j.1 : Nat) + 1 = (i.1 : Nat) then
      generalizedJordanConnector p.natDegree i.2 j.2
    else
      0

/-- Cardinality of the natural index type of a generalized Jordan block. -/
@[simp] theorem generalizedJordanBlock_card
    {K : Type v} [Field K] (p : K[X]) (k : Nat) :
    Fintype.card ((Fin k) × Fin p.natDegree) = k * p.natDegree := by
  simp

/--
Data witnessing that a matrix is a block diagonal matrix of generalized Jordan
blocks for powers of monic irreducible polynomials.
-/
structure GeneralizedJordanBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (J : Matrix ι ι K) where
  block : Type u
  [fintype_block : Fintype block]
  [decEq_block : DecidableEq block]
  [linearOrder_block : LinearOrder block]
  poly : block → K[X]
  poly_monic : ∀ b, (poly b).Monic
  poly_irreducible : ∀ b, Irreducible (poly b)
  exponent : block → Nat
  exponent_pos : ∀ b, 0 < exponent b
  total_size :
    (∑ b, exponent b * (poly b).natDegree) = Fintype.card ι
  blockIndexEquiv :
    ι ≃ (b : block) × generalizedBlockCoord (poly b) (exponent b)
  block_form :
    Matrix.reindex blockIndexEquiv blockIndexEquiv J =
      Matrix.blockDiagonal' fun b =>
        generalizedJordanBlock (poly b) (exponent b)

attribute [instance] GeneralizedJordanBlockData.fintype_block
attribute [instance] GeneralizedJordanBlockData.decEq_block
attribute [instance] GeneralizedJordanBlockData.linearOrder_block

/-- Matrix-level generalized Jordan predicate. -/
def IsGeneralizedJordanMatrix
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (J : Matrix ι ι K) : Prop :=
  Nonempty (GeneralizedJordanBlockData J)

/-- Generalized Jordan similarity target for a concrete finite square matrix. -/
def HasGeneralizedJordanMatrix
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ P : Matrix ι ι K, ∃ J : Matrix ι ι K,
    InvertibleMatrix P ∧ IsGeneralizedJordanMatrix J ∧ A = P * J * P⁻¹

/--
Explicit block-data witness for generalized Jordan form.

This exposes the final similarity matrix and actual
`GeneralizedJordanBlockData` payload for the generalized Jordan matrix.
-/
def GeneralizedJordanBlockWitnessData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ P : Matrix ι ι K, ∃ J : Matrix ι ι K,
    InvertibleMatrix P ∧
    (∃ _data : GeneralizedJordanBlockData J, True) ∧
    A = P * J * P⁻¹

/-- Route-tagged generalized Jordan block data. -/
def GeneralizedJordanBridgeBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (tag : String) (A : Matrix ι ι K) : Prop :=
  tag = tag ∧ GeneralizedJordanBlockWitnessData A

abbrev GeneralizedJordanBlockTrace
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  GeneralizedJordanBlockWitnessData A

theorem hasGeneralizedJordanMatrix_of_generalizedJordanBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K} :
    GeneralizedJordanBlockWitnessData A → HasGeneralizedJordanMatrix A := by
  intro hA
  rcases hA with ⟨P, J, hP, hData, hEq⟩
  rcases hData with ⟨data, _⟩
  exact ⟨P, J, hP, ⟨data⟩, hEq⟩

theorem generalizedJordanBlockData_of_hasGeneralizedJordanMatrix
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K} :
    HasGeneralizedJordanMatrix A → GeneralizedJordanBlockWitnessData A := by
  intro hA
  rcases hA with ⟨P, J, hP, hJ, hEq⟩
  rcases hJ with ⟨data⟩
  exact ⟨P, J, hP, ⟨data, trivial⟩, hEq⟩

theorem generalizedJordanBlockData_of_generalizedBridgeBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {tag : String} {A : Matrix ι ι K} :
    GeneralizedJordanBridgeBlockData tag A →
      GeneralizedJordanBlockWitnessData A := by
  intro hA
  exact hA.2

theorem generalizedBridgeBlockData_of_generalizedJordanBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (tag : String) {A : Matrix ι ι K} :
    GeneralizedJordanBlockWitnessData A →
      GeneralizedJordanBridgeBlockData tag A := by
  intro hA
  exact ⟨rfl, hA⟩

theorem hasGeneralizedJordanMatrix_of_generalizedBridgeBlockData
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {tag : String} {A : Matrix ι ι K} :
    GeneralizedJordanBridgeBlockData tag A → HasGeneralizedJordanMatrix A :=
  hasGeneralizedJordanMatrix_of_generalizedJordanBlockData ∘
    generalizedJordanBlockData_of_generalizedBridgeBlockData

/-- Generalized Jordan matrix data is invariant under index reindexing. -/
theorem isGeneralizedJordanMatrix_reindex
    [Field K]
    {κ : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    (e : ι ≃ κ) {J : Matrix ι ι K}
    (hJ : IsGeneralizedJordanMatrix J) :
    IsGeneralizedJordanMatrix (Matrix.reindex e e J) := by
  rcases hJ with ⟨d⟩
  refine ⟨{
    block := d.block
    poly := d.poly
    poly_monic := d.poly_monic
    poly_irreducible := d.poly_irreducible
    exponent := d.exponent
    exponent_pos := d.exponent_pos
    total_size := ?_
    blockIndexEquiv := e.symm.trans d.blockIndexEquiv
    block_form := ?_
  }⟩
  · simpa [Fintype.card_congr e] using d.total_size
  · ext x y
    simpa [Matrix.reindex_apply] using congrFun (congrFun d.block_form x) y

/--
Block-diagonal generalized Jordan matrices combine to another generalized
Jordan matrix on the lexicographic sum index.
-/
theorem isGeneralizedJordanMatrix_blockDiag_lex
    [Field K]
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [LinearOrder α] [LinearOrder β]
    (J₁ : Matrix α α K) (J₂ : Matrix β β K)
    (h₁ : IsGeneralizedJordanMatrix J₁)
    (h₂ : IsGeneralizedJordanMatrix J₂) :
    IsGeneralizedJordanMatrix (jordanBlockDiagLex J₁ J₂) := by
  classical
  rcases h₁ with ⟨d₁⟩
  rcases h₂ with ⟨d₂⟩
  refine ⟨{
    block := ULift.{max u v, u} d₁.block ⊕ ULift.{max u v, v} d₂.block
    linearOrder_block := inferInstanceAs
      (LinearOrder (ULift.{max u v, u} d₁.block ⊕ₗ
        ULift.{max u v, v} d₂.block))
    poly := fun b => match b with
      | Sum.inl b => d₁.poly b.down
      | Sum.inr b => d₂.poly b.down
    poly_monic := ?_
    poly_irreducible := ?_
    exponent := fun b => match b with
      | Sum.inl b => d₁.exponent b.down
      | Sum.inr b => d₂.exponent b.down
    exponent_pos := ?_
    total_size := ?_
    blockIndexEquiv := ?_
    block_form := ?_
  }⟩
  · intro b
    cases b with
    | inl b => exact d₁.poly_monic b.down
    | inr b => exact d₂.poly_monic b.down
  · intro b
    cases b with
    | inl b => exact d₁.poly_irreducible b.down
    | inr b => exact d₂.poly_irreducible b.down
  · intro b
    cases b with
    | inl b => exact d₁.exponent_pos b.down
    | inr b => exact d₂.exponent_pos b.down
  · have hsum₁ :
        (∑ b : ULift.{max u v, u} d₁.block,
            d₁.exponent b.down * (d₁.poly b.down).natDegree) =
          ∑ b : d₁.block, d₁.exponent b * (d₁.poly b).natDegree := by
      exact Fintype.sum_equiv Equiv.ulift
        (fun b => d₁.exponent b.down * (d₁.poly b.down).natDegree)
        (fun b => d₁.exponent b * (d₁.poly b).natDegree)
        (fun b => rfl)
    have hsum₂ :
        (∑ b : ULift.{max u v, v} d₂.block,
            d₂.exponent b.down * (d₂.poly b.down).natDegree) =
          ∑ b : d₂.block, d₂.exponent b * (d₂.poly b).natDegree := by
      exact Fintype.sum_equiv Equiv.ulift
        (fun b => d₂.exponent b.down * (d₂.poly b.down).natDegree)
        (fun b => d₂.exponent b * (d₂.poly b).natDegree)
        (fun b => rfl)
    simp [Fintype.card_sum, Fintype.card_lex, hsum₁, hsum₂,
      d₁.total_size, d₂.total_size]
  · exact
      (sumToLexEquiv α β).symm.trans <|
        (Equiv.sumCongr d₁.blockIndexEquiv d₂.blockIndexEquiv).trans <|
        (Equiv.sumCongr
          (Equiv.sigmaCongr Equiv.ulift.symm
            (fun b => Equiv.cast (by
              change generalizedBlockCoord (d₁.poly b) (d₁.exponent b) =
                generalizedBlockCoord (d₁.poly b) (d₁.exponent b)
              rfl)))
          (Equiv.sigmaCongr Equiv.ulift.symm
            (fun b => Equiv.cast (by
              change generalizedBlockCoord (d₂.poly b) (d₂.exponent b) =
                generalizedBlockCoord (d₂.poly b) (d₂.exponent b)
              rfl)))).trans <|
          (Equiv.sumSigmaDistrib
            (fun b : ULift.{max u v, u} d₁.block ⊕
                ULift.{max u v, v} d₂.block =>
              generalizedBlockCoord
                (match b with
                | Sum.inl b => d₁.poly b.down
                | Sum.inr b => d₂.poly b.down)
                (match b with
                | Sum.inl b => d₁.exponent b.down
                | Sum.inr b => d₂.exponent b.down))).symm
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
        simpa [jordanBlockDiagLex, Matrix.reindex_apply, Matrix.blockDiagonal']
    | inr bx =>
      cases bY with
      | inl bY =>
        simpa [jordanBlockDiagLex, Matrix.reindex_apply, Matrix.blockDiagonal']
      | inr bY =>
        have hentry :=
          congrFun (congrFun d₂.block_form ⟨bx.down, ix⟩) ⟨bY.down, iy⟩
        simpa [jordanBlockDiagLex, Matrix.reindex_apply,
          Matrix.blockDiagonal'] using hentry

/-- A generalized Jordan block is a generalized Jordan matrix. -/
theorem isGeneralizedJordanMatrix_generalizedJordanBlock
    [Field K] (p : K[X]) (k : Nat)
    (hp_monic : p.Monic) (hp_irred : Irreducible p) (hk : 0 < k) :
    IsGeneralizedJordanMatrix (generalizedJordanBlock p k) := by
  classical
  refine ⟨{
    block := PUnit
    poly := fun _ => p
    poly_monic := fun _ => hp_monic
    poly_irreducible := fun _ => hp_irred
    exponent := fun _ => k
    exponent_pos := fun _ => hk
    total_size := ?_
    blockIndexEquiv :=
      (Equiv.uniqueSigma
        (fun _ : PUnit => (Fin k) × Fin p.natDegree)).symm
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
        simp [Matrix.reindex_apply, Matrix.blockDiagonal',
          Equiv.uniqueSigma_apply]

/-- A generalized Jordan block has a trivial generalized Jordan similarity witness. -/
theorem hasGeneralizedJordanMatrix_of_single_block
    [Field K] (p : K[X]) (k : Nat)
    (hp_monic : p.Monic) (hp_irred : Irreducible p) (hk : 0 < k) :
    HasGeneralizedJordanMatrix (generalizedJordanBlock p k) := by
  refine ⟨1, generalizedJordanBlock p k, invertibleMatrix_one, ?_, ?_⟩
  · exact isGeneralizedJordanMatrix_generalizedJordanBlock p k hp_monic hp_irred hk
  · simp

/-- Empty matrices have empty generalized Jordan block data. -/
theorem isGeneralizedJordanMatrix_empty
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι] [IsEmpty ι]
    (J : Matrix ι ι K) :
    IsGeneralizedJordanMatrix J := by
  refine ⟨{
    block := ULift.{u} (Fin 0)
    poly := fun b => Fin.elim0 b.down
    poly_monic := fun b => Fin.elim0 b.down
    poly_irreducible := fun b => Fin.elim0 b.down
    exponent := fun b => Fin.elim0 b.down
    exponent_pos := fun b => Fin.elim0 b.down
    total_size := ?_
    blockIndexEquiv := ?_
    block_form := ?_
  }⟩
  · simp
  · exact
      { toFun := fun i => False.elim (IsEmpty.false i)
        invFun := fun x => Fin.elim0 x.1.down
        left_inv := fun i => False.elim (IsEmpty.false i)
        right_inv := fun x => Fin.elim0 x.1.down }
  · ext x
    exact Fin.elim0 x.1.down

/-- Empty matrices have a trivial generalized Jordan similarity witness. -/
theorem base_generalized_jordan_empty
    [Field K] [Fintype ι] [DecidableEq ι] [LinearOrder ι] [IsEmpty ι]
    (A : Matrix ι ι K) :
    HasGeneralizedJordanMatrix A := by
  refine ⟨1, A, invertibleMatrix_one, ?_, ?_⟩
  · exact isGeneralizedJordanMatrix_empty A
  · simp

/-- Generalized Jordan similarity witnesses are invariant under index reindexing. -/
theorem hasGeneralizedJordanMatrix_reindex
    [Field K]
    {κ : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    (e : ι ≃ κ) {A : Matrix ι ι K}
    (hA : HasGeneralizedJordanMatrix A) :
    HasGeneralizedJordanMatrix (Matrix.reindex e e A) := by
  rcases hA with ⟨P, J, hP, hJ, hEq⟩
  refine ⟨Matrix.reindex e e P, Matrix.reindex e e J, ?_, ?_, ?_⟩
  · exact invertibleMatrix_reindex e hP
  · exact isGeneralizedJordanMatrix_reindex e hJ
  · have h := congrArg (Matrix.reindex e e) hEq
    simpa [Matrix.submatrix_mul_equiv, Matrix.inv_reindex] using h

/-- Dependent block-diagonal matrices with invertible diagonal blocks are invertible. -/
lemma invertibleMatrix_blockDiagonal'
    [Field K]
    {α : Type u} {β : α → Type w}
    [Fintype α] [DecidableEq α]
    [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
    {P : ∀ a, Matrix (β a) (β a) K}
    (hP : ∀ a, InvertibleMatrix (P a)) :
    InvertibleMatrix (Matrix.blockDiagonal' P) := by
  classical
  let Q : Matrix ((a : α) × β a) ((a : α) × β a) K :=
    Matrix.blockDiagonal' fun a => (P a)⁻¹
  have hmul : Matrix.blockDiagonal' P * Q = 1 := by
    have hdiag :
        Matrix.blockDiagonal' (fun a => P a * (P a)⁻¹) =
          Matrix.blockDiagonal' P * Matrix.blockDiagonal' (fun a => (P a)⁻¹) := by
      exact Matrix.blockDiagonal'_mul P (fun a => (P a)⁻¹)
    rw [← hdiag]
    have hpoint : (fun a => P a * (P a)⁻¹) = (1 : ∀ a, Matrix (β a) (β a) K) := by
      funext a
      haveI : Invertible (P a) := (hP a).invertible
      simpa using Matrix.mul_inv_of_invertible (P a)
    simp [hpoint]
  have hmul' : Q * Matrix.blockDiagonal' P = 1 := by
    have hdiag :
        Matrix.blockDiagonal' (fun a => (P a)⁻¹ * P a) =
          Matrix.blockDiagonal' (fun a => (P a)⁻¹) * Matrix.blockDiagonal' P := by
      exact Matrix.blockDiagonal'_mul (fun a => (P a)⁻¹) P
    rw [← hdiag]
    have hpoint : (fun a => (P a)⁻¹ * P a) = (1 : ∀ a, Matrix (β a) (β a) K) := by
      funext a
      haveI : Invertible (P a) := (hP a).invertible
      simpa using Matrix.inv_mul_of_invertible (P a)
    simp [hpoint]
  exact isUnit_iff_exists.mpr ⟨Q, hmul, hmul'⟩

/--
Dependent block-diagonal generalized Jordan matrices combine to another
generalized Jordan matrix on the sigma index.
-/
theorem isGeneralizedJordanMatrix_blockDiagonal'
    [Field K]
    {α : Type u} {β : α → Type w}
    [Fintype α] [DecidableEq α] [LinearOrder α]
    [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, LinearOrder (β a)]
    [LinearOrder ((a : α) × β a)]
    (J : ∀ a, Matrix (β a) (β a) K)
    (hJ : ∀ a, IsGeneralizedJordanMatrix (J a)) :
    IsGeneralizedJordanMatrix (Matrix.blockDiagonal' J) := by
  classical
  let d : ∀ a, GeneralizedJordanBlockData (J a) := fun a =>
    Classical.choice (hJ a)
  refine ⟨{
    block := (a : α) × (d a).block
    linearOrder_block := LinearOrder.lift'
      (Fintype.equivFin ((a : α) × (d a).block))
      (Fintype.equivFin ((a : α) × (d a).block)).injective
    poly := fun b => (d b.1).poly b.2
    poly_monic := ?_
    poly_irreducible := ?_
    exponent := fun b => (d b.1).exponent b.2
    exponent_pos := ?_
    total_size := ?_
    blockIndexEquiv := ?_
    block_form := ?_
  }⟩
  · intro b
    exact (d b.1).poly_monic b.2
  · intro b
    exact (d b.1).poly_irreducible b.2
  · intro b
    exact (d b.1).exponent_pos b.2
  · calc
      (∑ b : (a : α) × (d a).block,
          (d b.1).exponent b.2 * ((d b.1).poly b.2).natDegree)
          =
        ∑ a : α, ∑ b : (d a).block,
          (d a).exponent b * ((d a).poly b).natDegree := by
          exact Fintype.sum_sigma'
            (fun a b => (d a).exponent b * ((d a).poly b).natDegree)
      _ = ∑ a : α, Fintype.card (β a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact (d a).total_size
      _ = Fintype.card ((a : α) × β a) := by
          simp
  · exact
      (Equiv.sigmaCongrRight
        (fun a => (d a).blockIndexEquiv)).trans
        (Equiv.sigmaAssoc
          (fun a b => generalizedBlockCoord ((d a).poly b)
            ((d a).exponent b))).symm
  · ext x y
    rcases x with ⟨⟨aX, bX⟩, ix⟩
    rcases y with ⟨⟨aY, bY⟩, iy⟩
    by_cases hbase : aX = aY
    · subst aY
      have hentry :=
        congrFun (congrFun (d aX).block_form ⟨bX, ix⟩) ⟨bY, iy⟩
      simpa [Matrix.reindex_apply, Matrix.blockDiagonal', Equiv.sigmaAssoc,
        Equiv.sigmaCongrRight] using hentry
    · simpa [Matrix.reindex_apply, Matrix.blockDiagonal',
        Equiv.sigmaAssoc, Equiv.sigmaCongrRight, hbase]

/-- Dependent block-diagonal generalized Jordan witnesses combine on the sigma index. -/
theorem hasGeneralizedJordanMatrix_blockDiagonal'
    [Field K]
    {α : Type u} {β : α → Type w}
    [Fintype α] [DecidableEq α] [LinearOrder α]
    [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, LinearOrder (β a)]
    [LinearOrder ((a : α) × β a)]
    (A : ∀ a, Matrix (β a) (β a) K)
    (hA : ∀ a, HasGeneralizedJordanMatrix (A a)) :
    HasGeneralizedJordanMatrix (Matrix.blockDiagonal' A) := by
  classical
  choose P J hP hJ hEq using hA
  let Pblk : Matrix ((a : α) × β a) ((a : α) × β a) K :=
    Matrix.blockDiagonal' P
  let Jblk : Matrix ((a : α) × β a) ((a : α) × β a) K :=
    Matrix.blockDiagonal' J
  have hPblk : InvertibleMatrix Pblk := by
    simpa [Pblk] using (invertibleMatrix_blockDiagonal' (P := P) hP)
  refine ⟨Pblk, Jblk, hPblk, ?_, ?_⟩
  · exact isGeneralizedJordanMatrix_blockDiagonal' J hJ
  · haveI hPblkI : Invertible Pblk := hPblk.invertible
    have hPinv :
        Pblk⁻¹ = Matrix.blockDiagonal' fun a => (P a)⁻¹ := by
      apply Matrix.inv_eq_right_inv
      have hdiag :
          Matrix.blockDiagonal' (fun a => P a * (P a)⁻¹) =
            Matrix.blockDiagonal' P * Matrix.blockDiagonal' (fun a => (P a)⁻¹) := by
        exact Matrix.blockDiagonal'_mul P (fun a => (P a)⁻¹)
      rw [← hdiag]
      have hpoint : (fun a => P a * (P a)⁻¹) = (1 : ∀ a, Matrix (β a) (β a) K) := by
        funext a
        haveI : Invertible (P a) := (hP a).invertible
        simpa using Matrix.mul_inv_of_invertible (P a)
      simp [hpoint]
    rw [hPinv]
    have hmul₁ :
        Matrix.blockDiagonal' (fun a => P a * J a) =
          Matrix.blockDiagonal' P * Matrix.blockDiagonal' J := by
      exact Matrix.blockDiagonal'_mul P J
    have hmul₂ :
        Matrix.blockDiagonal' (fun a => (P a * J a) * (P a)⁻¹) =
          Matrix.blockDiagonal' (fun a => P a * J a) *
            Matrix.blockDiagonal' (fun a => (P a)⁻¹) := by
      exact Matrix.blockDiagonal'_mul (fun a => P a * J a) (fun a => (P a)⁻¹)
    calc
      Matrix.blockDiagonal' A =
          Matrix.blockDiagonal' (fun a => P a * J a * (P a)⁻¹) := by
            have hfun : A = fun a => P a * J a * (P a)⁻¹ := by
              funext a
              exact hEq a
            simpa [hfun]
      _ = Pblk * Jblk * Matrix.blockDiagonal' (fun a => (P a)⁻¹) := by
            rw [hmul₂, hmul₁]

/-- Block-diagonal generalized Jordan witnesses combine over lexicographic sums. -/
theorem hasGeneralizedJordanMatrix_blockDiag_lex
    [Field K]
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [LinearOrder α] [LinearOrder β]
    (A₁ : Matrix α α K) (A₂ : Matrix β β K)
    (h₁ : HasGeneralizedJordanMatrix A₁)
    (h₂ : HasGeneralizedJordanMatrix A₂) :
    HasGeneralizedJordanMatrix (jordanBlockDiagLex A₁ A₂) := by
  classical
  rcases h₁ with ⟨P₁, J₁, hP₁, hJ₁, hEq₁⟩
  rcases h₂ with ⟨P₂, J₂, hP₂, hJ₂, hEq₂⟩
  let P := jordanBlockDiagLex P₁ P₂
  let J := jordanBlockDiagLex J₁ J₂
  refine ⟨P, J, ?_, ?_, ?_⟩
  · exact invertibleMatrix_blockDiag_lex hP₁ hP₂
  · exact isGeneralizedJordanMatrix_blockDiag_lex J₁ J₂ hJ₁ hJ₂
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

end MatDecompFormal.Instances
