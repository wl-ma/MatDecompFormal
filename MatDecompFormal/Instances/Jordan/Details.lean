import MatDecompFormal.Framework.UniverseDecompositionSquareSubtype
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Instances.Schur.Details

universe u v

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
