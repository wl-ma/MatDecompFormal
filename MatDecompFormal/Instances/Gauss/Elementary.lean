import MatDecompFormal.Instances.Gauss.Strategy
import Mathlib.LinearAlgebra.Matrix.Swap

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

variable {R : Type v}

section HeadPivot

variable [DivisionRing R]
variable {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The `1 × 1` head block inverse used by the concrete Gauss step. -/
noncomputable def gaussHeadInvBlock
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R) : Matrix Unit Unit R :=
  fun _ _ => (A.toBlocks₁₁ () ())⁻¹

/-- Concrete left factor clearing the head column after the head pivot is nonzero. -/
noncomputable def gaussPlainHeadLeft
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ m) (Unit ⊕ m) R :=
  let H : Matrix Unit Unit R := gaussHeadInvBlock A
  fromBlocks H 0 (-(A.toBlocks₂₁ * H)) 1

/-- Explicit inverse for `gaussPlainHeadLeft`. -/
noncomputable def gaussPlainHeadLeftInv
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ m) (Unit ⊕ m) R :=
  fromBlocks A.toBlocks₁₁ 0 A.toBlocks₂₁ 1

/-- Concrete right factor clearing the head row after the head column has been cleared. -/
noncomputable def gaussPlainHeadRight
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) R :=
  let H : Matrix Unit Unit R := gaussHeadInvBlock A
  fromBlocks 1 (-(H * A.toBlocks₁₂)) 0 1

/-- Explicit inverse for `gaussPlainHeadRight`. -/
noncomputable def gaussPlainHeadRightInv
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) R :=
  let H : Matrix Unit Unit R := gaussHeadInvBlock A
  fromBlocks 1 (H * A.toBlocks₁₂) 0 1

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
lemma gaussHeadInvBlock_mul_head
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R)
    (h : A.toBlocks₁₁ () () ≠ 0) :
    gaussHeadInvBlock A * A.toBlocks₁₁ = 1 := by
  ext i j
  cases i
  cases j
  simp [Matrix.mul_apply, gaussHeadInvBlock, h]

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
lemma gauss_head_mul_invBlock
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R)
    (h : A.toBlocks₁₁ () () ≠ 0) :
    A.toBlocks₁₁ * gaussHeadInvBlock A = 1 := by
  ext i j
  cases i
  cases j
  simp [Matrix.mul_apply, gaussHeadInvBlock, h]

omit [Fintype n] [DecidableEq n] in
lemma gaussPlainHeadLeft_invertible
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R)
    (h : A.toBlocks₁₁ () () ≠ 0) :
    GaussInvertibleMatrix (gaussPlainHeadLeft A) := by
  refine ⟨gaussPlainHeadLeftInv A, ?_, ?_⟩
  · simp [gaussPlainHeadLeft, gaussPlainHeadLeftInv, fromBlocks_multiply,
      gauss_head_mul_invBlock A h, Matrix.fromBlocks_one]
  · have h21 :
        -(A.toBlocks₂₁ * gaussHeadInvBlock A * A.toBlocks₁₁) + A.toBlocks₂₁ =
          0 := by
        rw [Matrix.mul_assoc, gaussHeadInvBlock_mul_head A h, Matrix.mul_one]
        simp
    simp [gaussPlainHeadLeft, gaussPlainHeadLeftInv, fromBlocks_multiply,
      gaussHeadInvBlock_mul_head A h, Matrix.fromBlocks_one, h21]

omit [Fintype m] [DecidableEq m] in
lemma gaussPlainHeadRight_invertible
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R)
    (_h : A.toBlocks₁₁ () () ≠ 0) :
    GaussInvertibleMatrix (gaussPlainHeadRight A) := by
  refine ⟨gaussPlainHeadRightInv A, ?_, ?_⟩
  · simp [gaussPlainHeadRight, gaussPlainHeadRightInv, fromBlocks_multiply,
      Matrix.fromBlocks_one]
  · simp [gaussPlainHeadRight, gaussPlainHeadRightInv, fromBlocks_multiply,
      Matrix.fromBlocks_one]

/--
In head-tail coordinates, the concrete Gauss factors isolate a unit head pivot
and clear the rest of the head row and column.
-/
lemma gaussPlainHead_step_blocks
    (A : Matrix (Unit ⊕ m) (Unit ⊕ n) R)
    (h : A.toBlocks₁₁ () () ≠ 0) :
    let B := gaussPlainHeadLeft A * A * gaussPlainHeadRight A
    B.toBlocks₁₁ = 1 ∧ B.toBlocks₁₂ = 0 ∧ B.toBlocks₂₁ = 0 := by
  let L : Matrix (Unit ⊕ m) (Unit ⊕ m) R := gaussPlainHeadLeft A
  let Q : Matrix (Unit ⊕ n) (Unit ⊕ n) R := gaussPlainHeadRight A
  have hA :
      A = fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂ := by
    exact (fromBlocks_toBlocks A).symm
  have hB :
      gaussPlainHeadLeft A * A * gaussPlainHeadRight A =
        L *
          (fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂) *
            Q := by
    rw [hA]
    rfl
  dsimp
  rw [hB]
  constructor
  · ext i j
    cases i
    cases j
    simp [L, Q, gaussPlainHeadLeft, gaussPlainHeadRight, fromBlocks_multiply,
      gaussHeadInvBlock_mul_head A h, Matrix.mul_assoc]
  constructor
  · ext i j
    cases i
    simp [L, Q, gaussPlainHeadLeft, gaussPlainHeadRight, fromBlocks_multiply,
      gaussHeadInvBlock_mul_head A h, Matrix.mul_assoc]
  · ext i j
    cases j
    have h21 :
        -(A.toBlocks₂₁ * (gaussHeadInvBlock A * A.toBlocks₁₁)) + A.toBlocks₂₁ =
          0 := by
        rw [gaussHeadInvBlock_mul_head A h, Matrix.mul_one]
        simp
    simp [L, Q, gaussPlainHeadLeft, gaussPlainHeadRight, fromBlocks_multiply,
      gaussHeadInvBlock_mul_head A h, Matrix.mul_assoc]

end HeadPivot

section PivotChoice

variable [DivisionRing R]
variable {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
  [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]

omit [DecidableEq m] [LinearOrder m] [Nonempty m] [DecidableEq n] [LinearOrder n]
  [Nonempty n] in
lemma exists_nonzero_entry_of_matrix_ne_zero
    (A : Matrix m n R) (hA : A ≠ 0) :
    ∃ i j, A i j ≠ 0 := by
  classical
  by_contra hnone
  apply hA
  ext i j
  by_contra hij
  exact hnone ⟨i, j, hij⟩

noncomputable def gaussPivotRow (A : Matrix m n R) : m :=
  by
    classical
    exact
      if hA : A = 0 then headElem (α := m)
      else Classical.choose (exists_nonzero_entry_of_matrix_ne_zero A hA)

noncomputable def gaussPivotCol (A : Matrix m n R) : n :=
  by
    classical
    exact
      if hA : A = 0 then headElem (α := n)
      else Classical.choose (Classical.choose_spec
        (exists_nonzero_entry_of_matrix_ne_zero A hA))

omit [DecidableEq m] [DecidableEq n] in
lemma gaussPivot_entry_ne_zero
    (A : Matrix m n R) (hA : A ≠ 0) :
    A (gaussPivotRow A) (gaussPivotCol A) ≠ 0 := by
  classical
  let w := exists_nonzero_entry_of_matrix_ne_zero A hA
  have hrow : gaussPivotRow A = Classical.choose w := by
    simp [gaussPivotRow, hA]
  have hcol :
      gaussPivotCol A = Classical.choose (Classical.choose_spec w) := by
    simp [gaussPivotCol, hA]
  rw [hrow, hcol]
  exact Classical.choose_spec (Classical.choose_spec w)

noncomputable def gaussSwapToHeadLeft (A : Matrix m n R) : Matrix m m R :=
  Matrix.swap R (headElem (α := m)) (gaussPivotRow A)

noncomputable def gaussSwapToHeadRight (A : Matrix m n R) : Matrix n n R :=
  Matrix.swap R (headElem (α := n)) (gaussPivotCol A)

omit [DecidableEq n] [LinearOrder n] [Nonempty n] in
lemma gaussSwapToHeadLeft_invertible (A : Matrix m n R) :
    GaussInvertibleMatrix (gaussSwapToHeadLeft A) :=
  ⟨gaussSwapToHeadLeft A, by simp [gaussSwapToHeadLeft, Matrix.swap_mul_self],
    by simp [gaussSwapToHeadLeft, Matrix.swap_mul_self]⟩

omit [DecidableEq m] [LinearOrder m] [Nonempty m] in
lemma gaussSwapToHeadRight_invertible (A : Matrix m n R) :
    GaussInvertibleMatrix (gaussSwapToHeadRight A) :=
  ⟨gaussSwapToHeadRight A, by simp [gaussSwapToHeadRight, Matrix.swap_mul_self],
    by simp [gaussSwapToHeadRight, Matrix.swap_mul_self]⟩

lemma gaussSwapToHead_entry_ne_zero
    (A : Matrix m n R) (hA : A ≠ 0) :
    (gaussSwapToHeadLeft A * A * gaussSwapToHeadRight A)
      (headElem (α := m)) (headElem (α := n)) ≠ 0 := by
  classical
  have hrow :
      (gaussSwapToHeadLeft A * A)
        (headElem (α := m)) (gaussPivotCol A) =
        A (gaussPivotRow A) (gaussPivotCol A) := by
    simpa [gaussSwapToHeadLeft] using
      (Matrix.swap_mul_apply_left
        (i := headElem (α := m)) (j := gaussPivotRow A)
        (a := gaussPivotCol A) (g := A))
  have hcol :
      (gaussSwapToHeadLeft A * A * gaussSwapToHeadRight A)
        (headElem (α := m)) (headElem (α := n)) =
        (gaussSwapToHeadLeft A * A)
          (headElem (α := m)) (gaussPivotCol A) := by
    simpa [gaussSwapToHeadRight] using
      (Matrix.mul_swap_apply_left
        (i := headElem (α := n)) (j := gaussPivotCol A)
        (a := headElem (α := m)) (g := gaussSwapToHeadLeft A * A))
  exact hcol.trans_ne (hrow.trans_ne (gaussPivot_entry_ne_zero A hA))

end PivotChoice

section ConcreteStep

variable [DivisionRing R]
variable {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
  [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]

noncomputable def gaussSwappedMatrix (A : Matrix m n R) : Matrix m n R :=
  gaussSwapToHeadLeft A * A * gaussSwapToHeadRight A

noncomputable def gaussSwappedPlain (A : Matrix m n R) :
    Matrix (Unit ⊕ GaussTailRowIdx m) (Unit ⊕ GaussTailColIdx n) R :=
  Matrix.reindex (headTailEquiv (α := m)) (headTailEquiv (α := n))
    (gaussSwappedMatrix A)

lemma gaussSwappedPlain_head_ne_zero
    (A : Matrix m n R) (hA : A ≠ 0) :
    (gaussSwappedPlain A).toBlocks₁₁ () () ≠ 0 := by
  classical
  have hswap := gaussSwapToHead_entry_ne_zero A hA
  simpa [gaussSwappedPlain, gaussSwappedMatrix, Matrix.toBlocks₁₁,
    Matrix.reindex_apply] using hswap

noncomputable def gaussHeadLeftOriginal (A : Matrix m n R) : Matrix m m R :=
  Matrix.reindex (headTailEquiv (α := m)).symm (headTailEquiv (α := m)).symm
    (gaussPlainHeadLeft (gaussSwappedPlain A))

noncomputable def gaussHeadRightOriginal (A : Matrix m n R) : Matrix n n R :=
  Matrix.reindex (headTailEquiv (α := n)).symm (headTailEquiv (α := n)).symm
    (gaussPlainHeadRight (gaussSwappedPlain A))

noncomputable def gaussConcreteStepP (A : Matrix m n R) : Matrix m m R :=
  by
    classical
    exact
      if hA : A = 0 then 1
      else gaussHeadLeftOriginal A * gaussSwapToHeadLeft A

noncomputable def gaussConcreteStepQ (A : Matrix m n R) : Matrix n n R :=
  by
    classical
    exact
      if hA : A = 0 then 1
      else gaussSwapToHeadRight A * gaussHeadRightOriginal A

lemma gaussHeadLeftOriginal_invertible
    (A : Matrix m n R) (hA : A ≠ 0) :
    GaussInvertibleMatrix (gaussHeadLeftOriginal A) := by
  exact gaussInvertibleMatrix_reindex (headTailEquiv (α := m)).symm
    (gaussPlainHeadLeft_invertible (gaussSwappedPlain A)
      (gaussSwappedPlain_head_ne_zero A hA))

lemma gaussHeadRightOriginal_invertible
    (A : Matrix m n R) (hA : A ≠ 0) :
    GaussInvertibleMatrix (gaussHeadRightOriginal A) := by
  exact gaussInvertibleMatrix_reindex (headTailEquiv (α := n)).symm
    (gaussPlainHeadRight_invertible (gaussSwappedPlain A)
      (gaussSwappedPlain_head_ne_zero A hA))

lemma gaussConcreteStepP_invertible (A : Matrix m n R) :
    GaussInvertibleMatrix (gaussConcreteStepP A) := by
  classical
  by_cases hA : A = 0
  · simpa [gaussConcreteStepP, hA] using
      (gaussInvertibleMatrix_one : GaussInvertibleMatrix (1 : Matrix m m R))
  · simpa [gaussConcreteStepP, hA] using
      (gaussHeadLeftOriginal_invertible A hA).mul
        (gaussSwapToHeadLeft_invertible A)

lemma gaussConcreteStepQ_invertible (A : Matrix m n R) :
    GaussInvertibleMatrix (gaussConcreteStepQ A) := by
  classical
  by_cases hA : A = 0
  · simpa [gaussConcreteStepQ, hA] using
      (gaussInvertibleMatrix_one : GaussInvertibleMatrix (1 : Matrix n n R))
  · simpa [gaussConcreteStepQ, hA] using
      (gaussSwapToHeadRight_invertible A).mul
        (gaussHeadRightOriginal_invertible A hA)

lemma gauss_reindex_concrete_nonzero
    (A : Matrix m n R) (hA : A ≠ 0) :
    Matrix.reindex (headTailEquiv (α := m)) (headTailEquiv (α := n))
        (gaussConcreteStepP A * A * gaussConcreteStepQ A) =
      gaussPlainHeadLeft (gaussSwappedPlain A) *
        gaussSwappedPlain A *
          gaussPlainHeadRight (gaussSwappedPlain A) := by
  classical
  let er := headTailEquiv (α := m)
  let ec := headTailEquiv (α := n)
  have hmain :
      gaussConcreteStepP A * A * gaussConcreteStepQ A =
        gaussHeadLeftOriginal A *
          (gaussSwapToHeadLeft A * A * gaussSwapToHeadRight A) *
            gaussHeadRightOriginal A := by
    simp [gaussConcreteStepP, gaussConcreteStepQ, hA, Matrix.mul_assoc]
  rw [hmain]
  have hleft :
      Matrix.reindex er er (gaussHeadLeftOriginal A) =
        gaussPlainHeadLeft (gaussSwappedPlain A) := by
    simp [gaussHeadLeftOriginal, er]
  have hmid :
      Matrix.reindex er ec
          (gaussSwapToHeadLeft A * A * gaussSwapToHeadRight A) =
        gaussSwappedPlain A := by
    simp [gaussSwappedPlain, gaussSwappedMatrix, er, ec, Matrix.mul_assoc]
  have hright :
      Matrix.reindex ec ec (gaussHeadRightOriginal A) =
        gaussPlainHeadRight (gaussSwappedPlain A) := by
    simp [gaussHeadRightOriginal, ec]
  calc
    Matrix.reindex er ec
        (gaussHeadLeftOriginal A *
          (gaussSwapToHeadLeft A * A * gaussSwapToHeadRight A) *
            gaussHeadRightOriginal A)
        =
      Matrix.reindex er er (gaussHeadLeftOriginal A) *
        Matrix.reindex er ec
          (gaussSwapToHeadLeft A * A * gaussSwapToHeadRight A) *
          Matrix.reindex ec ec (gaussHeadRightOriginal A) := by
        simp [Matrix.submatrix_mul_equiv, Matrix.mul_assoc]
    _ =
      gaussPlainHeadLeft (gaussSwappedPlain A) *
        gaussSwappedPlain A *
          gaussPlainHeadRight (gaussSwappedPlain A) := by
        rw [hleft, hmid, hright]

lemma gaussConcreteStep_ready (A : Matrix m n R) :
    GaussRankDescentReady (R := R) m n
      (gaussConcreteStepP A * A * gaussConcreteStepQ A) := by
  classical
  by_cases hA : A = 0
  · left
    simp [gaussConcreteStepP, gaussConcreteStepQ, hA]
  · right
    unfold GaussRankBlockReady
    rw [gauss_reindex_concrete_nonzero A hA]
    exact gaussPlainHead_step_blocks (gaussSwappedPlain A)
      (gaussSwappedPlain_head_ne_zero A hA)

/-- Concrete one-step Gauss elimination oracle over a division ring. -/
noncomputable def gaussRankStepOracle
    (R : Type v) [DivisionRing R]
    (m n : Type u) [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    GaussRankStepOracle R m n where
  P := gaussConcreteStepP
  Q := gaussConcreteStepQ
  invertible_P := gaussConcreteStepP_invertible
  invertible_Q := gaussConcreteStepQ_invertible
  ready := gaussConcreteStep_ready

end ConcreteStep

end MatDecompFormal.Instances
