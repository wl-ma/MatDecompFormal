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

/-- Data-oriented Smith normal-form payload. -/
structure SmithNormalFormData
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n R) where
  r : Type u
  fintype_r : Fintype r
  row : r → m
  col : r → n
  diag : r → R
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  successor : r → r → Prop
  entry_diag : ∀ k, D (row k) (col k) = diag k
  entry_zero : ∀ i j, (∀ k, row k ≠ i ∨ col k ≠ j) → D i j = 0
  divides_next : ∀ k l, successor k l → diag k ∣ diag l

attribute [instance] SmithNormalFormData.fintype_r

/-- Predicate saying a matrix is in data-oriented Smith normal form. -/
def IsSmithNormalForm
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n R) : Prop :=
  Nonempty (SmithNormalFormData D)

/-- Two-sided equivalence to a Smith normal-form matrix. -/
def HasSmithNormalForm
    [Semiring R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n R) : Prop :=
  ∃ P : Matrix m m R, ∃ Q : Matrix n n R, ∃ D : Matrix m n R,
    GaussInvertibleMatrix P ∧
    GaussInvertibleMatrix Q ∧
    IsSmithNormalForm D ∧
    D = P * A * Q

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
  row := fun k => Empty.elim k.down
  col := fun k => Empty.elim k.down
  diag := fun k => Empty.elim k.down
  row_injective := by intro k; cases k.down
  col_injective := by intro k; cases k.down
  successor := fun k _ => Empty.elim k.down
  entry_diag := by intro k; cases k.down
  entry_zero := by
    intro i j _h
    simp [hD]
  divides_next := by intro k; cases k.down

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
    row := fun k => em (data.row k)
    col := fun k => en (data.col k)
    diag := data.diag
    row_injective := ?_
    col_injective := ?_
    successor := data.successor
    entry_diag := ?_
    entry_zero := ?_
    divides_next := data.divides_next
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
  row := data.row
  col := data.col
  diag := fun _ => 1
  row_injective := data.row_injective
  col_injective := data.col_injective
  successor := fun _ _ => False
  entry_diag := data.entry_one
  entry_zero := data.entry_zero
  divides_next := by
    intro k l h
    cases h

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
  r := Unit ⊕ data.r
  fintype_r := inferInstance
  row := Sum.elim (fun _ => Sum.inl ()) (fun k => Sum.inr (data.row k))
  col := Sum.elim (fun _ => Sum.inl ()) (fun k => Sum.inr (data.col k))
  diag := Sum.elim (fun _ => d) data.diag
  row_injective := by
    intro a b h
    cases a with
    | inl au =>
        cases b with
        | inl bu => simp
        | inr bk => cases h
    | inr ak =>
        cases b with
        | inl bu => cases h
        | inr bk =>
            simp only [Sum.elim_inr, Sum.inr.injEq] at h
            exact congrArg Sum.inr (data.row_injective h)
  col_injective := by
    intro a b h
    cases a with
    | inl au =>
        cases b with
        | inl bu => simp
        | inr bk => cases h
    | inr ak =>
        cases b with
        | inl bu => cases h
        | inr bk =>
            simp only [Sum.elim_inr, Sum.inr.injEq] at h
            exact congrArg Sum.inr (data.col_injective h)
  successor := fun k l =>
    match k, l with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr k', Sum.inr l' => data.successor k' l'
    | _, _ => False
  entry_diag := by
    intro k
    cases k with
    | inl u => simp
    | inr k => simpa using data.entry_diag k
  entry_zero := by
    intro i j h
    cases i with
    | inl iu =>
        cases j with
        | inl ju =>
            exfalso
            exact (h (Sum.inl ())).elim (by simp) (by simp)
        | inr jn => simp
    | inr im =>
        cases j with
        | inl ju => simp
        | inr jn =>
            apply data.entry_zero
            intro k
            specialize h (Sum.inr k)
            rcases h with hrow | hcol
            · exact Or.inl (fun hk => hrow (by simp [hk]))
            · exact Or.inr (fun hk => hcol (by simp [hk]))
  divides_next := by
    intro k l hsucc
    cases k with
    | inl ku =>
        cases l with
        | inl lu => cases hsucc
        | inr ltail =>
            simpa [SmithNormalFormData.entry_diag] using hdiv (data.row ltail) (data.col ltail)
    | inr ktail =>
        cases l with
        | inl lu => cases hsucc
        | inr ltail =>
            exact data.divides_next ktail ltail hsucc

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

@[simp] lemma smithAppendZeroCols_inl (A : Matrix m n R) (i : m) (j : n) :
    smithAppendZeroCols (κ := κ) A i (Sum.inl j) = A i j :=
  rfl

@[simp] lemma smithAppendZeroCols_inr (A : Matrix m n R) (i : m) (j : κ) :
    smithAppendZeroCols (κ := κ) A i (Sum.inr j) = 0 :=
  rfl

/-- Smith-normal-form data remains valid after appending zero columns. -/
noncomputable def smithNormalFormData_appendZeroCols
    {D : Matrix m n R} (data : SmithNormalFormData D) :
    SmithNormalFormData (smithAppendZeroCols (κ := κ) D) where
  r := data.r
  fintype_r := data.fintype_r
  row := data.row
  col := fun k => Sum.inl (data.col k)
  diag := data.diag
  row_injective := data.row_injective
  col_injective := by
    intro a b h
    exact data.col_injective (Sum.inl.inj h)
  successor := data.successor
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
  divides_next := data.divides_next

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

lemma matrix_mul_appendZeroCols
    {ℓ : Type u} [Fintype ℓ]
    (P : Matrix ℓ m R) (A : Matrix m n R) :
    P * smithAppendZeroCols (κ := κ) A =
      smithAppendZeroCols (κ := κ) (P * A) := by
  ext i j
  cases j <;> simp [smithAppendZeroCols, Matrix.mul_apply]

lemma appendZeroCols_mul_blockDiag_right
    (A : Matrix m n R) (Q : Matrix n n R) :
    smithAppendZeroCols (κ := κ) A *
        (fromBlocks Q 0 0 (1 : Matrix κ κ R) :
          Matrix (n ⊕ κ) (n ⊕ κ) R) =
      smithAppendZeroCols (κ := κ) (A * Q) := by
  ext i j
  cases j with
  | inl jn =>
      simp [smithAppendZeroCols, Matrix.mul_apply, fromBlocks_apply]
  | inr jk =>
      simp [smithAppendZeroCols, Matrix.mul_apply, fromBlocks_apply]

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
    _ = P * smithAppendZeroCols (κ := κ) (A * Q) := by
      rw [matrix_mul_appendZeroCols]
    _ = P * (smithAppendZeroCols (κ := κ) A * Qblk) := by
      rw [appendZeroCols_mul_blockDiag_right]
    _ = P * smithAppendZeroCols (κ := κ) A * Qblk := by
      rw [Matrix.mul_assoc]

end AppendZeroCols

end BlockLift

end MatDecompFormal.Instances
