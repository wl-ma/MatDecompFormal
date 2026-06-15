import MatDecompFormal.Instances.Hessenberg.Boundary
import MatDecompFormal.Instances.Normal.Details
import MatDecompFormal.Instances.QR.Details
import MatDecompFormal.Instances.QR.Givens
import MatDecompFormal.Instances.QR.Householder

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open Sum.Lex

/-!
# Bidiagonalization Details

This file contains the target predicate, zero-pattern facts, and algebraic
transport/lift lemmas used by the rectangular descent-template implementation
of unitary bidiagonalization.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n : Type u}

/-- Upper bidiagonal zero pattern for arbitrary finite ordered row/column types. -/
def IsUpperBidiagonal
    {m n R : Type*} [Fintype m] [LinearOrder m]
    [Fintype n] [LinearOrder n] [Zero R]
    (B : Matrix m n R) : Prop :=
  ∀ i j,
    finiteOrderRank n j < finiteOrderRank m i ∨
      finiteOrderRank m i + 1 < finiteOrderRank n j →
    B i j = 0

/-- Unitary two-sided upper-bidiagonalization target. -/
def HasUnitaryBidiagonalization
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) : Prop :=
  ∃ U : Matrix m m 𝕜, ∃ V : Matrix n n 𝕜, ∃ B : Matrix m n 𝕜,
    IsUnitaryMatrix U ∧
    IsUnitaryMatrix V ∧
    IsUpperBidiagonal B ∧
    A = U * B * Vᴴ

/--
Unitary bidiagonalization whose right factor fixes the distinguished head
coordinate. This is the recursive target needed for boundary-aware
bidiagonalization lifting: the parent first superdiagonal entry may survive,
so the tail right factor must not mix the tail head column with later columns.
-/
def HasUnitaryBidiagonalizationFixedRightHead
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (A : Matrix m n 𝕜) : Prop :=
  ∃ U : Matrix m m 𝕜, ∃ V : Matrix n n 𝕜, ∃ B : Matrix m n 𝕜,
    IsUnitaryMatrix U ∧
    IsUnitaryMatrix V ∧
    (∀ j : n, V (headElem (α := n)) j = if j = headElem (α := n) then 1 else 0) ∧
    IsUpperBidiagonal B ∧
    A = U * B * Vᴴ

theorem hasUnitaryBidiagonalization_of_fixedRightHead
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    {A : Matrix m n 𝕜} :
    HasUnitaryBidiagonalizationFixedRightHead A → HasUnitaryBidiagonalization A := by
  intro hA
  rcases hA with ⟨U, V, B, hU, hV, _hVhead, hB, hEq⟩
  exact ⟨U, V, B, hU, hV, hB, hEq⟩

/-- Real orthogonal two-sided upper-bidiagonalization target. -/
def HasOrthogonalBidiagonalization
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℝ) : Prop :=
  ∃ U : Matrix m m ℝ, ∃ V : Matrix n n ℝ, ∃ B : Matrix m n ℝ,
    IsOrthogonalMatrix U ∧
    IsOrthogonalMatrix V ∧
    IsUpperBidiagonal B ∧
    A = U * B * Vᵀ

/--
Product-level real two-sided bidiagonalization witness.

The proposition exposes finite left and right elementary-factor lists whose
products are the final orthogonal factors. It records final-factor data only;
it does not assert the intermediate Golub-Kahan boundary invariants unless a
theorem supplies such a stronger trace separately.
-/
def HasLeftRightProductOrthogonalBidiagonalization
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (LeftStepProp : Matrix m m ℝ → Prop)
    (RightStepProp : Matrix n n ℝ → Prop)
    (A : Matrix m n ℝ) : Prop :=
  ∃ leftSteps : List (Matrix m m ℝ),
  ∃ rightSteps : List (Matrix n n ℝ),
  ∃ U : Matrix m m ℝ, ∃ V : Matrix n n ℝ, ∃ B : Matrix m n ℝ,
    (∀ M ∈ leftSteps, LeftStepProp M) ∧
    (∀ M ∈ rightSteps, RightStepProp M) ∧
    matrixProduct leftSteps = U ∧
    matrixProduct rightSteps = V ∧
    IsOrthogonalMatrix U ∧
    IsOrthogonalMatrix V ∧
    IsUpperBidiagonal B ∧
    A = U * B * Vᵀ

def HasLeftRightHouseholderProductBidiagonalization
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℝ) : Prop :=
  HasLeftRightProductOrthogonalBidiagonalization
    IsHouseholderMatrix IsHouseholderMatrix A

def HasLeftRightGivensProductBidiagonalization
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℝ) : Prop :=
  HasLeftRightProductOrthogonalBidiagonalization
    IsGivensMatrix IsGivensMatrix A

/--
Final-factor trace predicate for real bidiagonalization.

The current trace level records elementary left/right factor lists and the
final bidiagonal factor. It is deliberately a Prop-level witness layer, not an
algorithmic step-by-step invariant for the classical bidiagonalization sweep.
-/
def BidiagonalizationTrace
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (LeftStepProp : Matrix m m ℝ → Prop)
    (RightStepProp : Matrix n n ℝ → Prop)
    (A : Matrix m n ℝ) : Prop :=
  HasLeftRightProductOrthogonalBidiagonalization LeftStepProp RightStepProp A

abbrev HouseholderBidiagonalizationTrace
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℝ) : Prop :=
  BidiagonalizationTrace IsHouseholderMatrix IsHouseholderMatrix A

abbrev GivensBidiagonalizationTrace
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℝ) : Prop :=
  BidiagonalizationTrace IsGivensMatrix IsGivensMatrix A

theorem hasOrthogonalBidiagonalization_of_leftRightProduct
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    {LeftStepProp : Matrix m m ℝ → Prop}
    {RightStepProp : Matrix n n ℝ → Prop}
    {A : Matrix m n ℝ} :
    HasLeftRightProductOrthogonalBidiagonalization LeftStepProp RightStepProp A →
      HasOrthogonalBidiagonalization A := by
  intro hA
  rcases hA with
    ⟨_leftSteps, _rightSteps, U, V, B, _hleft, _hright, _hUprod, _hVprod,
      hU, hV, hB, hEq⟩
  exact ⟨U, V, B, hU, hV, hB, hEq⟩

theorem hasOrthogonalBidiagonalization_of_hasLeftRightHouseholderProduct
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    {A : Matrix m n ℝ} :
    HasLeftRightHouseholderProductBidiagonalization A →
      HasOrthogonalBidiagonalization A :=
  hasOrthogonalBidiagonalization_of_leftRightProduct

theorem hasOrthogonalBidiagonalization_of_hasLeftRightGivensProduct
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    {A : Matrix m n ℝ} :
    HasLeftRightGivensProductBidiagonalization A →
      HasOrthogonalBidiagonalization A :=
  hasOrthogonalBidiagonalization_of_leftRightProduct

theorem hasLeftRightProduct_of_bidiagonalizationTrace
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    {LeftStepProp : Matrix m m ℝ → Prop}
    {RightStepProp : Matrix n n ℝ → Prop}
    {A : Matrix m n ℝ} :
    BidiagonalizationTrace LeftStepProp RightStepProp A →
      HasLeftRightProductOrthogonalBidiagonalization LeftStepProp RightStepProp A :=
  id

theorem hasLeftRightHouseholderProduct_of_trace
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    {A : Matrix m n ℝ} :
    HouseholderBidiagonalizationTrace A →
      HasLeftRightHouseholderProductBidiagonalization A :=
  id

theorem hasLeftRightGivensProduct_of_trace
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    {A : Matrix m n ℝ} :
    GivensBidiagonalizationTrace A →
      HasLeftRightGivensProductBidiagonalization A :=
  id

theorem hasLeftRightHouseholderProduct_of_hasOrthogonalBidiagonalization
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    {A : Matrix m n ℝ} :
    HasOrthogonalBidiagonalization A →
      HasLeftRightHouseholderProductBidiagonalization A := by
  intro hA
  rcases hA with ⟨U, V, B, hU, hV, hB, hEq⟩
  rcases isHouseholderProduct_of_isOrthogonalMatrix U hU with
    ⟨leftSteps, hleftSteps, hleftProduct⟩
  rcases isHouseholderProduct_of_isOrthogonalMatrix V hV with
    ⟨rightSteps, hrightSteps, hrightProduct⟩
  exact
    ⟨leftSteps, rightSteps, U, V, B, hleftSteps, hrightSteps,
      hleftProduct, hrightProduct, hU, hV, hB, hEq⟩

theorem householderBidiagonalizationTrace_of_hasOrthogonalBidiagonalization
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    {A : Matrix m n ℝ} :
    HasOrthogonalBidiagonalization A →
      HouseholderBidiagonalizationTrace A :=
  hasLeftRightHouseholderProduct_of_hasOrthogonalBidiagonalization

theorem hasOrthogonalBidiagonalization_of_hasUnitary
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    {A : Matrix m n ℝ} :
    HasUnitaryBidiagonalization A → HasOrthogonalBidiagonalization A := by
  intro hA
  rcases hA with ⟨U, V, B, hU, hV, hB, hEq⟩
  refine ⟨U, V, B, ?_, ?_, hB, ?_⟩
  · simpa [IsUnitaryMatrix, IsOrthogonalMatrix] using hU.1
  · simpa [IsUnitaryMatrix, IsOrthogonalMatrix] using hV.1
  · simpa using hEq

/-- Universe-level bidiagonalization predicate used by the rectangular driver. -/
def Bidiagonalization_P (𝕜 : Type*) [RCLike 𝕜] (x : RectUniverse 𝕜) : Prop :=
  HasUnitaryBidiagonalization x.A

/--
Strong recursive bidiagonalization predicate. On positive-column subproblems it
requires the right factor to fix the head coordinate; when the column type is
empty, it falls back to the ordinary target.
-/
def BidiagonalizationFixedRightHead_P
    (𝕜 : Type*) [RCLike 𝕜] (x : RectUniverse 𝕜) : Prop :=
  (∃ _hn : Nonempty x.κ, HasUnitaryBidiagonalizationFixedRightHead x.A) ∨ IsEmpty x.κ

def Bidiagonalization_P_sub (𝕜 : Type*) [RCLike 𝕜] (x_sub : PosRectUniverse 𝕜) :
    Prop :=
  Bidiagonalization_P 𝕜 (x_sub : RectUniverse 𝕜)

@[simp] theorem bidiagonalization_P_compat (𝕜 : Type*) [RCLike 𝕜]
    (x_sub : PosRectUniverse 𝕜) :
    Bidiagonalization_P_sub 𝕜 x_sub ↔
      Bidiagonalization_P 𝕜 (x_sub : RectUniverse 𝕜) :=
  Iff.rfl

lemma isUpperBidiagonal_zero
    [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n] :
    IsUpperBidiagonal (0 : Matrix m n 𝕜) := by
  intro i j hij
  simp

theorem finiteOrderRank_pos_of_ne_headElem
    (α : Type*) [Fintype α] [LinearOrder α] [Nonempty α]
    {i : α} (hi : i ≠ headElem (α := α)) :
    0 < finiteOrderRank α i := by
  have hlt : headElem (α := α) < i :=
    lt_of_le_of_ne (headElem_le (α := α) i) hi.symm
  dsimp [finiteOrderRank]
  exact Fintype.card_pos_iff.mpr ⟨⟨headElem (α := α), hlt⟩⟩

theorem finiteOrderRank_eq_zero_iff_headElem
    (α : Type*) [Fintype α] [LinearOrder α] [Nonempty α]
    {i : α} :
    finiteOrderRank α i = 0 ↔ i = headElem (α := α) := by
  constructor
  · intro h
    by_contra hi
    have hpos := finiteOrderRank_pos_of_ne_headElem α hi
    omega
  · intro h
    rw [h, finiteOrderRank_headElem]

/-- Zero matrices have a trivial unitary bidiagonalization. -/
theorem hasUnitaryBidiagonalization_zero
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] :
    HasUnitaryBidiagonalization (0 : Matrix m n 𝕜) := by
  refine ⟨1, 1, 0, isUnitaryMatrix_one, isUnitaryMatrix_one, ?_, ?_⟩
  · exact isUpperBidiagonal_zero
  · simp

theorem hasUnitaryBidiagonalizationFixedRightHead_zero
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    HasUnitaryBidiagonalizationFixedRightHead (0 : Matrix m n 𝕜) := by
  refine ⟨1, 1, 0, isUnitaryMatrix_one, isUnitaryMatrix_one, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = headElem (α := n)
    · simp [Matrix.one_apply, hj]
    · have hhj : headElem (α := n) ≠ j := by
        intro h
        exact hj h.symm
      simp [hj, hhj]
  · exact isUpperBidiagonal_zero
  · simp

theorem fixedRightHead_one
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    ∀ j : n, (1 : Matrix n n 𝕜) (headElem (α := n)) j =
      if j = headElem (α := n) then 1 else 0 := by
  intro j
  by_cases hj : j = headElem (α := n)
  · simp [Matrix.one_apply, hj]
  · have hhj : headElem (α := n) ≠ j := by
      intro h
      exact hj h.symm
    simp [hj, hhj]

lemma bidiagonal_matrix_eq_zero_of_isEmpty_rows
    [Fintype m] [Fintype n] [IsEmpty m] (A : Matrix m n 𝕜) :
    A = 0 := by
  ext i
  cases IsEmpty.false i

lemma bidiagonal_matrix_eq_zero_of_isEmpty_cols
    [Fintype m] [Fintype n] [IsEmpty n] (A : Matrix m n 𝕜) :
    A = 0 := by
  ext i j
  cases IsEmpty.false j

/-- Base witness for matrices with an empty row type. -/
theorem base_bidiagonalization_empty_rows
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [IsEmpty m]
    (A : Matrix m n 𝕜) :
    HasUnitaryBidiagonalization A := by
  rw [bidiagonal_matrix_eq_zero_of_isEmpty_rows A]
  exact hasUnitaryBidiagonalization_zero

/-- Base witness for matrices with an empty column type. -/
theorem base_bidiagonalization_empty_cols
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [IsEmpty n]
    (A : Matrix m n 𝕜) :
    HasUnitaryBidiagonalization A := by
  rw [bidiagonal_matrix_eq_zero_of_isEmpty_cols A]
  exact hasUnitaryBidiagonalization_zero

theorem bidiagonalization_P_of_fixedRightHead_P
    (𝕜 : Type*) [RCLike 𝕜] (x : RectUniverse 𝕜) :
    BidiagonalizationFixedRightHead_P 𝕜 x → Bidiagonalization_P 𝕜 x := by
  intro h
  rcases h with ⟨_hn, hfixed⟩ | hEmpty
  · exact hasUnitaryBidiagonalization_of_fixedRightHead hfixed
  · letI : IsEmpty x.κ := hEmpty
    exact base_bidiagonalization_empty_cols x.A

/-- Transport a bidiagonalization witness across a two-sided unitary transform. -/
theorem bidiagonalization_transport_equivalence
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (U : Matrix m m 𝕜) (V : Matrix n n 𝕜)
    (A B : Matrix m n 𝕜)
    (hU : IsUnitaryMatrix U) (hV : IsUnitaryMatrix V)
    (hB : B = Uᴴ * A * V)
    (hBi : HasUnitaryBidiagonalization B) :
    HasUnitaryBidiagonalization A := by
  rcases hBi with ⟨UB, VB, C, hUB, hVB, hC, hEqB⟩
  refine ⟨U * UB, V * VB, C, isUnitaryMatrix_mul hU hUB,
    isUnitaryMatrix_mul hV hVB, hC, ?_⟩
  calc
    A = (U * Uᴴ) * A * (V * Vᴴ) := by
      simp [hU.2, hV.2]
    _ = U * (Uᴴ * A * V) * Vᴴ := by
      simp [Matrix.mul_assoc]
    _ = U * B * Vᴴ := by
      rw [← hB]
    _ = U * (UB * C * VBᴴ) * Vᴴ := by
      rw [hEqB]
    _ = (U * UB) * C * (V * VB)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp [Matrix.mul_assoc]

theorem fixedRightHead_mul
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    {V W : Matrix n n 𝕜}
    (hV : ∀ j : n, V (headElem (α := n)) j =
      if j = headElem (α := n) then 1 else 0)
    (hW : ∀ j : n, W (headElem (α := n)) j =
      if j = headElem (α := n) then 1 else 0) :
    ∀ j : n, (V * W) (headElem (α := n)) j =
      if j = headElem (α := n) then 1 else 0 := by
  intro j
  rw [Matrix.mul_apply]
  calc
    (∑ k : n, V (headElem (α := n)) k * W k j)
        = V (headElem (α := n)) (headElem (α := n)) *
            W (headElem (α := n)) j := by
          refine Finset.sum_eq_single (headElem (α := n)) ?_ ?_
          · intro k _hk hk
            have hk' : k ≠ headElem (α := n) := by
              intro h
              exact hk h
            simp [hV k, hk']
          · intro hnot
            exact (hnot (Finset.mem_univ _)).elim
    _ = if j = headElem (α := n) then 1 else 0 := by
          simp [hV (headElem (α := n)), hW j]

/-- Transport a fixed-right-head bidiagonalization across a head-fixing right transform. -/
theorem bidiagonalization_transport_equivalence_fixedRightHead
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (U : Matrix m m 𝕜) (V : Matrix n n 𝕜)
    (A B : Matrix m n 𝕜)
    (hU : IsUnitaryMatrix U) (hV : IsUnitaryMatrix V)
    (hVhead : ∀ j : n, V (headElem (α := n)) j =
      if j = headElem (α := n) then 1 else 0)
    (hB : B = Uᴴ * A * V)
    (hBi : HasUnitaryBidiagonalizationFixedRightHead B) :
    HasUnitaryBidiagonalizationFixedRightHead A := by
  rcases hBi with ⟨UB, VB, C, hUB, hVB, hVBhead, hC, hEqB⟩
  refine ⟨U * UB, V * VB, C, isUnitaryMatrix_mul hU hUB,
    isUnitaryMatrix_mul hV hVB, ?_, hC, ?_⟩
  · exact fixedRightHead_mul hVhead hVBhead
  · calc
      A = (U * Uᴴ) * A * (V * Vᴴ) := by
        simp [hU.2, hV.2]
      _ = U * (Uᴴ * A * V) * Vᴴ := by
        simp [Matrix.mul_assoc]
      _ = U * B * Vᴴ := by
        rw [← hB]
      _ = U * (UB * C * VBᴴ) * Vᴴ := by
        rw [hEqB]
      _ = (U * UB) * C * (V * VB)ᴴ := by
        rw [Matrix.conjTranspose_mul]
        simp [Matrix.mul_assoc]

section Reindex

variable {m' n' : Type u}
variable [Fintype m] [DecidableEq m] [LinearOrder m]
variable [Fintype n] [DecidableEq n] [LinearOrder n]
variable [Fintype m'] [DecidableEq m'] [LinearOrder m']
variable [Fintype n'] [DecidableEq n'] [LinearOrder n']

omit [DecidableEq m] [DecidableEq n] [DecidableEq m'] [DecidableEq n'] in
theorem isUpperBidiagonal_reindex_strictMono
    (em : m ≃ m') (en : n ≃ n') (hem : StrictMono em) (hen : StrictMono en)
    {B : Matrix m n 𝕜} (hB : IsUpperBidiagonal B) :
    IsUpperBidiagonal (Matrix.reindex em en B) := by
  intro i j hij
  have hij' :
      finiteOrderRank n (en.symm j) < finiteOrderRank m (em.symm i) ∨
        finiteOrderRank m (em.symm i) + 1 < finiteOrderRank n (en.symm j) := by
    simpa [finiteOrderRank_equiv_symm em hem i,
      finiteOrderRank_equiv_symm en hen j] using hij
  simpa [Matrix.reindex_apply] using hB (em.symm i) (en.symm j) hij'

theorem bidiagonalization_reindex_strictMono
    (em : m ≃ m') (en : n ≃ n') (hem : StrictMono em) (hen : StrictMono en)
    {A : Matrix m n 𝕜} (hA : HasUnitaryBidiagonalization A) :
    HasUnitaryBidiagonalization (Matrix.reindex em en A) := by
  rcases hA with ⟨U, V, B, hU, hV, hB, hEq⟩
  refine ⟨Matrix.reindex em em U, Matrix.reindex en en V, Matrix.reindex em en B,
    isUnitaryMatrix_reindex em hU, isUnitaryMatrix_reindex en hV, ?_, ?_⟩
  · exact isUpperBidiagonal_reindex_strictMono em en hem hen hB
  · have hEq' := congrArg (Matrix.reindex em en) hEq
    simpa [Matrix.conjTranspose_reindex, Matrix.submatrix_mul_equiv, Matrix.mul_assoc] using hEq'

theorem bidiagonalizationFixedRightHead_reindex_strictMono
    [Nonempty n] [Nonempty n']
    (em : m ≃ m') (en : n ≃ n') (hem : StrictMono em) (hen : StrictMono en)
    {A : Matrix m n 𝕜} (hA : HasUnitaryBidiagonalizationFixedRightHead A) :
    HasUnitaryBidiagonalizationFixedRightHead (Matrix.reindex em en A) := by
  rcases hA with ⟨U, V, B, hU, hV, hVhead, hB, hEq⟩
  refine ⟨Matrix.reindex em em U, Matrix.reindex en en V, Matrix.reindex em en B,
    isUnitaryMatrix_reindex em hU, isUnitaryMatrix_reindex en hV, ?_, ?_, ?_⟩
  · intro j
    have hhead := headElem_map_strictMono en hen
    have hhead_symm : en.symm (headElem (α := n')) = headElem (α := n) := by
      apply en.injective
      simp [hhead]
    have hiff : en.symm j = headElem (α := n) ↔ j = headElem (α := n') := by
      constructor
      · intro h
        calc
          j = en (en.symm j) := by simp
          _ = headElem (α := n') := by simpa [hhead] using congrArg en h
      · intro h
        simp [h, hhead_symm]
    simpa [Matrix.reindex_apply, hhead_symm, hiff] using hVhead (en.symm j)
  · exact isUpperBidiagonal_reindex_strictMono em en hem hen hB
  · have hEq' := congrArg (Matrix.reindex em en) hEq
    simpa [Matrix.conjTranspose_reindex, Matrix.submatrix_mul_equiv, Matrix.mul_assoc] using hEq'

end Reindex

section BlockLift

variable {m n : Type u}
variable [Fintype m] [DecidableEq m] [LinearOrder m]
variable [Fintype n] [DecidableEq n] [LinearOrder n]

omit [DecidableEq m] [DecidableEq n] in
/-- A one-head block matrix is upper bidiagonal from a ready boundary and tail shape. -/
theorem isUpperBidiagonal_fromBlocks_ready
    (B₁₁ : Matrix Unit Unit 𝕜) (B₁₂ : Matrix Unit n 𝕜)
    (B₂₁ : Matrix m Unit 𝕜) (B₂₂ : Matrix m n 𝕜)
    (hcol : ∀ i : m, B₂₁ i () = 0)
    (hrow : ∀ j : n, B₁₂ () j = 0)
    (hTail : IsUpperBidiagonal B₂₂) :
    IsUpperBidiagonal
      (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
        (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)) := by
  intro i j hij
  cases hi : ofLex i with
  | inl iu =>
      cases iu
      have i_eq : i = (Sum.inlₗ () : Unit ⊕ₗ m) := by
        rw [← toLex_ofLex i, hi]
      subst i
      cases hj : ofLex j with
      | inl ju =>
          cases ju
          have j_eq : j = (Sum.inlₗ () : Unit ⊕ₗ n) := by
            rw [← toLex_ofLex j, hj]
          subst j
          have hbad : 0 < 0 ∨ 1 < 0 := by
            simp [finiteOrderRank_sumLex_inl_unit] at hij
          rcases hbad with hbad | hbad
          · exact (Nat.lt_irrefl 0 hbad).elim
          · exact (Nat.not_lt_zero 1 hbad).elim
      | inr jj =>
          have j_eq : j = (Sum.inrₗ jj : Unit ⊕ₗ n) := by
            rw [← toLex_ofLex j, hj]
          subst j
          simpa [Matrix.reindex_apply, sumToLexEquiv] using hrow jj
  | inr ii =>
      have i_eq : i = (Sum.inrₗ ii : Unit ⊕ₗ m) := by
        rw [← toLex_ofLex i, hi]
      subst i
      cases hj : ofLex j with
      | inl ju =>
          cases ju
          rw [← toLex_ofLex j, hj]
          simpa [Matrix.reindex_apply, sumToLexEquiv] using hcol ii
      | inr jj =>
          have j_eq : j = (Sum.inrₗ jj : Unit ⊕ₗ n) := by
            rw [← toLex_ofLex j, hj]
          subst j
          have hijTail :
              finiteOrderRank n jj < finiteOrderRank m ii ∨
                finiteOrderRank m ii + 1 < finiteOrderRank n jj := by
            rw [finiteOrderRank_sumLex_inr, finiteOrderRank_sumLex_inr] at hij
            omega
          simpa [Matrix.reindex_apply, sumToLexEquiv] using hTail ii jj hijTail

omit [DecidableEq m] [DecidableEq n] in
/--
A one-head block matrix is upper bidiagonal when the lower-left block is zero,
the tail is upper bidiagonal, and the head row is zero past the first tail
column.
-/
theorem isUpperBidiagonal_fromBlocks_boundary
    [Nonempty n]
    (B₁₁ : Matrix Unit Unit 𝕜) (B₁₂ : Matrix Unit n 𝕜)
    (B₂₁ : Matrix m Unit 𝕜) (B₂₂ : Matrix m n 𝕜)
    (hcol : ∀ i : m, B₂₁ i () = 0)
    (hrow : ∀ j : n, 0 < finiteOrderRank n j → B₁₂ () j = 0)
    (hTail : IsUpperBidiagonal B₂₂) :
    IsUpperBidiagonal
      (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
        (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)) := by
  intro i j hij
  cases hi : ofLex i with
  | inl iu =>
      cases iu
      have i_eq : i = (Sum.inlₗ () : Unit ⊕ₗ m) := by
        rw [← toLex_ofLex i, hi]
      subst i
      cases hj : ofLex j with
      | inl ju =>
          cases ju
          have j_eq : j = (Sum.inlₗ () : Unit ⊕ₗ n) := by
            rw [← toLex_ofLex j, hj]
          subst j
          have hbad : 0 < 0 ∨ 1 < 0 := by
            simp [finiteOrderRank_sumLex_inl_unit] at hij
          rcases hbad with hbad | hbad
          · exact (Nat.lt_irrefl 0 hbad).elim
          · exact (Nat.not_lt_zero 1 hbad).elim
      | inr jj =>
          have j_eq : j = (Sum.inrₗ jj : Unit ⊕ₗ n) := by
            rw [← toLex_ofLex j, hj]
          subst j
          have hjpos : 0 < finiteOrderRank n jj := by
            rw [finiteOrderRank_sumLex_inl_unit, finiteOrderRank_sumLex_inr] at hij
            omega
          simpa [Matrix.reindex_apply, sumToLexEquiv] using hrow jj hjpos
  | inr ii =>
      have i_eq : i = (Sum.inrₗ ii : Unit ⊕ₗ m) := by
        rw [← toLex_ofLex i, hi]
      subst i
      cases hj : ofLex j with
      | inl ju =>
          cases ju
          rw [← toLex_ofLex j, hj]
          simpa [Matrix.reindex_apply, sumToLexEquiv] using hcol ii
      | inr jj =>
          have j_eq : j = (Sum.inrₗ jj : Unit ⊕ₗ n) := by
            rw [← toLex_ofLex j, hj]
          subst j
          have hijTail :
              finiteOrderRank n jj < finiteOrderRank m ii ∨
                finiteOrderRank m ii + 1 < finiteOrderRank n jj := by
            rw [finiteOrderRank_sumLex_inr, finiteOrderRank_sumLex_inr] at hij
            omega
          simpa [Matrix.reindex_apply, sumToLexEquiv] using hTail ii jj hijTail

/-- Lift a tail bidiagonalization through a ready rectangular head-tail block. -/
theorem bidiagonalization_of_ready_blocks
    (B₁₁ : Matrix Unit Unit 𝕜) (B₁₂ : Matrix Unit n 𝕜)
    (B₂₁ : Matrix m Unit 𝕜) (B₂₂ : Matrix m n 𝕜)
    (hcol : ∀ i : m, B₂₁ i () = 0)
    (hrow : ∀ j : n, B₁₂ () j = 0)
    (hTail : HasUnitaryBidiagonalization B₂₂) :
    HasUnitaryBidiagonalization
      (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
        (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)) := by
  rcases hTail with ⟨U, V, C, hU, hV, hC, hEq⟩
  let Ublk : Matrix (Unit ⊕ₗ m) (Unit ⊕ₗ m) 𝕜 :=
    fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 U
  let Vblk : Matrix (Unit ⊕ₗ n) (Unit ⊕ₗ n) 𝕜 :=
    fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 V
  let Cparent : Matrix (Unit ⊕ₗ m) (Unit ⊕ₗ n) 𝕜 :=
    Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
      (fromBlocks B₁₁ 0 0 C : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)
  refine ⟨Ublk, Vblk, Cparent, ?_, ?_, ?_, ?_⟩
  · exact isUnitaryMatrix_blockDiag_one hU
  · exact isUnitaryMatrix_blockDiag_one hV
  · exact isUpperBidiagonal_fromBlocks_ready B₁₁ 0 0 C (by simp) (by simp) hC
  · calc
      Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
          (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)
          = Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
              (fromBlocks B₁₁ 0 0 B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) := by
            congr 1
            ext i j
            all_goals cases i <;> cases j <;> simp [hrow, hcol]
      _ = Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
              (fromBlocks B₁₁ 0 0 (U * C * Vᴴ) :
                Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) := by
            rw [hEq]
      _ = Ublk * Cparent * Vblkᴴ := by
            have hraw :
                (fromBlocks B₁₁ 0 0 (U * C * Vᴴ) :
                  Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) =
                    (fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 U :
                      Matrix (Unit ⊕ m) (Unit ⊕ m) 𝕜) *
                      (fromBlocks B₁₁ 0 0 C :
                        Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) *
                      (fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 V :
                        Matrix (Unit ⊕ n) (Unit ⊕ n) 𝕜)ᴴ := by
              ext i j
              all_goals
                cases i <;> cases j <;>
                  simp [Matrix.fromBlocks_conjTranspose, fromBlocks_multiply,
                    Matrix.mul_assoc]
            have hlex := congrArg
              (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)) hraw
            simpa [Ublk, Vblk, Cparent, Matrix.submatrix_mul_equiv,
              Matrix.conjTranspose_reindex, Matrix.mul_assoc] using hlex

/-- Boundary lift when the recursive column tail is empty. -/
theorem bidiagonalization_fixedRightHead_of_boundary_ready_blocks_empty_tail_cols
    [IsEmpty n]
    (B₁₁ : Matrix Unit Unit 𝕜) (B₁₂ : Matrix Unit n 𝕜)
    (B₂₁ : Matrix m Unit 𝕜) (B₂₂ : Matrix m n 𝕜)
    (hcol : ∀ i : m, B₂₁ i () = 0) :
    HasUnitaryBidiagonalizationFixedRightHead
      (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
        (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)) := by
  let Cparent : Matrix (Unit ⊕ₗ m) (Unit ⊕ₗ n) 𝕜 :=
    Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
      (fromBlocks B₁₁ 0 0 (0 : Matrix m n 𝕜) : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)
  refine ⟨1, 1, Cparent, isUnitaryMatrix_one, isUnitaryMatrix_one,
    fixedRightHead_one, ?_, ?_⟩
  · exact isUpperBidiagonal_fromBlocks_ready B₁₁ 0 0 0 (by simp) (by simp)
      isUpperBidiagonal_zero
  · calc
      Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
          (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)
          = Cparent := by
            dsimp [Cparent]
            congr 1
            ext i j
            rcases i with (_ | i') <;> rcases j with (_ | j')
            · simp
            · cases IsEmpty.false j'
            · simp [hcol]
            · cases IsEmpty.false j'
      _ = (1 : Matrix (Unit ⊕ₗ m) (Unit ⊕ₗ m) 𝕜) * Cparent *
            (1 : Matrix (Unit ⊕ₗ n) (Unit ⊕ₗ n) 𝕜)ᴴ := by
            simp

/--
Boundary-aware one-head lift. The parent head row may keep the first tail
column, so the recursive tail witness must have a right unitary factor fixing
the tail head coordinate.
-/
theorem bidiagonalization_of_boundary_ready_blocks
    [Nonempty n]
    (B₁₁ : Matrix Unit Unit 𝕜) (B₁₂ : Matrix Unit n 𝕜)
    (B₂₁ : Matrix m Unit 𝕜) (B₂₂ : Matrix m n 𝕜)
    (hcol : ∀ i : m, B₂₁ i () = 0)
    (hrow : ∀ j : n, 0 < finiteOrderRank n j → B₁₂ () j = 0)
    (hTail : HasUnitaryBidiagonalizationFixedRightHead B₂₂) :
    HasUnitaryBidiagonalizationFixedRightHead
      (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
        (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)) := by
  rcases hTail with ⟨U, V, C, hU, hV, hVhead, hC, hEq⟩
  let Ublk : Matrix (Unit ⊕ₗ m) (Unit ⊕ₗ m) 𝕜 :=
    fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 U
  let Vblk : Matrix (Unit ⊕ₗ n) (Unit ⊕ₗ n) 𝕜 :=
    fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 V
  let C₁₂ : Matrix Unit n 𝕜 := B₁₂ * V
  let Cparent : Matrix (Unit ⊕ₗ m) (Unit ⊕ₗ n) 𝕜 :=
    Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
      (fromBlocks B₁₁ C₁₂ 0 C : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)
  have hC₁₂ : ∀ j : n, 0 < finiteOrderRank n j → C₁₂ () j = 0 := by
    intro j hj
    change (B₁₂ * V) () j = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero ?_
    intro k _hk
    by_cases hk : k = headElem (α := n)
    · subst k
      have hv : V (headElem (α := n)) j = 0 := by
        have hj_ne : j ≠ headElem (α := n) :=
          ne_headElem_of_finiteOrderRank_pos n hj
        simpa [hj_ne] using hVhead j
      simp [hv]
    · have hkpos : 0 < finiteOrderRank n k :=
        finiteOrderRank_pos_of_ne_headElem n hk
      simp [hrow k hkpos]
  refine ⟨Ublk, Vblk, Cparent, ?_, ?_, ?_, ?_, ?_⟩
  · exact isUnitaryMatrix_blockDiag_one hU
  · exact isUnitaryMatrix_blockDiag_one hV
  · intro j
    change Vblk (headElem (α := Unit ⊕ₗ n)) j =
      if j = headElem (α := Unit ⊕ₗ n) then 1 else 0
    rw [headElem_sumLex_unit]
    cases hj : ofLex j with
    | inl ju =>
        cases ju
        have j_eq : j = (Sum.inlₗ () : Unit ⊕ₗ n) := by
          rw [← toLex_ofLex j, hj]
        subst j
        change (fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 V :
          Matrix (Unit ⊕ n) (Unit ⊕ n) 𝕜) (Sum.inl ()) (Sum.inl ()) = 1
        simp
    | inr jj =>
        have j_eq : j = (Sum.inrₗ jj : Unit ⊕ₗ n) := by
          rw [← toLex_ofLex j, hj]
        subst j
        have hne : (Sum.inrₗ jj : Unit ⊕ₗ n) ≠ (Sum.inlₗ () : Unit ⊕ₗ n) := by
          intro h
          cases h
        change (fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 V :
          Matrix (Unit ⊕ n) (Unit ⊕ n) 𝕜) (Sum.inl ()) (Sum.inr jj) =
            if (Sum.inrₗ jj : Unit ⊕ₗ n) = Sum.inlₗ () then 1 else 0
        simp [hne]
  · exact isUpperBidiagonal_fromBlocks_boundary B₁₁ C₁₂ 0 C (by simp) hC₁₂ hC
  · calc
      Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
          (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜)
          = Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
              (fromBlocks B₁₁ B₁₂ 0 B₂₂ : Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) := by
            congr 1
            ext i j
            all_goals cases i <;> cases j <;> simp [hcol]
      _ = Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)
              (fromBlocks B₁₁ B₁₂ 0 (U * C * Vᴴ) :
                Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) := by
            rw [hEq]
      _ = Ublk * Cparent * Vblkᴴ := by
            have hraw :
                (fromBlocks B₁₁ B₁₂ 0 (U * C * Vᴴ) :
                  Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) =
                    (fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 U :
                      Matrix (Unit ⊕ m) (Unit ⊕ m) 𝕜) *
                      (fromBlocks B₁₁ C₁₂ 0 C :
                        Matrix (Unit ⊕ m) (Unit ⊕ n) 𝕜) *
                      (fromBlocks (1 : Matrix Unit Unit 𝕜) 0 0 V :
                        Matrix (Unit ⊕ n) (Unit ⊕ n) 𝕜)ᴴ := by
              ext i j
              all_goals
                cases i <;> cases j <;>
                  simp [C₁₂, Matrix.fromBlocks_conjTranspose, fromBlocks_multiply,
                    Matrix.mul_assoc, hV.2]
            have hlex := congrArg
              (Matrix.reindex (sumToLexEquiv Unit m) (sumToLexEquiv Unit n)) hraw
            simpa [Ublk, Vblk, Cparent, Matrix.submatrix_mul_equiv,
              Matrix.conjTranspose_reindex, Matrix.mul_assoc] using hlex


end BlockLift

end MatDecompFormal.Instances
