import Mathlib
import MatDecompFormal.ref.Basic

open Nat Matrix Classical

section aux
--补充些 Mathlib的api
@[inline] def Fin.natSub {n} (m) (i : Fin (n + m)) (h : n ≤ i) : Fin m :=
  ⟨i - n,  Nat.sub_lt_left_of_lt_add h i.2⟩

lemma finSumFinEquiv_symm_apply_right {n o} {i : Fin (n + o)} (hi : n ≤ i) :
  (finSumFinEquiv.symm i) = Sum.inr (Fin.natSub o i hi) := by
    simp [finSumFinEquiv, Fin.natSub, Fin.addCases, Nat.not_lt.mpr hi, Fin.subNat]

lemma finSumFinEquiv_symm_apply_left {n o}
   {i : Fin (n + o)} (hi : i < n) : finSumFinEquiv.symm i = Sum.inl ⟨i, hi⟩ := by
  simp [finSumFinEquiv, Fin.addCases, hi, Fin.castLT]

lemma find_pivot_col {α n} [NeZero n] [Zero α] {M : Fin n → α} (h : M ≠ 0) :
  ∃ i : Fin n, M i ≠ 0 := by
  by_contra! ha
  apply h
  funext i
  apply ha

lemma WithTop.map_lt_of_lt {α β : Type*} {x y : WithTop α} [LT α] [LT β] (h : α → β)
    (hh : ∀ x y, x < y → h x < h y) (hxy : x < y) :
    WithTop.map h x < WithTop.map h y := by
  rw [lt_def] at *
  have ⟨a, ⟨ha, hb⟩⟩ := hxy
  use h a
  simp only [ha, map_coe, true_and]
  intro b hbm
  rw [map_eq_some_iff] at hbm
  have ⟨b', ⟨hby, hb'⟩⟩ := hbm
  rw [← hb']
  apply hh _ _ (hb _ hby)

lemma WithTop.equiv_lt {α β : Type*} {x y : WithTop α}
  [PartialOrder α] [PartialOrder β] (h : α ≃o β) (hxy : x < y) :
  WithTop.map h x < WithTop.map h y := by
  simpa only [← OrderIso.withTopCongr_apply, OrderIso.lt_iff_lt]

/--
Given invertible matrices `x ∈ GL l R` and `y ∈ GL o R`, constructs their direct sum
as an invertible block-diagonal matrix in `GL (l ⊕ o) R`.

This is the group homomorphism sending `(x, y)` to `[x 0; 0 y]`.
-/
noncomputable def Matrix.GeneralLinearGroup.glDirectSum {R} {l o} [CommRing R]
    [Fintype l] [DecidableEq l] [Fintype o] [DecidableEq o]
    (x : GL l R) (y : GL o R) : GL (l ⊕ o) R where
  val:= fromBlocks x.1 0 0 y.1
  inv:= fromBlocks x.2 0 0 y.2
  val_inv:= by simp [fromBlocks_multiply]
  inv_val:= by simp [fromBlocks_multiply]

lemma matrix_mul_distrib_submatrix_fromBlocks_zero_top [AddCommMonoid F] [Mul F] [Fintype r]
  [Fintype l] [Fintype o]
  (P : Matrix l l F) (a : Matrix l r F) (b : Matrix l o F)
  (f : s → r ⊕ o) :
  P * ((fromBlocks 0 0 a b : Matrix ((Fin 0) ⊕ l) (r ⊕ o) F).submatrix Sum.inr f)  =
  (fromBlocks 0 0 (P * a) (P * b) : Matrix ((Fin 0) ⊕ l) (r ⊕ o) F ).submatrix Sum.inr f := by
  funext i j
  simp only [submatrix_apply]
  match hf : f j with
  | Sum.inl k => simp [HMul.hMul, hf];
  | Sum.inr k => simp [HMul.hMul, hf];

end aux

namespace Matrix

variable {l m n o p α R : Type*}
/-- Associativity of matrix multiplication in a particular nested form. -/
theorem mul_assoc_nested [NonUnitalSemiring α]
  [Fintype m] [Fintype n] [Fintype o]
  (a : Matrix l m α) (b : Matrix m n α)
  (c : Matrix n o α) (d : Matrix o p α) :
    (a * b) * (c * d) = a * (b * c) * d := by
  simp only [Matrix.mul_assoc]

/-- Multiplication of a 1x1 matrix with a 1×n matrix is a scalar multiplication. -/
lemma one_one_mul_one_n [Mul R] [AddCommMonoid R] (a : Matrix (Fin 1) (Fin 1) R) (b : Matrix (Fin 1) m R) :
    a * b = (a 0 0) • b := by
  funext i j
  simp only [HMul.hMul, dotProduct, Finset.univ_unique, Fin.fin_one_eq_zero, Fin.isValue,
    Finset.sum_const, Finset.card_singleton, one_smul, smul_apply, smul_eq_mul]


/-- Multiplication of a m×1 matrix with a 1×1 matrix is a scalar multiplication. -/
lemma m_one_mul_one_one [Mul R] [AddCommMonoid R] (a : Matrix (Fin 1) (Fin 1) R)
    (b : Matrix m (Fin 1) R) : b * a = MulOpposite.op (a 0 0) • b := by
  funext i j
  simp only [HMul.hMul, dotProduct, Finset.univ_unique, Fin.fin_one_eq_zero, Fin.isValue,
    Finset.sum_const, Finset.card_singleton, one_smul, smul_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]

/--
Given a matrix `a` with a single column (of type `Matrix m (Fin 1) R`) and a vector `b` of length 1,
the matrix-vector product `a *ᵥ b` simplifies to scaling the single column of `a` by `b 0`.

This shows that matrix-vector multiplication with a single-column matrix is equivalent to
scalar multiplication of that column by the single element of the vector.

* `a : Matrix m (Fin 1) R` - a matrix with a single column (indexed by `Fin 1`)
* `b : Fin 1 → R` - a vector of length 1 (effectively a scalar)
-/
lemma single_column_matrix_mulVec_scalar [Mul R] [CommSemiring R] (a : Matrix m (Fin 1) R)
    (b : Fin 1 → R) : a *ᵥ b = ((b 0) • (fun j ↦ a j 0)) := by
  funext i
  simp only [mulVec, dotProduct, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Pi.smul_apply, smul_eq_mul, mul_comm]

/--
Given vectors `a` and `b`, the matrix-vector product of the row matrix formed by `a`
with the vector `b` equals a constant function whose value is the dot product of `a` and `b`.

This shows that multiplying a single-row matrix (represented as `of fun (_ : Fin 1) j ↦ a j`)
by a vector `b` is equivalent to taking their dot product and creating a constant vector.

* `a : m → R` - the vector used to form the row matrix
* `b : m → R` - the vector to multiply with
-/
lemma row_matrix_mulVec_dotProduct [Fintype m] [NonUnitalNonAssocSemiring R] (a : m → R)
    (b : m → R) : (of fun (_ : Fin 1) j ↦ a j) *ᵥ b = (fun _ => a ⬝ᵥ b) := by
  funext i
  simp only [mulVec, of_apply]

theorem col_zero_mulVec_eq {n m p R} [NeZero p] [NonUnitalNonAssocSemiring R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin p) R) :
    A *ᵥ (fun i ↦ B i 0) = fun i ↦ (A * B) i 0 := rfl

theorem col_zero_mulVec_apply_eq {n m p R} [NeZero p] [NonUnitalNonAssocSemiring R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin p) R) (j : Fin m) :
    (A *ᵥ (fun i ↦ B i 0)) j = (A * B) j 0 := rfl

end Matrix

section vecMulVec

variable {m R : Type*}

/-- The outer product of two vectors can be expressed as matrix multiplication. -/
lemma vecMulVec_eq_mul [Mul R] [AddCommMonoid R] (a b : m → R) :
    vecMulVec a b = (of fun j (_ : Fin 1) ↦ a j) * (of fun (_ : Fin 1) i ↦ b i) := by
  funext i j
  simp [vecMulVec, HMul.hMul, dotProduct]

/--
Outer product followed by matrix-vector multiplication simplifies to a scaled vector:
`(a ⊗ b) * c = (b · c) • a` where `⊗` is outer product and `·` is dot product.
-/
lemma vecMulVec_mulVec_eq_dotProduct_smul [CommSemiring R] [Fintype m]
    (a b c : m → R) :
    (vecMulVec a b) *ᵥ c = (b ⬝ᵥ c) • a := by
  simp only [vecMulVec_eq_mul, ← mulVec_mulVec, row_matrix_mulVec_dotProduct,
    single_column_matrix_mulVec_scalar, Fin.isValue, of_apply]

/-- The dot product of two vectors can be obtained from their matrix product representation. -/
lemma dot_product_as_matrix_mul [Fintype m] [Mul R] [AddCommMonoid R] (b c : m → R) :
  ((of fun (_ : Fin 1) i ↦ b i) * (of fun j (_ : Fin 1) ↦ c j)) 0 0 = (b ⬝ᵥ c) := by
  simp only [HMul.hMul, Fin.isValue, of_apply]

/-- The product of two outer products can be expressed as a scalar multiple of another outer product. -/
lemma vecMulVec_mul_vecMulVec [Fintype m] [CommSemiring R] (a b c d : m → R) :
    vecMulVec a b * vecMulVec c d = (b ⬝ᵥ c) • (vecMulVec a d):= by
  simp only [vecMulVec_eq_mul, mul_assoc_nested, m_one_mul_one_one, Fin.isValue,
    dot_product_as_matrix_mul, op_smul_eq_smul, smul_mul]

end vecMulVec

section GaussianEliminator

variable {R F : Type*}
variable {n : ℕ}
/--
`gaussTrans k l` ― *column* Gauss transformation
`E[k; l] = I  -  l • eₖᵀ`

* `k : Fin n` — 选定的主元列索引
* `l : Fin n → R` — 每一行使用的消元系数，
  要求 *typically* 在 `i < k` 时为 `0`，以保证 “只消去行 `> k` 的元素”。

矩阵乘法 `E[k; l] ⬝ A` 的效果：
将矩阵 `A` 的 **第 k 列** 作为基准，
把 `l i` 倍的该列减到第 `i` 行，
从而把 `A i k`（`i > k`）化为 `0`。
-/
def gaussTrans [CommRing R] (k : Fin n) (l : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  1 - vecMulVec l (Pi.single k 1)

def gaussTransGL [CommRing R] (k : Fin n) (l : Fin n → R) (hl : l k = 0) : GL (Fin n) R where
  val := gaussTrans k l
  inv := 1 + vecMulVec l (Pi.single k 1)
  val_inv := by
    simp only [gaussTrans, mul_add, mul_one, sub_mul, one_mul, _root_.vecMulVec_mul_vecMulVec,
      single_dotProduct, hl, mul_zero, zero_smul, sub_zero, sub_add_cancel]
  inv_val := by
    simp only [gaussTrans, mul_sub, mul_one, add_mul, one_mul, _root_.vecMulVec_mul_vecMulVec,
      single_dotProduct, hl, mul_zero, zero_smul, add_zero, add_sub_cancel_right]


/-- 方便的记号：`E[k; l]` -/
notation "E[" k "; " l "]" => gaussTrans k l

/--
A structure representing a Gaussian elimination vector for position `k`.
The vector `l` satisfies `l i = 0` for all indices `i ≤ k`.
This is used in Gaussian elimination to create zero entries above the pivot.
-/
structure GaussianVec (R) [Zero R] (k : Fin n) where
  l : Fin n → R
  hl : ∀ i, i ≤ k → l i = 0

/--
Creates a Gaussian elimination vector for position `k` from vector `x`.
For indices `i ≤ k`, sets `l i = 0` (creating zeros above the pivot).
For indices `i > k`, sets `l i = x i / x k` (normalizing by the pivot element).
-/
instance GaussianVecElim [Field F] (k : Fin n) (x : Fin n → F) : GaussianVec F k :=
  ⟨ fun i ↦ if i ≤ k then 0 else x i / x k ,
    fun _ hi ↦ by simp [hi]⟩

/--
The key property of Gaussian elimination: multiplying the elimination vector `l`
by the original vector `x` produces zeros above the pivot position `k`.
Here `E[k; l]` represents the elementary matrix constructed from vector `l` at row `k`.
-/
theorem gaussElim_zero_above [Field F] {k : Fin n} {x : Fin n → F} (hx : x k ≠ 0) :
    ∀ i, i > k → (E[k;(GaussianVecElim k x).l] *ᵥ x) i = 0 := by
  intro i hi
  field_simp [gaussTrans, sub_mulVec, vecMulVec_mulVec_eq_dotProduct_smul,
     GaussianVecElim, Fin.not_le.mpr hi]


lemma gaussElim_zero_of_zero {m n} [NeZero m] [NeZero n] [Field F]
  {A : Matrix (Fin m) (Fin n) F} : (GaussianVecElim 0 fun i ↦ A i 0).l 0 = 0 := by
  simp [GaussianVecElim]


open MatrixSlice MatrixRel

section PivotGaussElim

section feasible

variable [Zero F]
/--
矩阵大小合法
-/
@[mk_iff] class MatNonEmpty (x : MatObj F) : Prop where
  (hμ : x.μ > 0)

/--
矩阵大小合法，第一列不都为0
-/
@[mk_iff] class MatFirstColNonZero (x : MatObj F) extends MatNonEmpty x where
  (hA : (fun i ↦ x.A i ⟨0, Nat.pos_of_mul_pos_left hμ⟩) ≠ 0)

/--
矩阵大小合法，左上角不为0
-/
class MatPivotNonZero (x : MatObj F) extends MatNonEmpty x where
  (hA : x.A ⟨0, Nat.pos_of_mul_pos_right hμ⟩ ⟨0, Nat.pos_of_mul_pos_left hμ⟩ ≠ 0)

instance {x : MatObj F} (hμ : x.μ > 0) : NeZero x.n :=
  ⟨Nat.pos_iff_ne_zero.mp <| Nat.pos_of_mul_pos_left hμ⟩

instance {x : MatObj F} (hμ : x.μ > 0) : NeZero x.m :=
   ⟨Nat.pos_iff_ne_zero.mp <| Nat.pos_of_mul_pos_right hμ⟩

instance {x : { x : MatObj F // MatNonEmpty x}} : NeZero x.1.n :=
  instNeZeroNatNOfGtμOfNat x.2.hμ

instance {x : { x : MatObj F // MatNonEmpty x}} : NeZero x.1.m :=
  instNeZeroNatMOfGtμOfNat x.2.hμ

instance {x : { x : MatObj F // MatPivotNonZero x}} : NeZero x.1.n :=
  instNeZeroNatNOfGtμOfNat x.2.hμ

instance {x : { x : MatObj F // MatPivotNonZero x}} : NeZero x.1.m :=
  instNeZeroNatMOfGtμOfNat x.2.hμ

instance {x : { x : MatObj F // MatFirstColNonZero x}} : NeZero x.1.n :=
  instNeZeroNatNOfGtμOfNat x.2.hμ

instance {x : { x : MatObj F // MatFirstColNonZero x}} : NeZero x.1.m :=
  instNeZeroNatMOfGtμOfNat x.2.hμ

lemma MatNonEmpty_eq (R) [Zero R] : MatNonEmpty = (fun (x : MatObj R) ↦ x.μ > 0) := by
  ext i
  simp only [matNonEmpty_iff, gt_iff_lt]

end feasible

def gaussColElimOpWithoutPivot [Field F] :
    ElimOp (X := MatObj F) IsRowEquiv S_col1Ready MatPivotNonZero where
  E x := ⟨x.1.m, x.1.n, E[0;(GaussianVecElim 0 (fun i ↦ x.1.A i 0)).l] * x.1.A⟩
  hS x :=
    ⟨inferInstance, inferInstance, by
    simp only [gt_iff_lt, Fin.val_pos_iff]
    exact gaussElim_zero_above x.2.2⟩
  hr x := {
    h := ⟨rfl, rfl⟩
    hP := ⟨(gaussTransGL 0 (GaussianVecElim 0 (fun i ↦ x.1.A i 0)).l) gaussElim_zero_of_zero,
        by simp [gaussTransGL, MatObj.SameSize.reindex]⟩
  }

section Pivot

open Equiv.Perm Equiv

noncomputable def gaussColPivotElimOp [Field F] :
    ElimOp (X := MatObj F) IsRowEquiv MatNonEmpty MatFirstColNonZero where
  E x := ⟨x.1.m, x.1.n, (swap F 0 (find_pivot_col x.2.hA).choose) * x.1.A⟩
  hS x := ⟨x.2.hμ⟩
  hr x := {
    h := ⟨rfl, rfl⟩
    hP :=
    ⟨(GeneralLinearGroup.swap F 0 (find_pivot_col x.2.hA).choose), by simp [MatObj.SameSize.reindex]⟩
  }

lemma gaussColPivot_pivot_nonzero [Field F] :
  ∀ (x : { x : MatObj F // MatFirstColNonZero x }),
  MatPivotNonZero (gaussColPivotElimOp.E x) := by
  intro a
  exact {
    toMatNonEmpty := gaussColPivotElimOp.hS _ ,
    hA := by simpa only [gaussColPivotElimOp, Fin.mk_zero', swap_mul_apply_left]
    using (gaussColPivotElimOp._proof_3 a).choose_spec
  }

noncomputable def gaussColElimOpNonZero [Field F] :
    ElimOp (X := MatObj F) IsRowEquiv S_col1Ready MatFirstColNonZero :=
    ElimOp.compOnImage gaussColPivotElimOp gaussColElimOpWithoutPivot gaussColPivot_pivot_nonzero
  {trans := @MatrixRel.IsRowEquiv.trans F _ }

lemma nonempty_not_firstColNonZero_implies_col1Ready [Zero F] (x : MatObj F) (he : MatNonEmpty x)
  (hz : ¬MatFirstColNonZero x) : S_col1Ready x := by
  simp only [matFirstColNonZero_iff, ne_eq, not_exists, Decidable.not_not] at hz
  refine ⟨instNeZeroNatMOfGtμOfNat he.1,
          instNeZeroNatNOfGtμOfNat he.1,?_⟩
  intro i hi
  show (fun i ↦ x.A i ⟨0, _⟩) i = 0
  rw [hz he]
  rfl

noncomputable def gaussColElimOp (F) [Field F] :
    ElimOp (X := MatObj F) IsRowEquiv S_col1Ready MatNonEmpty :=
  ElimOp.promote gaussColElimOpNonZero nonempty_not_firstColNonZero_implies_col1Ready (fun x _ => MatrixRel.IsRowEquiv.refl x)

end Pivot

end PivotGaussElim

section

section Matrix.IsRowEchelon

open List

variable {m n : ℕ}
variable {α} [DecidableEq α] [Zero α] (M : Matrix (Fin n) (Fin m) α)

def Matrix.NonZeroIndex : Fin n → WithTop (Fin m) := fun i ↦
    Fin.find (fun j => M i j ≠ 0)

namespace Matrix.NonZeroIndex

lemma eq_top {i} : (M.NonZeroIndex i = ⊤) ↔ ∀ j, M i j = 0 := by
  show (M.NonZeroIndex i = none) ↔ ∀ j, M i j = 0
  simp [NonZeroIndex]
  rw [Fin.find_eq_none_iff]
  simp

lemma ne_top_iff (i) : M.NonZeroIndex i ≠ ⊤ ↔
  ∃ j, M.NonZeroIndex i = some j := by
  show M.NonZeroIndex i ≠ none ↔ _
  rw [Option.ne_none_iff_exists']

lemma ne_top_iff' (i) : M.NonZeroIndex i ≠ ⊤ ↔
  ∃ j, M.NonZeroIndex i = WithTop.some j := by
  show M.NonZeroIndex i ≠ none ↔ ∃ j, M.NonZeroIndex i = some j
  rw [Option.ne_none_iff_exists']

lemma eq_some_iff (i j) : M.NonZeroIndex i = some j ↔ (∀ k < j, M i k = 0) ∧ M i j ≠ 0:= by
  rw [NonZeroIndex, Fin.find_eq_some_iff]
  constructor
  · intro hx
    refine ⟨?_, hx.1⟩
    by_contra!
    rcases this with ⟨k, hk, hm⟩
    exact Nat.lt_le_asymm hk (hx.2 k hm)
  intro hx
  refine ⟨hx.2, ?_⟩
  by_contra!
  rcases this with ⟨k, hk, hm⟩
  exact hk (hx.1 k hm)

lemma eq_some_iff' (i j) : M.NonZeroIndex i = WithTop.some j ↔ (∀ k < j, M i k = 0) ∧ M i j ≠ 0:= by
  show M.NonZeroIndex i = some j ↔ (∀ k < j, M i k = 0) ∧ M i j ≠ 0
  rw [eq_some_iff]

variable {l o p q}

/--
Auxiliary lemma for `submatrix_nonZeroIndex_map` handling the case where
the submatrix has a non-zero index equal to `⊤` (all zeros in the row).
-/
lemma submatrix_nonZeroIndex_map_top_case {s t} [DecidableEq R] [Zero R]
    (A : Matrix l o R) (f : Fin m → l) (g : Fin n → o) (i : Fin m)
    (p : Fin s → l) (q : Fin t → o) (uh : Fin m → Prop) (hi : uh i)
    (u : {x : Fin m // uh x} → Fin s) (h : Fin t → Fin n)
    (hjk : (∀ (j : Fin t), A (p (u ⟨i, hi⟩)) (q j) = 0) → ∀ (j : Fin n), A (p (u ⟨i, hi⟩)) (g j) = 0)
    (hpq : (A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩) = ⊤)
    (hpu : p (u ⟨i, hi⟩) = f i) :
    (A.submatrix f g).NonZeroIndex i = WithTop.map h ((A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩)) := by
  simp [hpq]
  simp [eq_top] at *
  rw [← hpu]
  apply hjk hpq

lemma submatrix_nonZeroIndex_map_finite_case {s t} [DecidableEq R] [Zero R]
    (A : Matrix l o R) (f : Fin m → l) (g : Fin n → o) (i : Fin m)
    (p : Fin s → l) (q : Fin t → o) (uh : Fin m → Prop) (hi : uh i)
    (u : {x : Fin m // uh x} → Fin s) (h : Fin t → Fin n)
    (hpq : (A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩) ≠ ⊤)
    (hkj : (j : Fin t) → (∀ k < j, A (p (u ⟨i, hi⟩)) (q k) = 0) → ∀ k < h j, A (p (u ⟨i, hi⟩)) (g k) = 0)
    (hpu : p (u ⟨i, hi⟩) = f i) (hgh : g ∘ h = q) :
    (A.submatrix f g).NonZeroIndex i = WithTop.map h ((A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩)) := by
  change _ ≠ ⊤ at hpq
  rw [ne_top_iff] at hpq
  rcases hpq with ⟨j, hj⟩
  simp only [hj]
  show _ = some (h j)
  rw [eq_some_iff] at *
  refine ⟨?_, ?_⟩
  · simp only [← hpu, submatrix_apply]
    simp at hj
    apply hkj j hj.1
  simp only [← hpu, submatrix_apply]
  simp at hj
  show A ((p ∘ u) ⟨i, hi⟩) ((g ∘ h) j) ≠ 0
  rw [hgh]
  apply hj.2

/--
Main theorem relating non-zero indices of submatrices under index mapping.

Given a matrix `A`, index mappings `f, g, p, q, u, h` with appropriate conditions,
shows that the non-zero index of the submatrix `A.submatrix f g` at row `i`
is obtained by mapping the non-zero index of `A.submatrix p q` at row `u ⟨i, hi⟩`
through the function `h`.

This handles both cases (⊤ and finite indices) by delegating to auxiliary lemmas.
-/
lemma submatrix_nonZeroIndex_map {s t} [DecidableEq R] [Zero R] (A : Matrix l o R) (f : Fin m → l)
    (g : Fin n → o) (i : Fin m)
    (p : Fin s → l) (q : Fin t → o) (uh : Fin m → Prop) (hi : uh i)
    (u : {x : Fin m // uh x} → Fin s) (h : Fin t → Fin n)
    (hjk : (∀ (j : Fin t), A (p (u ⟨i, hi⟩)) (q j) = 0) → ∀ (j : Fin n), A (p (u ⟨i, hi⟩)) (g j) = 0)
    (hkj : (j : Fin t) → (∀ k < j, A (p (u ⟨i, hi⟩)) (q k) = 0) → ∀ k < h j, A (p (u ⟨i, hi⟩)) (g k) = 0)
    (hpu : p (u ⟨i, hi⟩) = f i) (hgh : g ∘ h = q) :
    (A.submatrix f g).NonZeroIndex i = WithTop.map h ((A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩)) := by
  by_cases hpq : (A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩) = ⊤
  · exact submatrix_nonZeroIndex_map_top_case A f g i p q uh hi u h hjk hpq hpu
  exact submatrix_nonZeroIndex_map_finite_case A f g i p q uh hi u h hpq hkj hpu hgh

/--
Simplified version of `submatrix_nonZeroIndex_map` where the predicate `uh`
is trivial (always true), making the index mapping `u` simpler to use.
-/
lemma submatrix_nonZeroIndex_map_simple {s t} [DecidableEq R] [Zero R] (A : Matrix l o R)
    (f : Fin m → l) (g : Fin n → o) (i : Fin m)
    (p : Fin s → l) (q : Fin t → o)
    (u : Fin m → Fin s) (h : Fin t → Fin n)
    (hjk : (∀ (j : Fin t), A (p (u i)) (q j) = 0) → ∀ (j : Fin n), A (p (u i)) (g j) = 0)
    (hkj : (j : Fin t) → (∀ k < j, A (p (u i)) (q k) = 0) → ∀ k < h j, A (p (u i)) (g k) = 0)
    (hpu : p (u i) = f i) (hgh : g ∘ h = q) :
    (A.submatrix f g).NonZeroIndex i = WithTop.map h ((A.submatrix p q).NonZeroIndex (u i)) := by
  apply submatrix_nonZeroIndex_map A f  g i p q  (fun _ ↦ True) (by simp) (fun x ↦ ⟨u x, by simp⟩) h hjk hkj hpu hgh

lemma submatrix_nonZeroIndex_map_simple_fin {s t} [DecidableEq R] [Zero R]
    (A : Matrix (Fin s) (Fin t) R) (f : Fin m ≃ Fin s) (g : Fin n ≃ Fin t) (i : Fin m)
    (hg : ∀ x y, x < y → g x < g y) :
    (A.submatrix f g).NonZeroIndex i = WithTop.map g.2 (A.NonZeroIndex (f i)) := by
    apply submatrix_nonZeroIndex_map_simple
    · intro hj j
      apply hj (g j)
    · intro j hkj k hk
      apply hkj
      rw [← g.4 j]
      apply hg _ _ hk
    · rfl
    · funext
      simp

lemma fromBlocks_reindex_nonZeroIndex_left {i : Fin (n + o)} (A : Matrix (Fin n) (Fin l) α)
    (B : Matrix (Fin n) (Fin m) α) (C : Matrix (Fin o) (Fin l) α)
    (D : Matrix (Fin o) (Fin m) α) (hi : i < n)
    (ha : A.NonZeroIndex ⟨i, hi⟩ ≠ ⊤) :
    ((fromBlocks A B C D).reindex finSumFinEquiv finSumFinEquiv).NonZeroIndex i =
    WithTop.map (Fin.castAdd m) (A.NonZeroIndex ⟨i, hi⟩) := by
    apply submatrix_nonZeroIndex_map_finite_case  (fromBlocks A B C D) finSumFinEquiv.symm finSumFinEquiv.symm i Sum.inl Sum.inl (fun j ↦ j < n) hi (fun j ↦ ⟨j.1, j.2⟩)
    · simp only [submatrix, fromBlocks_apply₁₁]
      show A.NonZeroIndex _ ≠ ⊤
      apply ha
    · intro j hkj k hk
      have hk' : k.1 < l := by
        rw [← Fin.val_fin_lt] at hk
        apply lt_trans hk
        simp only [Fin.coe_castAdd, Fin.is_lt]
      simp [finSumFinEquiv_symm_apply_left hk', fromBlocks_apply₁₁]
      apply hkj _   hk
    · simp [finSumFinEquiv, Fin.addCases, hi, Fin.castLT]
    · funext i
      simp

lemma fromBlocks_lowerTriangular_reindex_nonZeroIndex {i : Fin (n + o)} (A : Matrix (Fin n) (Fin l) α)
    (B : Matrix (Fin n) (Fin m) α) (D : Matrix (Fin o) (Fin m) α)
    (hi : n ≤ i) : ((fromBlocks A B 0 D).reindex finSumFinEquiv finSumFinEquiv).NonZeroIndex i =
    WithTop.map (Fin.natAdd l) (D.NonZeroIndex (Fin.natSub o i hi)) := by
    apply submatrix_nonZeroIndex_map (fromBlocks A B 0 D) finSumFinEquiv.symm finSumFinEquiv.symm i Sum.inr Sum.inr
      (fun j ↦ n ≤ j) hi (fun j ↦ (Fin.natSub o j.1 j.2)) (Fin.natAdd l)
    · intro hj j
      match (finSumFinEquiv.symm j) with
      | Sum.inr u => simp only [hj]
      | Sum.inl v => simp only [fromBlocks_apply₂₁, zero_apply]
    · intro j hj k hk
      match hkf : (finSumFinEquiv.symm k) with
      | Sum.inr u =>
        simp at *
        apply hj
        simp [finSumFinEquiv, Fin.addCases] at hkf
        by_cases hkl : k < l
        · simp [hkl] at hkf
        simp [hkl, Fin.subNat] at hkf
        simpa [← hkf] using Fin.mk_lt_of_lt_val <| Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hkl) hk
      | Sum.inl v => simp only [fromBlocks_apply₂₁, zero_apply]
    · have : ¬ n > i := Nat.not_lt.mpr hi
      simp [finSumFinEquiv, Fin.addCases, this, Fin.natSub, Fin.subNat]
    · funext i
      simp only [Function.comp_apply, finSumFinEquiv_symm_apply_natAdd]

lemma preserved_under_injective_columns {r j}
  {A : Matrix (Fin m) (Fin n) α} (f : Fin r → Fin m) (g : Fin o ≃ Fin n)
  (hg : ∀ x y, x < y → g.2 x < g.2 y) (hA : (A.submatrix f g.1).NonZeroIndex j ≠ ⊤) :
  A.NonZeroIndex (f j) ≠ ⊤ := by
  simp [ne_top_iff', eq_some_iff'] at *
  rcases hA with ⟨w, hw⟩
  use (g w)
  refine ⟨?_, hw.2⟩
  intro k hk
  have : g.invFun k < w := by
    rw [← g.3 w]
    apply hg _ _ hk
  have := (hw.1 (g.2 k) this )
  simp at this
  apply this

end Matrix.NonZeroIndex

open Matrix.NonZeroIndex

@[class, mk_iff]
structure Matrix.IsRowEchelon : Prop where
  pivot_right_move :
    ∀ (i j), i < j → M.NonZeroIndex j ≠ ⊤ → M.NonZeroIndex i < M.NonZeroIndex j

lemma Matrix.IsRowEchelon.lt_of_lt (i j : Fin n) (u v : Fin m)
    (hi : M.NonZeroIndex i = WithTop.some u) (hj : M.NonZeroIndex j = WithTop.some v)
    (huv : u < v) :
    M.NonZeroIndex i < M.NonZeroIndex j := by
  simpa [hi, hj]

def Matrix.IsRowEchelonable [CommRing R]
  (x : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ P : GL (Fin m) R , (P.1 * x).IsRowEchelon

def MatObj.IsRowEchelonable [CommRing R] (x : MatObj R) : Prop :=
  x.A.IsRowEchelonable

lemma submatrix_eq {m' n'} [Zero R] (x : Matrix (Fin m) (Fin n) R)
  (hm : m' = m) (hn : n' = n) (i : Fin m') :
  WithTop.map (finCongr hn.symm) (x.NonZeroIndex ((finCongr hm) i)) =
    (x.submatrix (finCongr hm) (finCongr hn)).NonZeroIndex i := by
  by_cases h : x.NonZeroIndex ((finCongr hm) i) = ⊤
  · simp_rw [h, WithTop.map_top]
    rw [eq_top] at h
    symm
    rw [eq_top]
    intro j
    apply h ((finCongr hn) j)
  have : x.NonZeroIndex ((finCongr hm) i) ≠ ⊤ := h
  rw [ne_top_iff] at this
  rcases this with ⟨j, hj⟩
  simp_rw [hj, WithTop.map, Option.map]
  rw [eq_some_iff] at hj
  symm
  simp_rw [eq_some_iff, submatrix_apply, finCongr_apply,
    Fin.cast_trans, Fin.cast_eq_self, ne_eq]
  refine ⟨?_,hj.2⟩
  have := hj.1
  simp only [finCongr_apply] at this
  intro k hk
  apply this _ hk

lemma Matrix.IsRowEchelon.submatrix {m' n'} [Zero R] (x : Matrix (Fin m) (Fin n) R) (hx : x.IsRowEchelon)
  (hm : m' = m) (hn : n' = n) : (x.submatrix (finCongr hm) (finCongr hn)).IsRowEchelon := by
  simp [Matrix.isRowEchelon_iff]
  intro i j hij
  rw [← submatrix_eq x hm hn i, ← submatrix_eq x hm hn j]
  intro h
  show WithTop.map (Fin.castOrderIso hn.symm) _ < WithTop.map (Fin.castOrderIso hn.symm) _
  apply WithTop.equiv_lt (Fin.castOrderIso hn.symm)
  apply hx.1 ((finCongr hm) i) ((finCongr hm) j) hij (ne_of_apply_ne _ h)

lemma IsRowEchelonable.trans [CommRing R] : Transport (X := MatObj R) MatrixRel.IsRowEquiv MatObj.IsRowEchelonable := by
  simp [Transport, MatObj.IsRowEchelonable, Matrix.IsRowEchelonable]
  intro x y hxy P hP
  have ⟨Q, hQ⟩:= hxy.2
  use ((GeneralLinearGroup.reindex R (finCongr hxy.1.1)).1 P) * Q
  simp [Units.val_mul, Matrix.mul_assoc, hQ, Matrix.GeneralLinearGroup.reindex, MatObj.SameSize.reindex]
  apply Matrix.IsRowEchelon.submatrix _ hP


lemma isRowEchelonable_reindex_of_order_preserving {l o} [CommRing R] {A : Matrix (Fin m) (Fin n) R}
  (hA : A.IsRowEchelonable) (f : Fin m ≃ Fin l) (g : Fin n ≃ Fin o)
  (hf : ∀ x y, x < y → f.2 x < f.2 y) (hg1 : ∀ x y, x < y → g.1 x < g.1 y)
  (hg2 : ∀ x y, x < y → g.2 x < g.2 y) :
  (A.reindex f g).IsRowEchelonable := by
  have ⟨P, hP⟩ := hA
  use Matrix.GeneralLinearGroup.reindex R f P
  simp [GeneralLinearGroup.reindex, Matrix.isRowEchelon_iff]
  simp [Matrix.isRowEchelon_iff] at hP
  intro i j hij ht
  have hgi := Matrix.NonZeroIndex.submatrix_nonZeroIndex_map_simple_fin (P.1 * A) f.symm g.symm i hg2
  have hgj := Matrix.NonZeroIndex.submatrix_nonZeroIndex_map_simple_fin (P.1 * A) f.symm g.symm j hg2
  rw [hgi, hgj]
  apply WithTop.map_lt_of_lt _ hg1
  apply hP (f.2 i) (f.2 j) (hf _ _ hij)
  · simp [hgj]at ht
    exact ht

end Matrix.IsRowEchelon

open Matrix.NonZeroIndex MatrixSlice.S_col1Ready

section

variable [CommRing R] {x : MatObj R} (hx : S_col1Ready x)

/-- Given `m ≥ r`, constructs an equivalence between `Fin r ⊕ Fin (m - r)` and `Fin m`. -/
def finSumFinEquivOfLE {m r} (hm : m ≥ r) :
    Fin r ⊕ Fin (m - r) ≃ Fin m := trans finSumFinEquiv <| finCongr <|  add_sub_of_le hm

/--
Given `[NeZero m] [NeZero n]`, constructs an equivalence between matrices indexed by
`Fin 1 ⊕ Fin (m-1) × Fin 1 ⊕ Fin (n-1)` and matrices indexed by `Fin m × Fin n`.
This is useful for decomposing matrices into blocks.
-/
noncomputable def Matrix.equivSumFin {m} [NeZero m] [NeZero n] :
  Matrix (Fin 1 ⊕ Fin (m - 1)) (Fin 1 ⊕ Fin (n - 1)) R
  ≃ Matrix (Fin m) (Fin n) R :=
  reindex  (finSumFinEquivOfLE NeZero.one_le) (finSumFinEquivOfLE NeZero.one_le)

@[simp]
noncomputable def slice_botRight_aux (h : x.A 0 0 ≠ 0) :
  Matrix (Fin 1 ⊕ Fin (slice_botRight hx).m) (Fin 1 ⊕ Fin (slice_botRight hx).n) R
  ≃ Matrix (Fin x.m) (Fin x.n) R :=
  reindex (trans finSumFinEquiv <| finCongr (slice_botRight_m_eq_one_add hx h).symm)
    (trans finSumFinEquiv <| finCongr (one_add_slice_botRight_eq_sub_one hx))

@[simp]
noncomputable def MatObj.slice_botRight_upright :
  Matrix (Fin 1) (Fin (slice_botRight hx).n) R :=
  subUpRight <| x.A.submatrix (Fin.cast (add_sub_of_le NeZero.one_le)) (Fin.cast (one_add_slice_botRight_eq_sub_one _))

noncomputable def MatObj.slice_botRight_upright' :
  Matrix (Fin 1) (Fin (x.n - 1)) R :=
  subUpRight <| submatrix x.A (Fin.cast<|add_sub_of_le NeZero.one_le) (Fin.cast <| add_sub_of_le NeZero.one_le)

noncomputable def slice_botRight_aux_of_nezero (h : x.A 0 0 ≠ 0) :
  Matrix (Fin (slice_botRight hx).m) (Fin (slice_botRight hx).n) R
  ≃ Matrix (Fin (x.m - 1)) (Fin (x.n - 1)) R :=
  reindex (finCongr (slice_botRight_m_eq_sub_one hx h))
   (finCongr (slice_botRight_eq_sub_one hx))

lemma slice_botRight_equiv_reconstruction' (h : x.A 0 0 ≠ 0) :
  equivSumFin.2 x.A =
  (fromBlocks !![x.A 0 0] (x.slice_botRight_upright' hx) 0
     ((slice_botRight_aux_of_nezero hx h) (slice_botRight hx).A))  := by
  funext i j
  match i, j with
  | Sum.inl u, Sum.inl v => simp [Fin.fin_one_eq_zero]; rfl
  | Sum.inl u, Sum.inr v => simp; rfl
  | Sum.inr u, Sum.inl v =>
    simp [Fin.fin_one_eq_zero];
    apply hx.3
    simp [finSumFinEquivOfLE]
  | Sum.inr u, Sum.inr v =>
    simp [slice_botRight_def_A_ne_zero hx ⟨h⟩, MatObj.SameSize.reindex]
    rfl

lemma slice_botRight_equiv_reconstruction (h : x.A 0 0 ≠ 0) :
   x.A = equivSumFin.1
  (fromBlocks !![x.A 0 0] (x.slice_botRight_upright' hx) 0
     ((slice_botRight_aux_of_nezero hx h) (slice_botRight hx).A)) := by
  simp [← slice_botRight_equiv_reconstruction' hx h]

@[simp]
noncomputable def Matrix.equivSumFin' {m} [NeZero n] :
  Matrix (Fin 0 ⊕ Fin m) (Fin 1 ⊕ Fin (n - 1)) R
  ≃ Matrix (Fin m) (Fin n) R :=
reindex (finSumFinEquivOfLE (Nat.zero_le m))  (finSumFinEquivOfLE NeZero.one_le)

noncomputable def slice_botRight_aux_of_zero (h : x.A 0 0 = 0) :
  Matrix (Fin (slice_botRight hx).m) (Fin (slice_botRight hx).n) R
  ≃ Matrix (Fin x.m) (Fin (x.n - 1)) R :=
  reindex (finCongr (slice_botRight_m_eq_m_zero hx h))
   (finCongr (slice_botRight_eq_sub_one hx))

lemma equivSumFin'_zero_pivot_decomposition' (h : MatObj.A 0 0 = 0) :
  equivSumFin'.2 x.A = (fromBlocks 0 0 0 (slice_botRight_aux_of_zero hx h (slice_botRight hx).A)) := by
  funext i j
  match hi : i, hj : j with
  | Sum.inl u, _ =>
    exfalso
    exact not_succ_le_zero u.1 u.2
  | Sum.inr u, Sum.inl v =>
    simp [Fin.fin_one_eq_zero];
    by_cases hu : 0 < u
    · apply hx.3
      simpa [finSumFinEquivOfLE]
    simp at hu
    simpa [hu, finSumFinEquivOfLE, Fin.castAdd, Fin.castLE]
  | Sum.inr u, Sum.inr v =>
    simp [finSumFinEquivOfLE, Fin.cast, slice_botRight_aux_of_zero]
    let s : Fin ((slice_botRight hx).m):= ⟨u.1, Fin.cast._proof_1 (Eq.symm (slice_botRight_aux_of_zero._proof_1 hx h)) u ⟩
    let t : Fin ((slice_botRight hx).n):= ⟨v.1, Fin.cast._proof_1 (Eq.symm (slice_botRight_aux_of_nezero._proof_2 hx)) v ⟩
    show x.A ⟨s, Fin.cast._proof_1 (slice_botRight_m_eq_m_zero hx h) s⟩ ⟨1 + t.1, id (Eq.refl (1 + t.1)) ▸ Fin.cast._proof_1 (one_add_slice_botRight_eq_sub_one hx) (Fin.natAdd 1 t)⟩
      = (slice_botRight hx).A s t
    apply slice_botRight_m_eq_m_zero' hx h


lemma equivSumFin'_zero_pivot_decomposition (h) :
   x.A = equivSumFin'.1
  (fromBlocks 0 0 0 (slice_botRight_aux_of_zero hx h (slice_botRight hx).A)) := by
  simp [← equivSumFin'_zero_pivot_decomposition']


lemma slice_botRight_aux_of_nezero_preserves_rowEchelonable
  (h) {A} (hA : A.IsRowEchelonable) :
  ((slice_botRight_aux_of_nezero hx h) A).IsRowEchelonable := by
  apply isRowEchelonable_reindex_of_order_preserving hA _ _
  repeat intro _ _ _; simpa


lemma slice_botRight_aux_of_zero_preserves_rowEchelonable (h) {A} (hA : A.IsRowEchelonable) :
  ((slice_botRight_aux_of_zero hx h) A).IsRowEchelonable := by
  apply isRowEchelonable_reindex_of_order_preserving hA _ _
  repeat intro _ _ _; simpa



open Matrix.NonZeroIndex

section Matrix.NonZeroIndex
lemma submatrix_nonZeroIndex_equiv_cast {m i} [Zero F] [NeZero m] [NeZero n]
    (A : Matrix (Fin 1 ⊕ Fin (m - 1)) (Fin 1 ⊕ Fin (n - 1)) F) :
    (A.submatrix (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm).NonZeroIndex i =
    WithTop.map (Fin.cast (add_sub_of_le NeZero.one_le))
    ((A.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).NonZeroIndex (Fin.cast (add_sub_of_le NeZero.one_le).symm i)) := by
  apply submatrix_nonZeroIndex_map_simple A (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm i
    finSumFinEquiv.symm finSumFinEquiv.symm (Fin.cast (add_sub_of_le NeZero.one_le).symm)
  · exact (fun hj _ ↦ hj _ )
  · exact fun j hkj k hk ↦ hkj _ hk
  · rfl
  · funext i
    simp [finSumFinEquivOfLE]


lemma fromBlocks_reindex_nonZeroIndex_left_case [Zero α] [NeZero n] [NeZero m]
    {i : Fin m}
    (A : Matrix (Fin 1) (Fin 1) α) (B : Matrix (Fin 1) (Fin (n - 1)) α)
    (C : Matrix (Fin (m - 1)) (Fin 1) α) (D : Matrix (Fin (m - 1)) (Fin (n - 1)) α)
    (hi : i.1 < 1) (ha : A.NonZeroIndex ⟨i, hi⟩ ≠ ⊤) :
    ((fromBlocks A B C D).reindex (finSumFinEquivOfLE NeZero.one_le) (finSumFinEquivOfLE NeZero.one_le)).NonZeroIndex i =
    WithTop.map (fun y => Fin.cast (add_sub_of_le NeZero.one_le) (Fin.castAdd (n - 1) y)) (A.NonZeroIndex ⟨i, hi⟩) := by
  simp only [reindex_apply]
  have : A = (fromBlocks A B C D).submatrix (Sum.inl) (Sum.inl) := rfl
  nth_rw 2 [this]
  apply submatrix_nonZeroIndex_map_finite_case
    (fromBlocks A B C D) (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm
    i Sum.inl Sum.inl (fun j ↦ j.1 < 1) hi (fun j ↦ ⟨j.1, j.2⟩) (fun y => Fin.cast (add_sub_of_le NeZero.one_le) (Fin.castAdd (n - 1) y))
  · simpa
  · intro j hkj k hk
    simp [Fin.cast] at hk
  · have : i = 0 := Fin.val_eq_zero_iff.mp <| lt_one_iff.mp hi
    simp [finSumFinEquivOfLE, finSumFinEquiv, Fin.addCases, this, Fin.castLT]
  · funext i
    have : i = 0 := Fin.fin_one_eq_zero i
    simp [finSumFinEquivOfLE, finSumFinEquiv, Fin.addCases, this, Fin.castAdd, Fin.castLE, Fin.castLT]

lemma fromBlocks_reindex_nonZeroIndex_left_case_submatrix [Zero α] [NeZero n] [NeZero m]
    {i : Fin m}
    (A : Matrix (Fin 1) (Fin 1) α) (B : Matrix (Fin 1) (Fin (n - 1)) α)
    (C : Matrix (Fin (m - 1)) (Fin 1) α) (D : Matrix (Fin (m - 1)) (Fin (n - 1)) α)
    (hi : i.1 < 1) (ha : A.NonZeroIndex ⟨i, hi⟩ ≠ ⊤) :
    ((fromBlocks A B C D).submatrix (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm).NonZeroIndex i =
    WithTop.map (fun y => Fin.cast (add_sub_of_le NeZero.one_le) (Fin.castAdd (n - 1) y)) (A.NonZeroIndex ⟨i, hi⟩) := by
  apply fromBlocks_reindex_nonZeroIndex_left_case
  apply ha


lemma fromBlocks_lowerTriangular_reindex_nonZeroIndex_case
    [Zero α] [NeZero n] [NeZero m]
    {i : Fin m}
    (A : Matrix (Fin 1) (Fin 1) α) (B : Matrix (Fin 1) (Fin (n - 1)) α)
    (D : Matrix (Fin (m - 1)) (Fin (n - 1)) α)
    (hi : 1 ≤ i.1) :
    ((fromBlocks A B 0 D).submatrix (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm).NonZeroIndex i =
    WithTop.map (fun y => (Fin.cast (add_sub_of_le NeZero.one_le) (Fin.natAdd 1 y)))
      (D.NonZeroIndex (@Fin.natSub 1 (m - 1) (Fin.cast (add_sub_of_le NeZero.one_le).symm i) hi)) := by
    apply submatrix_nonZeroIndex_map (fromBlocks A B 0 D) (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm
      i Sum.inr Sum.inr (fun j ↦ 1 ≤ j.1) hi
      (fun j ↦ @Fin.natSub 1 (m - 1) (Fin.cast (add_sub_of_le NeZero.one_le).symm j.1) j.2)
    · intro hj j
      match ((finSumFinEquivOfLE NeZero.one_le).symm j) with
      | Sum.inr u => simp only [hj]
      | Sum.inl v => simp only [fromBlocks_apply₂₁, zero_apply]
    · intro j hj k hk
      match hkf : ((finSumFinEquivOfLE NeZero.one_le).symm k) with
      | Sum.inr u =>
        simp at *
        apply hj
        simp [finSumFinEquivOfLE, finSumFinEquiv, Fin.addCases] at hkf
        by_cases hkl : k = 0
        · simp [hkl] at hkf
        simp [hkl, Fin.subNat] at hkf
        simp [← hkf]
        refine Fin.mk_lt_of_lt_val <| Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt ?_) hk
        simpa
      | Sum.inl v => simp only [fromBlocks_apply₂₁, zero_apply]
    · have : ¬ i = 0 := Fin.pos_iff_ne_zero.mp hi
      simp [finSumFinEquivOfLE, finSumFinEquiv, Fin.addCases, this, Fin.natSub, Fin.subNat]
    · funext i
      simp [finSumFinEquivOfLE, finSumFinEquiv, Fin.addCases, Fin.natAdd]

end Matrix.NonZeroIndex

/--
Characterizes when a 1×1 matrix is the zero matrix.

A matrix with a single entry is zero if and only if its only entry is zero.
This follows from the fact that `Fin 1` has only one element (index 0).
-/
lemma matrix_one_by_one_zero_iff [Zero F] {a : Matrix (Fin 1) (Fin 1) F} :
  a = 0 ↔ a 0 0 = 0 := by
  refine ⟨?_, ?_⟩
  · intro ha
    show a 0 0 = (0: Matrix (Fin 1) (Fin 1) F) 0 0
    rw [ha]
  · intro ha
    funext i j
    simpa [Fin.fin_one_eq_zero]

lemma matrix_one_by_one_ne_zero_iff [Zero F] {a : Matrix (Fin 1) (Fin 1) F} :
  a ≠ 0 ↔ a 0 0 ≠ 0 := by
  simp [matrix_one_by_one_zero_iff]

/--
Characterizes when the square of a 1×1 matrix is zero.

For a 1×1 matrix over a ring with no zero divisors, `a * a = 0` if and only if
the single entry `a 0 0 = 0`. This follows from the fact that matrix multiplication
of 1×1 matrices reduces to ordinary multiplication of their entries.
-/
lemma matrix_one_by_one_square_zero_iff [Ring F] [NoZeroDivisors F]
  {a : Matrix (Fin 1) (Fin 1) F} :
  a * a = 0 ↔ a 0 0 = 0 := by
  simp [matrix_one_by_one_zero_iff, HMul.hMul, dotProduct]
  show (a 0 0) * (a 0 0) = 0 ↔ _
  rw [mul_self_eq_zero]

lemma matrix_one_by_one_square_ne_zero_iff [Ring F] [NoZeroDivisors F]
  {a : Matrix (Fin 1) (Fin 1) F} :
  a * a ≠ 0 ↔ a 0 0 ≠ 0 := by
  simp [matrix_one_by_one_square_zero_iff]

/--
Determines the non-zero index of a non-zero 1×1 matrix.

For a non-zero 1×1 matrix, the non-zero index at row 0 must be column 0,
since there's only one possible entry position.
-/
lemma matrix_one_by_one_nonZeroIndex [Zero F] {a : Matrix (Fin 1) (Fin 1) F} (ha : a ≠ 0) :
  a.NonZeroIndex 0 = some 0 := by
  simp [eq_some_iff]
  show a 0 0 ≠ (0: Matrix (Fin 1) (Fin 1) F) 0 0
  by_contra!
  apply ha
  funext i j
  simp [Fin.fin_one_eq_zero] at *
  exact this

/--
A non-zero 1×1 matrix never has a ⊤ (all-zero) non-zero index.

For any valid row index `⟨i, hi⟩` where `i < 1` in a non-zero 1×1 matrix,
the non-zero index cannot be ⊤, since the matrix has at least one non-zero entry.
-/
lemma matrix_one_by_one_nonZeroIndex_ne_top {i} [Zero F] {a : Matrix (Fin 1) (Fin 1) F}
  (ha : a ≠ 0) (hi : i < 1) :
  a.NonZeroIndex ⟨i, hi⟩ ≠ ⊤ := by
  simp [lt_one_iff.mp hi, matrix_one_by_one_nonZeroIndex ha]

/--
The non-zero index of a non-zero 1×1 matrix is always column 0.

For any valid row index `⟨i, hi⟩` where `i < 1` in a non-zero 1×1 matrix,
the non-zero index is exactly `some 0`, since there's only one possible column.
-/
lemma matrix_one_by_one_nonZeroIndex_eq_some_zero {i} [Zero F] {a : Matrix (Fin 1) (Fin 1) F}
  (ha : a ≠ 0) (hi : i < 1) :
  a.NonZeroIndex ⟨i, hi⟩ = some 0 := by
  simp [lt_one_iff.mp hi, matrix_one_by_one_nonZeroIndex ha]


lemma isRowEchelonable_fromBlocks_upper_triangular
    [Field F] {m n : ℕ} [NeZero m] [NeZero n]
    (a : Matrix (Fin 1) (Fin 1) F) (ha : a ≠ 0)
    (b : Matrix (Fin 1) (Fin (n - 1)) F)
    (c : Matrix (Fin (m - 1)) (Fin (n - 1)) F)
    (hxr : IsRowEchelonable c) :
    IsRowEchelonable (equivSumFin.1 (fromBlocks a b 0 c)) := by
  rcases hxr with ⟨P, pc⟩
  have haa : a * a ≠ 0 :=
    matrix_one_by_one_square_ne_zero_iff.2 <| matrix_one_by_one_ne_zero_iff.1 ha
  let A : GL (Fin 1) F := Matrix.GeneralLinearGroup.mk' a
    (by simpa using invertibleOfNonzero <| matrix_one_by_one_ne_zero_iff.1 ha)
  let Q : GL (Fin m) F :=
    (Matrix.GeneralLinearGroup.reindex F <| finSumFinEquivOfLE NeZero.one_le).1 (Matrix.GeneralLinearGroup.glDirectSum A P)
  use Q; simp [Q, GeneralLinearGroup.reindex, GeneralLinearGroup.glDirectSum, equivSumFin, reindex_apply, submatrix_mul_equiv,
    fromBlocks_multiply, GeneralLinearGroup.val_mk', A, Matrix.isRowEchelon_iff]
  intro i j hij hnt; change _ ≠ ⊤ at hnt
  have hi1 := fromBlocks_reindex_nonZeroIndex_left_case_submatrix (i := i) (a * a) (a * b) 0 (P.1 * c)
  have hi2 := fromBlocks_lowerTriangular_reindex_nonZeroIndex_case (i := i) (a * a) (a * b) (P.1 * c)
  have hj1 := fromBlocks_reindex_nonZeroIndex_left_case_submatrix (i := j) (a * a) (a * b) 0 (P.1 * c)
  have hj2 := fromBlocks_lowerTriangular_reindex_nonZeroIndex_case (i := j) (a * a) (a * b) (P.1 * c)
  rcases (Nat.lt_or_ge i.1 1) , (Nat.lt_or_ge j.1 1) with ⟨hi | hi, hj | hj⟩
  · simp [Fin.val_eq_zero_iff.mp (lt_one_iff.mp hi),  Fin.val_eq_zero_iff.mp (lt_one_iff.mp hj)] at hij
  · simp [hi1 hi (matrix_one_by_one_nonZeroIndex_ne_top haa _), hj2 hj, matrix_one_by_one_nonZeroIndex_eq_some_zero haa _]
    let yP := (P.1 * c).NonZeroIndex (Fin.natSub (m - 1) (Fin.cast (add_sub_of_le NeZero.one_le).symm j) hj)
    show WithTop.some (Fin.cast (add_sub_of_le NeZero.one_le) (Fin.castAdd (n - 1) 0)) < WithTop.map _ yP
    simp only [Fin.cast, Fin.isValue, Fin.coe_castAdd, Fin.val_eq_zero, Fin.mk_zero',
      WithTop.coe_zero, Fin.coe_natAdd]
    by_cases hyp : yP = ⊤
    · simp [hyp]
    · change yP ≠ ⊤ at hyp
      rw [WithTop.ne_top_iff_exists] at hyp
      rcases hyp with ⟨a, ha⟩
      simp [← ha,  ← Fin.val_fin_lt]
  · exfalso; exact (not_lt.2 <| le_trans (le_of_lt hj) hi) hij
  · simpa [hi2 hi, hj2 hj] using  WithTop.map_lt_of_lt _  (by simp) <| pc.1 _ _ (by simp [Fin.natSub, Nat.sub_lt_sub_right hi hij])
        (by simp [hj2 hj] at hnt; simpa)

lemma zero_padded_submatrix_nonZeroIndex [CommRing F] {m n : ℕ} [NeZero n]
  (A : Matrix (Fin m) (Fin (n - 1)) F) (i : Fin m) :
  ((fromBlocks 0 0 0 A).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).symm (finSumFinEquivOfLE (@NeZero.one_le n _)).symm).NonZeroIndex i
  = WithTop.map (fun y ↦ Fin.cast (add_sub_of_le NeZero.one_le) (Fin.natAdd 1 y)) (A.NonZeroIndex i) := by
  apply submatrix_nonZeroIndex_map_simple (fromBlocks 0 0 0 A) (finSumFinEquivOfLE (Nat.zero_le m)).symm (finSumFinEquivOfLE (@NeZero.one_le n _)).symm
    i Sum.inr Sum.inr id (fun y ↦ Fin.cast (add_sub_of_le NeZero.one_le) (Fin.natAdd 1 y))
  · intro hj j
    match (finSumFinEquivOfLE (@NeZero.one_le n _)).symm j with
    | Sum.inl u => simp
    | Sum.inr v => simpa using hj _
  · intro j hj k hk
    simp [Fin.cast] at hk
    match h : (finSumFinEquivOfLE (@NeZero.one_le n _)).symm k with
    | Sum.inl u => simp
    | Sum.inr v =>
      simp at *
      apply hj
      by_cases hk0 : k = 0
      · simp [finSumFinEquivOfLE, Fin.cast, finSumFinEquiv, Fin.addCases, hk0] at h
      simp [finSumFinEquivOfLE, Fin.cast, finSumFinEquiv, Fin.addCases, hk0] at h
      simp [← h]
      refine Fin.mk_lt_of_lt_val <| (Nat.sub_lt_iff_lt_add' ?_).mpr hk
      refine one_le_iff_ne_zero.mpr (Fin.val_ne_zero_iff.mpr hk0)
  · simp [finSumFinEquivOfLE, Fin.cast, finSumFinEquiv, Fin.addCases]
  · funext
    simp [finSumFinEquivOfLE, Fin.cast, finSumFinEquiv, Fin.addCases]

lemma finSumFinEquivOfLE_zero_equiv_eq_inr :
   (finSumFinEquivOfLE (Nat.zero_le m)).2 = Sum.inr := by
    funext i
    simp [finSumFinEquivOfLE, Fin.cast, finSumFinEquiv, Fin.addCases]

lemma matrix_mul_submatrix_fromBlocks_zero_top_with_equiv [AddCommMonoid F] [Mul F] [NeZero n]
  (a : Matrix (Fin m) (Fin 1) F) (b : Matrix (Fin m) (Fin (n - 1)) F)
  (P : Matrix (Fin m) (Fin m) F) :
  P * ((fromBlocks 0 0 a b : Matrix (Fin 0 ⊕ Fin m) (Fin 1 ⊕ Fin (n - 1)) F).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).2 (finSumFinEquivOfLE (@NeZero.one_le n _)).2) =
  (fromBlocks 0 0 (P * a) (P * b) : Matrix (Fin 0 ⊕ Fin m) (Fin 1 ⊕ Fin (n - 1)) F ).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).2 (finSumFinEquivOfLE (@NeZero.one_le n _)).2 := by
  rw [finSumFinEquivOfLE_zero_equiv_eq_inr]
  apply matrix_mul_distrib_submatrix_fromBlocks_zero_top

lemma isRowEchelonable_fromBlocks_upper_triangular'
    [CommRing F] {m n : ℕ} [NeZero n]
    (c : Matrix (Fin m) (Fin (n - 1)) F)
    (hxr : IsRowEchelonable c) :
    IsRowEchelonable (equivSumFin'.1 (fromBlocks 0 0 0 c)) := by
  rcases hxr with ⟨P, pc⟩
  use P
  simp [reindex_apply]
  show (P.1 * (fromBlocks 0 0 0 c).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).2 (finSumFinEquivOfLE (@NeZero.one_le n _)).2).IsRowEchelon
  rw [matrix_mul_submatrix_fromBlocks_zero_top_with_equiv]
  simp [Matrix.isRowEchelon_iff] at *
  intro i j hij hnt;
  change ((fromBlocks 0 0 0 (P.1 * c)).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).symm (finSumFinEquivOfLE (@NeZero.one_le n _)).symm).NonZeroIndex j ≠ ⊤ at hnt
  show ((fromBlocks 0 0 0 (P.1 * c)).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).symm (finSumFinEquivOfLE (@NeZero.one_le n _)).symm).NonZeroIndex i <
    ((fromBlocks 0 0 0 (P.1 * c)).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).symm (finSumFinEquivOfLE (@NeZero.one_le n _)).symm).NonZeroIndex j
  rw [zero_padded_submatrix_nonZeroIndex (P.1 * c) i, zero_padded_submatrix_nonZeroIndex (P.1 * c) j] at *
  refine
    WithTop.map_lt_of_lt (fun y ↦ Fin.cast (add_sub_of_le NeZero.one_le) (Fin.natAdd 1 y)) ?_ ?_
  · intro x y hxy
    simpa
  · apply pc
    apply hij
    simp at hnt
    apply hnt

lemma IsRowEchelonable.bridge [Field F] {x : MatObj F} (hx : S_col1Ready x)
    (hxr : (slice_botRight hx).IsRowEchelonable) :
  x.IsRowEchelonable:= by
  simp [MatObj.IsRowEchelonable]
  by_cases h : x.A 0 0 ≠ 0
  · rw [slice_botRight_equiv_reconstruction hx h]
    apply isRowEchelonable_fromBlocks_upper_triangular
    exact matrix_one_by_one_ne_zero_iff.mpr h
    apply slice_botRight_aux_of_nezero_preserves_rowEchelonable hx h hxr
  simp at h
  rw [equivSumFin'_zero_pivot_decomposition hx h]
  apply isRowEchelonable_fromBlocks_upper_triangular'
  apply slice_botRight_aux_of_zero_preserves_rowEchelonable hx h hxr

end


theorem matrix_rowOperation_induction {R} [Field R]
    (P : MatObj R → Prop)
    (trans : Transport MatrixRel.IsRowEquiv P)
    (bridge : ∀ {x} (hx : S_col1Ready x), P (slice_botRight hx) → P x)
    (baseμ : ∀ {x}, x.μ = 0 → P x) :
  ∀ x, P x := by
  apply equivSliceInduction_viaElimOp (X := MatObj R) MatObj.μ trans S_col1Ready
    slice_botRight bridge _ MatrixRel.IsRowEquiv.muMono S_col1Ready_prog baseμ
  rw [← MatNonEmpty_eq]
  exact gaussColElimOp R

lemma IsRowEchelonable.baseμ [CommRing R] {x : MatObj R} (hx : x.μ = 0) :
    x.IsRowEchelonable := by
  simp [MatObj.μ] at hx
  simp [MatObj.IsRowEchelonable, IsRowEchelonable]
  use 1
  simp [Matrix.isRowEchelon_iff]
  intro i j hij hnt
  simp [ne_top_iff] at hnt
  rcases hnt with ⟨w, hw⟩
  rcases hx with h | h
  · simp [h] at i
    exfalso
    exact not_succ_le_zero i.1 i.2
  simp [h] at w
  exfalso
  exact not_succ_le_zero w.1 w.2

theorem matrix_Gauss_pre {R} [Field R] :
  ∀ x : MatObj R, x.IsRowEchelonable := by
  apply matrix_rowOperation_induction
  exact IsRowEchelonable.trans
  exact fun {x} hx a ↦ IsRowEchelonable.bridge hx a
  exact IsRowEchelonable.baseμ


/--
Every matrix over a field can be put into row echelon form by Gaussian elimination.
This is the main existence theorem for row echelon forms.
-/
theorem exists_rowEchelonForm {R} [Field R] {n m} (x : Matrix (Fin n) (Fin m) R) :
  x.IsRowEchelonable := by
  let y : MatObj R := ⟨n,m,x⟩
  apply matrix_Gauss_pre y

end

end GaussianEliminator
