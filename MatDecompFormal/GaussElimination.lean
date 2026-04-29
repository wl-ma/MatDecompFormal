import Mathlib

open Nat Matrix Classical

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
lemma one_one_mul_one_n [Mul R] [AddCommMonoid R]
    (a : Matrix (Fin 1) (Fin 1) R) (b : Matrix (Fin 1) m R) :
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

/--
The product of two outer products can be expressed as a scalar multiple of
another outer product.
-/
lemma vecMulVec_mul_vecMulVec [Fintype m] [CommSemiring R] (a b c d : m → R) :
    vecMulVec a b * vecMulVec c d = (b ⬝ᵥ c) • (vecMulVec a d):= by
  simp only [vecMulVec_eq_mul, mul_assoc_nested, m_one_mul_one_one, Fin.isValue,
    dot_product_as_matrix_mul, op_smul_eq_smul, smul_mul]

end vecMulVec
