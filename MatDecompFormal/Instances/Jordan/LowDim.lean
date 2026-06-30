/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Jordan.Existence

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open scoped Polynomial

/-!
# Low-Dimensional Jordan Companion Checks

This file contains explicit `n = 2, 3, 4` companion-block computations for
`(X - C λ)^n`.  These lemmas are regression checks for the binomial chain-basis
formula in `Jordan.Existence`; they are not the proof spine for the final
Jordan theorem.  The main route must prove the all-`n`
`JordanLinearPowerCompanionBlockBridge` and feed it into the recursive descent
template.
-/

/-- The explicit basis-change matrix for the quadratic linear-power companion check. -/
def jordanQuadraticCompanionP
    {K : Type u} [Field K] (lam : K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![-lam, 1; 1, 0]

/-- The inverse of `jordanQuadraticCompanionP`. -/
def jordanQuadraticCompanionPinv
    {K : Type u} [Field K] (lam : K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, lam]

/-- The quadratic explicit change matrix is the general binomial chain matrix. -/
theorem jordanQuadraticCompanionP_eq_linearPowerCompanionChange
    {K : Type u} [Field K] (lam : K) :
    jordanQuadraticCompanionP (K := K) lam =
      linearPowerCompanionChange lam 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanQuadraticCompanionP, linearPowerCompanionChange]

/-- The quadratic explicit inverse is the general inverse binomial chain matrix. -/
theorem jordanQuadraticCompanionPinv_eq_linearPowerCompanionChangeInv
    {K : Type u} [Field K] (lam : K) :
    jordanQuadraticCompanionPinv (K := K) lam =
      linearPowerCompanionChangeInv lam 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanQuadraticCompanionPinv, linearPowerCompanionChangeInv]

/-- The quadratic companion basis-change matrix is invertible. -/
theorem jordanQuadraticCompanion_hasMatrixInverse
    {K : Type u} [Field K] (lam : K) :
    HasMatrixInverse
      (jordanQuadraticCompanionP (K := K) lam)
      (jordanQuadraticCompanionPinv (K := K) lam) := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [jordanQuadraticCompanionP, jordanQuadraticCompanionPinv]

/--
The standard companion matrix for `(X - C lam)^2` is similar to the standard
size-two Jordan block.
-/
theorem companionMatrixFin_linear_power_two_hasJordan
    {K : Type u} [Field K] (lam : K) :
    HasJordanMatrix
      (companionMatrixFin ((Polynomial.X - Polynomial.C lam) ^ (2 : Nat))) := by
  classical
  let p : K[X] := (Polynomial.X - Polynomial.C lam) ^ (2 : Nat)
  have hdeg : p.natDegree = 2 := by
    simp [p, Polynomial.natDegree_pow]
  let e : Fin p.natDegree ≃ Fin 2 := finCongr hdeg
  let P := jordanQuadraticCompanionP (K := K) lam
  let J := jordanBlock lam 2
  have hInv : HasMatrixInverse P (jordanQuadraticCompanionPinv (K := K) lam) := by
    simpa [P] using jordanQuadraticCompanion_hasMatrixInverse (K := K) lam
  have hP : InvertibleMatrix P :=
    invertibleMatrix_of_hasMatrixInverse hInv
  have hPinv : P⁻¹ = jordanQuadraticCompanionPinv (K := K) lam := by
    haveI : Invertible P := hP.invertible
    exact Matrix.inv_eq_left_inv hInv.1
  have hcoeff0 : p.coeff 0 = lam ^ 2 := by
    change (((Polynomial.X - Polynomial.C lam) ^ (2 : Nat) : K[X]).coeff 0) = lam ^ 2
    rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]
    norm_num
  have hcoeff1 : -p.coeff 1 = 2 * lam := by
    change -(((Polynomial.X - Polynomial.C lam) ^ (2 : Nat) : K[X]).coeff 1) = 2 * lam
    rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]
    norm_num
    ring
  have hJ : J = !![lam, 1; 0, lam] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, jordanBlock]
  have hModel :
      HasJordanMatrix (Matrix.reindex e e (companionMatrixFin p)) := by
    refine ⟨P, J, hP, isJordanMatrix_jordanBlock lam 2 (by decide), ?_⟩
    rw [hPinv]
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, e, p, companionMatrixFin, jordanQuadraticCompanionP,
        jordanQuadraticCompanionPinv,
        hdeg, hcoeff0, hcoeff1] <;>
      ring
  have hBack :
      HasJordanMatrix
        (Matrix.reindex e.symm e.symm
          (Matrix.reindex e e (companionMatrixFin p))) :=
    hasJordanMatrix_reindex
      (K := K)
      (ι := Fin 2)
      (κ := Fin p.natDegree)
      e.symm hModel
  simpa [p, e, Matrix.reindex_apply, Matrix.submatrix_submatrix,
    Function.comp_def] using hBack

/--
Any verified companion block for `(X - C lam)^2` has Jordan form.
-/
theorem companion_hasJordan_of_linear_power_two
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} (lam : K)
    (hC : SingleCompanionBlockForm C
      ((Polynomial.X - Polynomial.C lam) ^ (2 : Nat))) :
    HasJordanMatrix C := by
  classical
  rcases hC.2.2.2 with ⟨e, he⟩
  have hStd :
      HasJordanMatrix
        (Matrix.reindex e e C) := by
    simpa [he] using companionMatrixFin_linear_power_two_hasJordan (K := K) lam
  have hBack :
      HasJordanMatrix (Matrix.reindex e.symm e.symm (Matrix.reindex e e C)) :=
    hasJordanMatrix_reindex_fin e hStd
  simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix, Function.comp_def] using hBack

/-- The explicit basis-change matrix for the cubic linear-power companion check. -/
def jordanCubicCompanionP
    {K : Type u} [Field K] (lam : K) :
    Matrix (Fin 3) (Fin 3) K :=
  !![lam ^ 2, -lam, 1; -2 * lam, 1, 0; 1, 0, 0]

/-- The inverse of `jordanCubicCompanionP`. -/
def jordanCubicCompanionPinv
    {K : Type u} [Field K] (lam : K) :
    Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, 1, 2 * lam; 1, lam, lam ^ 2]

/-- The cubic explicit change matrix is the general binomial chain matrix. -/
theorem jordanCubicCompanionP_eq_linearPowerCompanionChange
    {K : Type u} [Field K] (lam : K) :
    jordanCubicCompanionP (K := K) lam =
      linearPowerCompanionChange lam 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanCubicCompanionP, linearPowerCompanionChange]

/-- The cubic explicit inverse is the general inverse binomial chain matrix. -/
theorem jordanCubicCompanionPinv_eq_linearPowerCompanionChangeInv
    {K : Type u} [Field K] (lam : K) :
    jordanCubicCompanionPinv (K := K) lam =
      linearPowerCompanionChangeInv lam 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanCubicCompanionPinv, linearPowerCompanionChangeInv]

/-- The cubic companion basis-change matrix is invertible. -/
theorem jordanCubicCompanion_hasMatrixInverse
    {K : Type u} [Field K] (lam : K) :
    HasMatrixInverse
      (jordanCubicCompanionP (K := K) lam)
      (jordanCubicCompanionPinv (K := K) lam) := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [jordanCubicCompanionP, jordanCubicCompanionPinv] <;>
    ring

/--
The standard companion matrix for `(X - C lam)^3` is similar to the standard
size-three Jordan block.
-/
theorem companionMatrixFin_linear_power_three_hasJordan
    {K : Type u} [Field K] (lam : K) :
    HasJordanMatrix
      (companionMatrixFin ((Polynomial.X - Polynomial.C lam) ^ (3 : Nat))) := by
  classical
  let p : K[X] := (Polynomial.X - Polynomial.C lam) ^ (3 : Nat)
  have hdeg : p.natDegree = 3 := by
    simp [p, Polynomial.natDegree_pow]
  let e : Fin p.natDegree ≃ Fin 3 := finCongr hdeg
  let P := jordanCubicCompanionP (K := K) lam
  let J := jordanBlock lam 3
  have hInv : HasMatrixInverse P (jordanCubicCompanionPinv (K := K) lam) := by
    simpa [P] using jordanCubicCompanion_hasMatrixInverse (K := K) lam
  have hP : InvertibleMatrix P :=
    invertibleMatrix_of_hasMatrixInverse hInv
  have hPinv : P⁻¹ = jordanCubicCompanionPinv (K := K) lam := by
    haveI : Invertible P := hP.invertible
    exact Matrix.inv_eq_left_inv hInv.1
  have hcoeff0 : p.coeff 0 = -lam ^ 3 := by
    change (((Polynomial.X - Polynomial.C lam) ^ (3 : Nat) : K[X]).coeff 0) = -lam ^ 3
    rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]
    norm_num
    ring_nf
  have hcoeff1 : -p.coeff 1 = -(3 * lam ^ 2) := by
    change -(((Polynomial.X - Polynomial.C lam) ^ (3 : Nat) : K[X]).coeff 1) =
      -(3 * lam ^ 2)
    rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]
    norm_num
    ring_nf
  have hcoeff2 : -p.coeff 2 = 3 * lam := by
    change -(((Polynomial.X - Polynomial.C lam) ^ (3 : Nat) : K[X]).coeff 2) =
      3 * lam
    rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]
    norm_num
    ring
  have hJ : J = !![lam, 1, 0; 0, lam, 1; 0, 0, lam] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, jordanBlock]
  have hModel :
      HasJordanMatrix (Matrix.reindex e e (companionMatrixFin p)) := by
    refine ⟨P, J, hP, isJordanMatrix_jordanBlock lam 3 (by decide), ?_⟩
    rw [hPinv]
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, e, p, companionMatrixFin, jordanCubicCompanionP,
        jordanCubicCompanionPinv,
        hdeg, hcoeff0, hcoeff1, hcoeff2] <;>
      ring
  have hBack :
      HasJordanMatrix
        (Matrix.reindex e.symm e.symm
          (Matrix.reindex e e (companionMatrixFin p))) :=
    hasJordanMatrix_reindex
      (K := K)
      (ι := Fin 3)
      (κ := Fin p.natDegree)
      e.symm hModel
  simpa [p, e, Matrix.reindex_apply, Matrix.submatrix_submatrix,
    Function.comp_def] using hBack

/--
Any verified companion block for `(X - C lam)^3` has Jordan form.
-/
theorem companion_hasJordan_of_linear_power_three
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} (lam : K)
    (hC : SingleCompanionBlockForm C
      ((Polynomial.X - Polynomial.C lam) ^ (3 : Nat))) :
    HasJordanMatrix C := by
  classical
  rcases hC.2.2.2 with ⟨e, he⟩
  have hStd :
      HasJordanMatrix
        (Matrix.reindex e e C) := by
    simpa [he] using companionMatrixFin_linear_power_three_hasJordan (K := K) lam
  have hBack :
      HasJordanMatrix (Matrix.reindex e.symm e.symm (Matrix.reindex e e C)) :=
    hasJordanMatrix_reindex_fin e hStd
  simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix, Function.comp_def] using hBack

/-- The explicit basis-change matrix for the quartic linear-power companion check. -/
def jordanQuarticCompanionP
    {K : Type u} [Field K] (lam : K) :
    Matrix (Fin 4) (Fin 4) K :=
  !![-lam ^ 3, lam ^ 2, -lam, 1;
     3 * lam ^ 2, -2 * lam, 1, 0;
     -3 * lam, 1, 0, 0;
     1, 0, 0, 0]

/-- The inverse of `jordanQuarticCompanionP`. -/
def jordanQuarticCompanionPinv
    {K : Type u} [Field K] (lam : K) :
    Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1;
     0, 0, 1, 3 * lam;
     0, 1, 2 * lam, 3 * lam ^ 2;
     1, lam, lam ^ 2, lam ^ 3]

/-- The quartic explicit change matrix is the general binomial chain matrix. -/
theorem jordanQuarticCompanionP_eq_linearPowerCompanionChange
    {K : Type u} [Field K] (lam : K) :
    jordanQuarticCompanionP (K := K) lam =
      linearPowerCompanionChange lam 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanQuarticCompanionP, linearPowerCompanionChange];
    ring

/-- The quartic explicit inverse is the general inverse binomial chain matrix. -/
theorem jordanQuarticCompanionPinv_eq_linearPowerCompanionChangeInv
    {K : Type u} [Field K] (lam : K) :
    jordanQuarticCompanionPinv (K := K) lam =
      linearPowerCompanionChangeInv lam 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanQuarticCompanionPinv, linearPowerCompanionChangeInv]

set_option maxHeartbeats 800000 in
-- The 4x4 explicit inverse proof expands sixteen polynomial matrix entries.
/-- The quartic companion basis-change matrix is invertible. -/
theorem jordanQuarticCompanion_hasMatrixInverse
    {K : Type u} [Field K] (lam : K) :
    HasMatrixInverse
      (jordanQuarticCompanionP (K := K) lam)
      (jordanQuarticCompanionPinv (K := K) lam) := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [jordanQuarticCompanionP, jordanQuarticCompanionPinv] <;>
    ring

set_option maxHeartbeats 800000 in
-- The 4x4 explicit similarity proof expands all entries of `P * J * P⁻¹`.
/--
The standard companion matrix for `(X - C lam)^4` is similar to the standard
size-four Jordan block.
-/
theorem companionMatrixFin_linear_power_four_hasJordan
    {K : Type u} [Field K] (lam : K) :
    HasJordanMatrix
      (companionMatrixFin ((Polynomial.X - Polynomial.C lam) ^ (4 : Nat))) := by
  classical
  let p : K[X] := (Polynomial.X - Polynomial.C lam) ^ (4 : Nat)
  have hdeg : p.natDegree = 4 := by
    simp [p, Polynomial.natDegree_pow]
  let e : Fin p.natDegree ≃ Fin 4 := finCongr hdeg
  let P := jordanQuarticCompanionP (K := K) lam
  let J := jordanBlock lam 4
  have hInv : HasMatrixInverse P (jordanQuarticCompanionPinv (K := K) lam) := by
    simpa [P] using jordanQuarticCompanion_hasMatrixInverse (K := K) lam
  have hP : InvertibleMatrix P :=
    invertibleMatrix_of_hasMatrixInverse hInv
  have hPinv : P⁻¹ = jordanQuarticCompanionPinv (K := K) lam := by
    haveI : Invertible P := hP.invertible
    exact Matrix.inv_eq_left_inv hInv.1
  have hcoeff0 : -p.coeff 0 = -lam ^ 4 := by
    change -(((Polynomial.X - Polynomial.C lam) ^ (4 : Nat) : K[X]).coeff 0) =
      -lam ^ 4
    rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]
    norm_num
  have hcoeff1 : -p.coeff 1 = 4 * lam ^ 3 := by
    change -(((Polynomial.X - Polynomial.C lam) ^ (4 : Nat) : K[X]).coeff 1) =
      4 * lam ^ 3
    rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]
    norm_num
    ring_nf
  have hcoeff2 : -p.coeff 2 = -(6 * lam ^ 2) := by
    change -(((Polynomial.X - Polynomial.C lam) ^ (4 : Nat) : K[X]).coeff 2) =
      -(6 * lam ^ 2)
    rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]
    rw [show Nat.choose 4 2 = 6 by decide]
    norm_num
    ring_nf
  have hcoeff3 : -p.coeff 3 = 4 * lam := by
    change -(((Polynomial.X - Polynomial.C lam) ^ (4 : Nat) : K[X]).coeff 3) =
      4 * lam
    rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]
    norm_num
    ring
  have hJ : J = !![lam, 1, 0, 0; 0, lam, 1, 0; 0, 0, lam, 1; 0, 0, 0, lam] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, jordanBlock]
  have hModel :
      HasJordanMatrix (Matrix.reindex e e (companionMatrixFin p)) := by
    refine ⟨P, J, hP, isJordanMatrix_jordanBlock lam 4 (by decide), ?_⟩
    rw [hPinv]
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, e, p, companionMatrixFin, jordanQuarticCompanionP,
        jordanQuarticCompanionPinv,
        hdeg, hcoeff0, hcoeff1, hcoeff2, hcoeff3] <;>
      ring
  have hBack :
      HasJordanMatrix
        (Matrix.reindex e.symm e.symm
          (Matrix.reindex e e (companionMatrixFin p))) :=
    hasJordanMatrix_reindex
      (K := K)
      (ι := Fin 4)
      (κ := Fin p.natDegree)
      e.symm hModel
  simpa [p, e, Matrix.reindex_apply, Matrix.submatrix_submatrix,
    Function.comp_def] using hBack

/--
Any verified companion block for `(X - C lam)^4` has Jordan form.
-/
theorem companion_hasJordan_of_linear_power_four
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} (lam : K)
    (hC : SingleCompanionBlockForm C
      ((Polynomial.X - Polynomial.C lam) ^ (4 : Nat))) :
    HasJordanMatrix C := by
  classical
  rcases hC.2.2.2 with ⟨e, he⟩
  have hStd :
      HasJordanMatrix
        (Matrix.reindex e e C) := by
    simpa [he] using companionMatrixFin_linear_power_four_hasJordan (K := K) lam
  have hBack :
      HasJordanMatrix (Matrix.reindex e.symm e.symm (Matrix.reindex e e C)) :=
    hasJordanMatrix_reindex_fin e hStd
  simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix, Function.comp_def] using hBack

/--
A single-root factorization with exponent two is discharged by the quadratic
linear-power companion check.
-/
theorem companion_hasJordan_of_single_root_exponent_two_factorization
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]}
    (hC : SingleCompanionBlockForm C p)
    (factorization : JordanSplitPolynomialFactorization K p)
    [Unique factorization.rootIdx]
    (hexp : factorization.exponent default = 2) :
    HasJordanMatrix C := by
  classical
  have hCq :
      SingleCompanionBlockForm C
        ((Polynomial.X - Polynomial.C (factorization.eigenvalue default)) ^
          (2 : Nat)) :=
    singleCompanionBlockForm_of_single_root_factorization_exponent_eq
      hC factorization hexp
  exact companion_hasJordan_of_linear_power_two
    (factorization.eigenvalue default)
    hCq

/--
A single-root factorization with exponent three is discharged by the cubic
linear-power companion check.
-/
theorem companion_hasJordan_of_single_root_exponent_three_factorization
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]}
    (hC : SingleCompanionBlockForm C p)
    (factorization : JordanSplitPolynomialFactorization K p)
    [Unique factorization.rootIdx]
    (hexp : factorization.exponent default = 3) :
    HasJordanMatrix C := by
  classical
  have hCq :
      SingleCompanionBlockForm C
        ((Polynomial.X - Polynomial.C (factorization.eigenvalue default)) ^
          (3 : Nat)) :=
    singleCompanionBlockForm_of_single_root_factorization_exponent_eq
      hC factorization hexp
  exact companion_hasJordan_of_linear_power_three
    (factorization.eigenvalue default)
    hCq

/--
A single-root factorization with exponent four is discharged by the quartic
linear-power companion check.
-/
theorem companion_hasJordan_of_single_root_exponent_four_factorization
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]}
    (hC : SingleCompanionBlockForm C p)
    (factorization : JordanSplitPolynomialFactorization K p)
    [Unique factorization.rootIdx]
    (hexp : factorization.exponent default = 4) :
    HasJordanMatrix C := by
  classical
  have hCq :
      SingleCompanionBlockForm C
        ((Polynomial.X - Polynomial.C (factorization.eigenvalue default)) ^
          (4 : Nat)) :=
    singleCompanionBlockForm_of_single_root_factorization_exponent_eq
      hC factorization hexp
  exact companion_hasJordan_of_linear_power_four
    (factorization.eigenvalue default)
    hCq

end MatDecompFormal.Instances
