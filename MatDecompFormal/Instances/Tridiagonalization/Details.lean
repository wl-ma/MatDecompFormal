import MatDecompFormal.Instances.Hessenberg.Details
import MatDecompFormal.Instances.Normal.Details
import MatDecompFormal.Instances.OrthogonalHessenberg.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Tridiagonalization Details

This file contains the target predicate for complex unitary tridiagonalization.
The implementation is routed through the square descent framework in later
files; the current target is the Hermitian/unitary version.
-/

variable {ι : Type*}

/-- Tridiagonal zero pattern with respect to finite-order ranks. -/
def IsTridiagonal
    {R : Type*} [Fintype ι] [LinearOrder ι] [Zero R]
    (T : Matrix ι ι R) : Prop :=
  ∀ i j,
    finiteOrderRank ι j + 1 < finiteOrderRank ι i ∨
      finiteOrderRank ι i + 1 < finiteOrderRank ι j →
    T i j = 0

/-- Matrix-level unitary tridiagonalization target. -/
def HasUnitaryTridiagonalization
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) : Prop :=
  ∃ Q : Matrix ι ι ℂ, ∃ T : Matrix ι ι ℂ,
    IsUnitaryMatrix Q ∧
    IsTridiagonal T ∧
    T.IsHermitian ∧
    A = Q * T * Qᴴ

/-- Universe-level predicate used by the square subtype induction framework. -/
def Tridiagonalization_P (x : SquareUniverse ℂ) : Prop :=
  x.A.IsHermitian → HasUnitaryTridiagonalization x.A

def Tridiagonalization_P_sub (x_sub : PosSquareUniverse ℂ) : Prop :=
  Tridiagonalization_P (x_sub : SquareUniverse ℂ)

@[simp] theorem tridiagonalization_P_compat (x_sub : PosSquareUniverse ℂ) :
    Tridiagonalization_P_sub x_sub ↔
      Tridiagonalization_P (x_sub : SquareUniverse ℂ) :=
  Iff.rfl

lemma isTridiagonal_subsingleton
    [Fintype ι] [LinearOrder ι] [Subsingleton ι]
    (A : Matrix ι ι ℂ) :
    IsTridiagonal A := by
  intro i j hij
  have hji : j = i := Subsingleton.elim j i
  rw [hji] at hij
  rcases hij with hij | hij
  · have hlt_self : finiteOrderRank ι i < finiteOrderRank ι i :=
      lt_trans (Nat.lt_succ_self _) hij
    exact False.elim (Nat.lt_irrefl _ hlt_self)
  · have hlt_self : finiteOrderRank ι i < finiteOrderRank ι i :=
      lt_trans (Nat.lt_succ_self _) hij
    exact False.elim (Nat.lt_irrefl _ hlt_self)

/-- Subsingleton matrices have a trivial unitary tridiagonalization. -/
theorem base_unitaryTridiagonalization_subsingleton
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Subsingleton ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A := by
  refine ⟨1, A, isUnitaryMatrix_one, ?_, hA, ?_⟩
  · exact isTridiagonal_subsingleton A
  · simp

lemma isHermitian_unitarySimilarity
    [Fintype ι] [DecidableEq ι]
    {Q A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) :
    (Qᴴ * A * Q).IsHermitian := by
  rw [Matrix.IsHermitian]
  calc
    (Qᴴ * A * Q)ᴴ = Qᴴ * Aᴴ * Q := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp [Matrix.mul_assoc]
    _ = Qᴴ * A * Q := by
      rw [hA.eq]

/-- Transport a tridiagonalization witness backward across a unitary similarity. -/
theorem tridiagonalization_transport_unitarySimilarity
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (Q A B : Matrix ι ι ℂ)
    (hQ : IsUnitaryMatrix Q)
    (hB : B = Qᴴ * A * Q)
    (hTri : HasUnitaryTridiagonalization B) :
    HasUnitaryTridiagonalization A := by
  rcases hTri with ⟨S, T, hS, hT, hTHerm, hEq⟩
  refine ⟨Q * S, T, isUnitaryMatrix_mul hQ hS, hT, hTHerm, ?_⟩
  calc
    A = (Q * Qᴴ) * A * (Q * Qᴴ) := by
      simp [hQ.2]
    _ = Q * (Qᴴ * A * Q) * Qᴴ := by
      simp [Matrix.mul_assoc]
    _ = Q * B * Qᴴ := by
      rw [← hB]
    _ = Q * (S * T * Sᴴ) * Qᴴ := by
      rw [hEq]
    _ = (Q * S) * T * (Q * S)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp [Matrix.mul_assoc]

theorem isTridiagonal_of_isUpperHessenberg_of_isHermitian
    [Fintype ι] [LinearOrder ι]
    {T : Matrix ι ι ℂ}
    (hHess : IsUpperHessenberg T) (hHerm : T.IsHermitian) :
    IsTridiagonal T := by
  intro i j hij
  rcases hij with hij | hij
  · exact hHess i j hij
  · have hji : T j i = 0 := hHess j i hij
    have happ := hHerm.apply i j
    rw [hji] at happ
    simpa using happ.symm

lemma unitary_similarity_target_eq
    [Fintype ι] [DecidableEq ι]
    {Q H A : Matrix ι ι ℂ}
    (hQ : IsUnitaryMatrix Q) (hEq : A = Q * H * Qᴴ) :
    H = Qᴴ * A * Q := by
  calc
    H = (Qᴴ * Q) * H * (Qᴴ * Q) := by
      simp [hQ.1]
    _ = Qᴴ * (Q * H * Qᴴ) * Q := by
      simp [Matrix.mul_assoc]
    _ = Qᴴ * A * Q := by
      rw [← hEq]

theorem hasUnitaryTridiagonalization_of_hasUnitaryHessenberg
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ}
    (hHerm : A.IsHermitian) (hA : HasUnitaryHessenberg A) :
    HasUnitaryTridiagonalization A := by
  rcases hA with ⟨Q, H, hQ, hHess, hEq⟩
  have hH_eq : H = Qᴴ * A * Q :=
    unitary_similarity_target_eq hQ hEq
  have hHHerm : H.IsHermitian := by
    rw [hH_eq]
    exact isHermitian_unitarySimilarity hHerm
  exact ⟨Q, H, hQ,
    isTridiagonal_of_isUpperHessenberg_of_isHermitian hHess hHHerm,
    hHHerm, hEq⟩

end MatDecompFormal.Instances
