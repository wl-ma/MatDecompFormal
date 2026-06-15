import MatDecompFormal.Instances.Hessenberg.Boundary
import MatDecompFormal.Instances.Normal.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Orthogonal/Unitary Hessenberg Details

This file introduces the stronger Hessenberg target where the similarity
witness is unitary. The concrete public theorem is over `ℂ`; the underlying
unitary predicate itself is scalar-parametric.
-/

/-- Matrix-level unitary Hessenberg reduction target. -/
def HasUnitaryHessenberg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) : Prop :=
  ∃ Q : Matrix ι ι ℂ, ∃ H : Matrix ι ι ℂ,
    IsUnitaryMatrix Q ∧
    IsUpperHessenberg H ∧
    A = Q * H * Qᴴ

/--
Final-witness trace for complex unitary Hessenberg reduction.

The optional `tag` records which concrete boundary oracle route produced the
witness, while the theorem still exposes the final unitary factor, Hessenberg
matrix, and similarity equation.
-/
def UnitaryHessenbergWitnessData
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (tag : String) (A : Matrix ι ι ℂ) : Prop :=
  tag = tag ∧ ∃ Q : Matrix ι ι ℂ, ∃ H : Matrix ι ι ℂ,
    IsUnitaryMatrix Q ∧
    IsUpperHessenberg H ∧
    A = Q * H * Qᴴ

abbrev UnitaryHessenbergTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (tag : String) (A : Matrix ι ι ℂ) : Prop :=
  UnitaryHessenbergWitnessData tag A

theorem hasUnitaryHessenberg_of_witnessData
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {tag : String} {A : Matrix ι ι ℂ} :
    UnitaryHessenbergWitnessData tag A → HasUnitaryHessenberg A := by
  intro hA
  rcases hA with ⟨_htag, Q, H, hQ, hH, hEq⟩
  exact ⟨Q, H, hQ, hH, hEq⟩

theorem witnessData_of_hasUnitaryHessenberg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (tag : String) {A : Matrix ι ι ℂ} :
    HasUnitaryHessenberg A → UnitaryHessenbergWitnessData tag A := by
  intro hA
  rcases hA with ⟨Q, H, hQ, hH, hEq⟩
  exact ⟨rfl, Q, H, hQ, hH, hEq⟩

/--
Boundary-aware unitary Hessenberg target.

The same unitary similarity that reduces `A` must also transform the protected
boundary column into a first-entry-only column.
-/
def HasUnitaryHessenbergBoundary
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (c : Matrix ι Unit ℂ) : Prop :=
  ∃ Q : Matrix ι ι ℂ, ∃ H : Matrix ι ι ℂ,
    IsUnitaryMatrix Q ∧
    IsUpperHessenberg H ∧
    A = Q * H * Qᴴ ∧
    ∀ i : ι, i ≠ headElem (α := ι) → (Qᴴ * c) i () = 0

/-- Universe-level unitary Hessenberg predicate for the square driver. -/
def UnitaryHessenberg_P (x : SquareUniverse ℂ) : Prop :=
  HasUnitaryHessenberg x.A

/-- Boundary-universe unitary Hessenberg predicate. -/
def UnitaryHessenbergBoundary_P (x : HessenbergBoundaryUniverse.{u} ℂ) : Prop :=
  ∀ (_h : Nonempty x.ι), @HasUnitaryHessenbergBoundary x.ι x.fintype_ι
    x.decEq_ι x.linOrder_ι _h x.A x.c

/-- A unitary matrix gives the explicit inverse witness used by ordinary Hessenberg. -/
theorem hasMatrixInverse_of_isUnitaryMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Matrix ι ι ℂ} (hQ : IsUnitaryMatrix Q) :
    HasMatrixInverse Q Qᴴ :=
  hQ

/-- Forget the unitary condition from a unitary Hessenberg witness. -/
theorem hasHessenberg_of_hasUnitaryHessenberg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ} :
    HasUnitaryHessenberg A → HasHessenberg A := by
  intro hA
  rcases hA with ⟨Q, H, hQ, hH, hEq⟩
  exact ⟨Q, Qᴴ, H, hasMatrixInverse_of_isUnitaryMatrix hQ, hH, hEq⟩

/-- Forget the unitary condition from a boundary unitary Hessenberg witness. -/
theorem hasHessenbergBoundary_of_hasUnitaryHessenbergBoundary
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} {c : Matrix ι Unit ℂ} :
    HasUnitaryHessenbergBoundary A c → HasHessenbergBoundary A c := by
  intro hA
  rcases hA with ⟨Q, H, hQ, hH, hEq, hBoundary⟩
  exact ⟨Q, Qᴴ, H, hasMatrixInverse_of_isUnitaryMatrix hQ, hH, hEq, hBoundary⟩

/-- Subsingleton matrices have the trivial unitary Hessenberg decomposition. -/
theorem base_unitaryHessenberg_subsingleton
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Subsingleton ι]
    (A : Matrix ι ι ℂ) :
    HasUnitaryHessenberg A := by
  refine ⟨1, A, isUnitaryMatrix_one, ?_, ?_⟩
  · exact isUpperHessenberg_subsingleton A
  · simp

/-- Subsingleton matrices with a zero boundary column satisfy the boundary target. -/
theorem base_unitaryHessenbergBoundary_subsingleton_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    [Subsingleton ι] (A : Matrix ι ι ℂ) :
    HasUnitaryHessenbergBoundary A (0 : Matrix ι Unit ℂ) := by
  refine ⟨1, A, isUnitaryMatrix_one, ?_, ?_, ?_⟩
  · exact isUpperHessenberg_subsingleton A
  · simp
  · intro i hi
    exact False.elim (hi (Subsingleton.elim _ _))

/-- Transport a unitary Hessenberg witness backward across a unitary similarity. -/
theorem unitaryHessenberg_transport_unitarySimilarity
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (Q A B : Matrix ι ι ℂ)
    (hQ : IsUnitaryMatrix Q)
    (hB : B = Qᴴ * A * Q)
    (hHess : HasUnitaryHessenberg B) :
    HasUnitaryHessenberg A := by
  rcases hHess with ⟨S, H, hS, hH, hEq⟩
  refine ⟨Q * S, H, isUnitaryMatrix_mul hQ hS, hH, ?_⟩
  calc
    A = (Q * Qᴴ) * A * (Q * Qᴴ) := by
      simp [hQ.2]
    _ = Q * (Qᴴ * A * Q) * Qᴴ := by
      simp [Matrix.mul_assoc]
    _ = Q * B * Qᴴ := by
      rw [← hB]
    _ = Q * (S * H * Sᴴ) * Qᴴ := by
      rw [hEq]
    _ = (Q * S) * H * (Q * S)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp [Matrix.mul_assoc]

end MatDecompFormal.Instances
