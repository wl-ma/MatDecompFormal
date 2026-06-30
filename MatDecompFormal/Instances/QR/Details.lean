/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Framework.Universe
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Components.Properties.Triangular
import Mathlib.LinearAlgebra.UnitaryGroup

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework
open MatDecompFormal.Components.Properties

section Presentation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [Semiring R]

/-- A matrix `Q` is orthogonal if `Qᵀ * Q = 1`. -/
def IsOrthogonalMatrix (Q : Matrix ι ι R) : Prop :=
  Qᵀ * Q = 1

/-- The ordered matrix product of a list, computed left-to-right: `l[0] * l[1] * ⋯ * l[n-1]`. -/
noncomputable def matrixProduct (l : List (Matrix ι ι R)) : Matrix ι ι R :=
  l.foldl (fun acc M => acc * M) 1

lemma matrixProduct_eq_prod (l : List (Matrix ι ι R)) :
    matrixProduct l = l.prod := by
  have hfold :
      ∀ (l : List (Matrix ι ι R)) (A : Matrix ι ι R),
        List.foldl (fun acc M => acc * M) A l = A * l.prod := by
    intro l
    induction l with
    | nil =>
        intro A
        simp
    | cons M l ih =>
        intro A
        simp [ih, Matrix.mul_assoc]
  simpa [matrixProduct] using hfold l 1

/-- `IsProductOf P Q` holds when `Q` is the left-to-right product of a finite list of matrices
each satisfying `P`. -/
def IsProductOf (P : Matrix ι ι R → Prop) (Q : Matrix ι ι R) : Prop :=
  ∃ l : List (Matrix ι ι R), (∀ M ∈ l, P M) ∧ matrixProduct l = Q

lemma isProductOf_one (P : Matrix ι ι R → Prop) :
    IsProductOf P (1 : Matrix ι ι R) := by
  refine ⟨[], ?_, ?_⟩
  · intro M hM
    cases hM
  · simp [matrixProduct]

lemma isProductOf_mul (P : Matrix ι ι R → Prop)
    {Q₁ Q₂ : Matrix ι ι R}
    (hQ₁ : IsProductOf P Q₁)
    (hQ₂ : IsProductOf P Q₂) :
    IsProductOf P (Q₁ * Q₂) := by
  rcases hQ₁ with ⟨l₁, hl₁, rfl⟩
  rcases hQ₂ with ⟨l₂, hl₂, rfl⟩
  refine ⟨l₁ ++ l₂, ?_, ?_⟩
  · intro M hM
    rcases List.mem_append.mp hM with hM | hM
    · exact hl₁ M hM
    · exact hl₂ M hM
  · unfold matrixProduct
    rw [List.foldl_append]
    let Q0 : Matrix ι ι R := List.foldl (fun acc M => acc * M) 1 l₁
    have hfold : ∀ (l : List (Matrix ι ι R)) (A B : Matrix ι ι R),
        List.foldl (fun acc M => acc * M) (A * B) l =
          A * List.foldl (fun acc M => acc * M) B l := by
      intro l
      induction l with
      | nil => intro A B; simp
      | cons M l ih =>
          intro A B
          simp [ih, Matrix.mul_assoc]
    simpa [Q0] using hfold l₂ Q0 1

lemma isProductOf_map
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Matrix ι ι R → Prop) (P' : Matrix κ κ R → Prop)
    (f : Matrix ι ι R → Matrix κ κ R)
    (h_one : f 1 = 1)
    (h_mul : ∀ A B, f (A * B) = f A * f B)
    (h_mem : ∀ M, P M → P' (f M))
    {Q : Matrix ι ι R}
    (hQ : IsProductOf P Q) :
    IsProductOf P' (f Q) := by
  rcases hQ with ⟨l, hl, hEq⟩
  refine ⟨l.map f, ?_, ?_⟩
  · intro M hM
    rcases List.mem_map.mp hM with ⟨N, hN, rfl⟩
    exact h_mem N (hl N hN)
  · subst hEq
    have hfold : ∀ (l : List (Matrix ι ι R)) (A : Matrix ι ι R),
        List.foldl (fun acc M => acc * M) (f A) (l.map f) =
          f (List.foldl (fun acc M => acc * M) A l) := by
      intro l
      induction l with
      | nil =>
          intro A
          simp
      | cons M l ih =>
          intro A
          rw [List.map, List.foldl]
          rw [← h_mul]
          exact ih (A * M)
    simpa [matrixProduct, h_one] using hfold l 1

lemma isProductOf_map_to_product
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Matrix ι ι R → Prop) (P' : Matrix κ κ R → Prop)
    (f : Matrix ι ι R → Matrix κ κ R)
    (h_one : f 1 = 1)
    (h_mul : ∀ A B, f (A * B) = f A * f B)
    (h_mem : ∀ M, P M → IsProductOf P' (f M))
    {Q : Matrix ι ι R}
    (hQ : IsProductOf P Q) :
    IsProductOf P' (f Q) := by
  rcases hQ with ⟨l, hl, hEq⟩
  subst Q
  induction l with
  | nil =>
      simpa [matrixProduct, h_one] using isProductOf_one P'
  | cons M l ih =>
      have hM : IsProductOf P' (f M) := h_mem M (hl M (by simp))
      have hl_tail : ∀ N ∈ l, P N := by
        intro N hN
        exact hl N (by simp [hN])
      have htail : IsProductOf P' (f (matrixProduct l)) := ih hl_tail
      have hprod : IsProductOf P' (f M * f (matrixProduct l)) :=
        isProductOf_mul P' hM htail
      simpa [matrixProduct_eq_prod, h_mul] using hprod

lemma isOrthogonalMatrix_one :
    IsOrthogonalMatrix (1 : Matrix ι ι R) := by
  simp [IsOrthogonalMatrix]

/-- The QR decomposition schema: factors are `(Q, R')` where `Q` is orthogonal and `R'` is
upper triangular, with `A = Q * R'`. -/
def QR_Schema [LinearOrder ι] : DecompositionSchema ι ι R where
  Factors := Matrix ι ι R × Matrix ι ι R
  property := fun (Q, R') => IsOrthogonalMatrix Q ∧ IsUpperTriangular R'
  equation := fun A (Q, R') => A = Q * R'

/-- `HasQR A` holds when `A` admits a QR decomposition, i.e., has a witness in `QR_Schema`. -/
def HasQR [LinearOrder ι] (A : Matrix ι ι R) : Prop :=
  HasDecomposition QR_Schema A

/-- `HasStructuredQR QProp A` holds when `A = Q * R'` with `Q` satisfying both `QProp` and the
orthogonality condition, and `R'` upper triangular.  The additional predicate `QProp` carries
structural information about the orthogonal factor (e.g., it is a product of Givens rotations). -/
abbrev HasStructuredQR [LinearOrder ι]
    (QProp : Matrix ι ι R → Prop) (A : Matrix ι ι R) : Prop :=
  ∃ Q R', QProp Q ∧
    IsOrthogonalMatrix Q ∧
    IsUpperTriangular R' ∧
    A = Q * R'

lemma hasQR_of_hasStructuredQR
    [LinearOrder ι]
    {QProp : Matrix ι ι R → Prop} {A : Matrix ι ι R}
    (hA : HasStructuredQR QProp A) :
    HasQR A := by
  rcases hA with ⟨Q, R', _hQprop, hQorth, hR, hEq⟩
  exact ⟨(Q, R'), ⟨hQorth, hR⟩, hEq⟩

/--
Product-level QR trace predicate.

This records a finite list of elementary factors whose product is the final
orthogonal factor. It is stronger than the structural `HasQR` target because
the factorization of `Q` is exposed in the proposition, but it does not by
itself claim step-by-step numerical pivot or stability properties.
-/
def QRProductTrace [LinearOrder ι]
    (StepProp : Matrix ι ι R → Prop) (A : Matrix ι ι R) : Prop :=
  ∃ steps : List (Matrix ι ι R), ∃ Q R' : Matrix ι ι R,
    (∀ M ∈ steps, StepProp M) ∧
    matrixProduct steps = Q ∧
    IsOrthogonalMatrix Q ∧
    IsUpperTriangular R' ∧
    A = Q * R'

lemma qrProductTrace_of_hasStructuredQR
    [LinearOrder ι]
    {StepProp : Matrix ι ι R → Prop} {A : Matrix ι ι R}
    (hA : HasStructuredQR (IsProductOf StepProp) A) :
    QRProductTrace StepProp A := by
  rcases hA with ⟨Q, R', hQprod, hQorth, hR, hEq⟩
  rcases hQprod with ⟨steps, hsteps, hprod⟩
  exact ⟨steps, Q, R', hsteps, hprod, hQorth, hR, hEq⟩

lemma hasStructuredQR_of_qrProductTrace
    [LinearOrder ι]
    {StepProp : Matrix ι ι R → Prop} {A : Matrix ι ι R}
    (hA : QRProductTrace StepProp A) :
    HasStructuredQR (IsProductOf StepProp) A := by
  rcases hA with ⟨steps, Q, R', hsteps, hprod, hQorth, hR, hEq⟩
  exact ⟨Q, R', ⟨steps, hsteps, hprod⟩, hQorth, hR, hEq⟩

lemma hasQR_of_qrProductTrace
    [LinearOrder ι]
    {StepProp : Matrix ι ι R → Prop} {A : Matrix ι ι R}
    (hA : QRProductTrace StepProp A) :
    HasQR A :=
  hasQR_of_hasStructuredQR (hasStructuredQR_of_qrProductTrace hA)

lemma base_qr_zero_dim_sq
    {x : SquareUniverse R} (h_zero : Fintype.card x.ι = 0) :
    HasQR x.A := by
  classical
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp h_zero
  refine ⟨(1, x.A), ?_, ?_⟩
  · constructor
    · simp [IsOrthogonalMatrix]
    · exact isUpperTriangular_of_subsingleton x.A
  · change x.A = (1 : Matrix x.ι x.ι R) * x.A
    simp

lemma base_qr_subsingleton
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Subsingleton ι]
    (A : Matrix ι ι R) :
    HasQR A := by
  refine ⟨(1, A), ?_, ?_⟩
  · constructor
    · simp [IsOrthogonalMatrix]
    · exact isUpperTriangular_of_subsingleton A
  · change A = (1 : Matrix ι ι R) * A
    simp

end Presentation

section CommSemiringPresentation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommSemiring R]


lemma isProductOf_transpose
    (P : Matrix ι ι R → Prop)
    (h_mem : ∀ M, P M → P Mᵀ)
    {Q : Matrix ι ι R}
    (hQ : IsProductOf P Q) :
    IsProductOf P Qᵀ := by
  rcases hQ with ⟨l, hl, hEq⟩
  refine ⟨(l.map Matrix.transpose).reverse, ?_, ?_⟩
  · intro M hM
    rcases List.mem_reverse.mp hM with hM
    rcases List.mem_map.mp hM with ⟨N, hN, rfl⟩
    exact h_mem N (hl N hN)
  · calc
      matrixProduct ((l.map Matrix.transpose).reverse)
          = ((l.map Matrix.transpose).reverse).prod := matrixProduct_eq_prod _
      _ = (l.prod)ᵀ := by rw [← Matrix.transpose_list_prod]
      _ = Qᵀ := by rw [← hEq, matrixProduct_eq_prod]

lemma isOrthogonalMatrix_mul {Q₁ Q₂ : Matrix ι ι R}
    (hQ₁ : IsOrthogonalMatrix Q₁)
    (hQ₂ : IsOrthogonalMatrix Q₂) :
    IsOrthogonalMatrix (Q₁ * Q₂) := by
  calc
    (Q₁ * Q₂)ᵀ * (Q₁ * Q₂)
        = Q₂ᵀ * (Q₁ᵀ * Q₁) * Q₂ := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Q₂ᵀ * Q₂ := by rw [hQ₁]; simp
    _ = 1 := hQ₂

end CommSemiringPresentation

section CommRingPresentation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

lemma isOrthogonalMatrix_transpose {Q : Matrix ι ι R}
    (hQ : IsOrthogonalMatrix Q) :
    IsOrthogonalMatrix Qᵀ := by
  have hmem : Q ∈ Matrix.orthogonalGroup ι R :=
    (Matrix.mem_orthogonalGroup_iff' (A := Q)).2 hQ
  have hqqt : Q * Qᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := Q)).1 hmem
  simpa [IsOrthogonalMatrix] using hqqt

end CommRingPresentation

end MatDecompFormal.Instances
