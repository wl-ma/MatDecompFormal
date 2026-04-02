import MatDecompFormal.Framework.FinEnum
import MatDecompFormal.Instances.QR.Driver

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties
open MatDecompFormal.Framework

/-!
# QR External Bridge

This file provides the presentation-layer `FinEnum` view of QR together with
the bridge support that connects it to the internal `_fin` theorem exported
from `QR.lean`.
-/

section FinEnum

variable {ι : Type*} [FinEnum ι]

/-- Orthogonality predicate on the external `FinEnum` presentation layer. -/
def IsOrthogonalMatrix (Q : Matrix ι ι ℝ) : Prop :=
  Qᵀ * Q = 1

/-- External presentation schema for QR on `FinEnum`-indexed square matrices. -/
def QR_Schema : DecompositionSchema' ι ι ℝ where
  Factors := Matrix ι ι ℝ × Matrix ι ι ℝ
  property := fun (Q, R') => IsOrthogonalMatrix Q ∧ IsUpperTriangular R'
  equation := fun A (Q, R') => A = Q * R'

/-- External semantic wrapper for QR existence. -/
def HasQR (A : Matrix ι ι ℝ) : Prop :=
  HasDecomposition' (QR_Schema (ι := ι)) A

/--
Bridge lemma: `HasQR` is equivalent to `HasQR_fin` after reindexing through the
canonical `FinEnum`/`Fin` order isomorphism.
-/
lemma hasQR_reindex_iff
    (e : ι ≃o Fin (FinEnum.card ι)) (A : Matrix ι ι ℝ) :
    HasQR A ↔ HasQR_fin (A.reindex e.toEquiv e.toEquiv) := by
  constructor
  · rintro ⟨⟨Q, R'⟩, ⟨hQ, hR⟩, hEq⟩
    let Q' := Q.reindex e.toEquiv e.toEquiv
    let R'' := R'.reindex e.toEquiv e.toEquiv
    refine ⟨⟨Q', R''⟩, ?_, ?_⟩
    · constructor
      · dsimp [IsOrthogonalMatrix_fin, Q']
        calc
          Q'ᵀ * Q' = (Qᵀ * Q).reindex e.toEquiv e.toEquiv := by
            simpa [Q', Matrix.transpose_reindex, submatrix_mul_equiv] using
              (submatrix_mul_equiv Qᵀ Q e.symm.toEquiv e.symm.toEquiv e.symm.toEquiv)
          _ = 1 := by
            have h := congrArg (Matrix.reindex e.toEquiv e.toEquiv) hQ
            calc
              (Qᵀ * Q).reindex e.toEquiv e.toEquiv =
                  (1 : Matrix ι ι ℝ).reindex e.toEquiv e.toEquiv := h
              _ = 1 := by
                simpa using (submatrix_one_equiv e.symm.toEquiv : (1 : Matrix ι ι ℝ).submatrix
                  e.symm.toEquiv e.symm.toEquiv = 1)
      · have h_mono : StrictMono e.toEquiv := e.strictMono
        exact (isUpperTriangular_reindex e.toEquiv h_mono R').1 hR
    · dsimp [QR_Schema]
      calc
        A.reindex e.toEquiv e.toEquiv = (Q * R').reindex e.toEquiv e.toEquiv := by
          exact congrArg (Matrix.reindex e.toEquiv e.toEquiv) hEq
        _ = Q' * R'' := by
          simpa [Q', R'', submatrix_mul_equiv] using
            (submatrix_mul_equiv Q R' e.symm.toEquiv e.symm.toEquiv e.symm.toEquiv).symm
  · rintro ⟨⟨Q', R'⟩, ⟨hQ', hR'⟩, hEq⟩
    let Q := Q'.reindex e.symm.toEquiv e.symm.toEquiv
    let R'' := R'.reindex e.symm.toEquiv e.symm.toEquiv
    refine ⟨⟨Q, R''⟩, ?_, ?_⟩
    · constructor
      · dsimp [IsOrthogonalMatrix, Q]
        calc
          Qᵀ * Q = (Q'ᵀ * Q').reindex e.symm.toEquiv e.symm.toEquiv := by
            simpa [Q, Matrix.transpose_reindex, submatrix_mul_equiv] using
              (submatrix_mul_equiv Q'ᵀ Q' e.toEquiv e.toEquiv e.toEquiv)
          _ = 1 := by
            have h := congrArg (Matrix.reindex e.symm.toEquiv e.symm.toEquiv) hQ'
            calc
              (Q'ᵀ * Q').reindex e.symm.toEquiv e.symm.toEquiv =
                  (1 : Matrix (Fin (FinEnum.card ι)) (Fin (FinEnum.card ι)) ℝ).reindex
                    e.symm.toEquiv e.symm.toEquiv := h
              _ = 1 := by
                simpa using
                  (submatrix_one_equiv e.toEquiv :
                    (1 : Matrix (Fin (FinEnum.card ι)) (Fin (FinEnum.card ι)) ℝ).submatrix
                      e.toEquiv e.toEquiv = 1)
      · have h_mono : StrictMono e.symm.toEquiv := e.symm.strictMono
        exact (isUpperTriangular_reindex e.symm.toEquiv h_mono R').1 hR'
    · dsimp [QR_Schema]
      calc
        A = ((A.reindex e.toEquiv e.toEquiv).reindex e.symm.toEquiv e.symm.toEquiv) := by
          ext i j
          simp
        _ = (Q' * R').reindex e.symm.toEquiv e.symm.toEquiv := by
          simpa [QR_Schema_fin] using
            congrArg (Matrix.reindex e.symm.toEquiv e.symm.toEquiv) hEq
        _ = Q * R'' := by
          simpa [Q, R'', submatrix_mul_equiv] using
            (submatrix_mul_equiv Q' R' e.toEquiv e.toEquiv e.toEquiv).symm
end FinEnum

end MatDecompFormal.Instances
