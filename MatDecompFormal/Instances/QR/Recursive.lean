/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Framework.Reindex
import MatDecompFormal.Components.BlockAlgebra
import MatDecompFormal.Components.Lifting.LowLevel
import MatDecompFormal.Components.Properties.Reindex
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Instances.QR.Details
import MatDecompFormal.Instances.QR.Strategy

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Components
open MatDecompFormal.Components.Properties

variable {ι : Type*}
variable {R : Type*}

section SliceHelpers

lemma qr_headTailSlice_eq_tailBlock
    {ι : Type*} {R : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι R) :
    A.submatrix
        (fun i : QRTailIdx ι => headTailEquiv.symm (Sum.inr i))
        (fun j : QRTailIdx ι => headTailEquiv.symm (Sum.inr j)) =
      (Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A).toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.reindex_apply, headTailLexEquiv]


end SliceHelpers

section Helpers

variable [Semiring R]

lemma isOrthogonalMatrix_reindex
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (Q : Matrix α α R) :
    IsOrthogonalMatrix Q ↔ IsOrthogonalMatrix (Q.reindex e e) := by
  constructor
  · intro hQ
    have h := congrArg (Matrix.reindex e e) hQ
    simpa [IsOrthogonalMatrix, Matrix.transpose_reindex, Matrix.submatrix_mul_equiv] using h
  · intro hQ
    have h := congrArg (Matrix.reindex e.symm e.symm) hQ
    simpa [IsOrthogonalMatrix, Matrix.transpose_reindex, Matrix.submatrix_mul_equiv] using h

end Helpers

section TransportHelpers

section TransportHelpersCommSemiring

variable [CommSemiring R]

/-- Transport a QR decomposition back across an orthogonal left factor,
assuming transpose-side orthogonality has already been supplied. -/
theorem qr_transport_of_orthogonal_left_of_transpose
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (H A : Matrix ι ι R)
    (hH : IsOrthogonalMatrix H)
    (hHT : IsOrthogonalMatrix Hᵀ)
    (hQR : HasQR (H * A)) :
    HasQR A := by
  rcases hQR with ⟨⟨Q, R'⟩, hprop, hEq⟩
  refine ⟨(Hᵀ * Q, R'), ?_, ?_⟩
  · constructor
    · exact isOrthogonalMatrix_mul hHT hprop.1
    · exact hprop.2
  · calc
      A = (Hᵀ * H) * A := by
        have hHH := congrArg (fun M => M * A) hH
        simpa [IsOrthogonalMatrix, Matrix.mul_assoc] using hHH.symm
      _ = Hᵀ * (H * A) := by rw [Matrix.mul_assoc]
      _ = Hᵀ * (Q * R') := by rw [hEq]
      _ = (Hᵀ * Q) * R' := by rw [Matrix.mul_assoc]

end TransportHelpersCommSemiring

section TransportHelpersCommRing

variable [CommRing R]

/-- Transport a QR decomposition back across an orthogonal left factor. -/
theorem qr_transport_of_orthogonal_left
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (H A : Matrix ι ι R)
    (hH : IsOrthogonalMatrix H)
    (hQR : HasQR (H * A)) :
    HasQR A := by
  rcases hQR with ⟨⟨Q, R'⟩, hprop, hEq⟩
  refine ⟨(Hᵀ * Q, R'), ?_, ?_⟩
  · constructor
    · exact isOrthogonalMatrix_mul (isOrthogonalMatrix_transpose hH) hprop.1
    · exact hprop.2
  · calc
      A = (Hᵀ * H) * A := by
        have hHH := congrArg (fun M => M * A) hH
        simpa [IsOrthogonalMatrix, Matrix.mul_assoc] using hHH.symm
      _ = Hᵀ * (H * A) := by rw [Matrix.mul_assoc]
      _ = Hᵀ * (Q * R') := by rw [hEq]
      _ = (Hᵀ * Q) * R' := by rw [Matrix.mul_assoc]

end TransportHelpersCommRing

end TransportHelpers

section BlockHelpers

variable [Semiring R]

lemma isOrthogonalMatrix_blockDiag_one
    {β : Type*} [Fintype β] [DecidableEq β]
    {Q' : Matrix β β R} (hQ' : IsOrthogonalMatrix Q') :
    IsOrthogonalMatrix
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 Q' : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
  have hT :
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 Q' : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R)ᵀ =
        fromBlocks (1 : Matrix Unit Unit R) 0 0 Q'ᵀ := by
    simpa using
      (Matrix.fromBlocks_transpose
        (1 : Matrix Unit Unit R)
        (0 : Matrix Unit β R)
        (0 : Matrix β Unit R)
        Q')
  rw [IsOrthogonalMatrix, hT]
  calc
    (fromBlocks (1 : Matrix Unit Unit R) 0 0 Q'ᵀ : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) *
        (fromBlocks (1 : Matrix Unit Unit R) 0 0 Q' : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R)
        = fromBlocks (1 : Matrix Unit Unit R) 0 0 (Q'ᵀ * Q') := by
            simpa using
              (block_P_mul_A
                (A₁₁ := (1 : Matrix Unit Unit R))
                (A₁₂ := (0 : Matrix Unit β R))
                (A₂₁ := (0 : Matrix β Unit R))
                (A₂₂ := Q')
                (P' := Q'ᵀ))
    _ = fromBlocks (1 : Matrix Unit Unit R) 0 0 (1 : Matrix β β R) := by rw [hQ']
    _ = 1 := Matrix.fromBlocks_one

lemma isUpperTriangular_qrUpper
    {β : Type*} [LinearOrder β]
    (A₁₁ : Matrix Unit Unit R) (A₁₂ : Matrix Unit β R)
    {R' : Matrix β β R} (hR' : IsUpperTriangular R') :
    IsUpperTriangular
      (fromBlocks A₁₁ A₁₂ 0 R' : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
  dsimp [IsUpperTriangular, BlockTriangular] at hR' ⊢
  intro i j hij
  rcases i with (_ | i)
  · rcases j with (_ | j)
    · simpa using hij
    · exfalso
      exact Sum.not_inr_lt_inl hij
  · rcases j with (_ | j)
    · simp
    · exact hR' (Sum.inr_lt_inr_iff.mp hij)

end BlockHelpers

section RecursiveLift

variable [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
variable [Semiring R]

/-- Lift a QR decomposition of the tail slice back across a QR-ready head-tail split. -/
theorem qrReady_headTailSubmatrixLift
    (A : Matrix ι ι R)
    (hA : QRReady ι A)
    (hP :
      HasQR
        (A.submatrix
          (fun i : QRTailIdx ι => headTailEquiv.symm (Sum.inr i))
          (fun j : QRTailIdx ι => headTailEquiv.symm (Sum.inr j)))) :
    HasQR A := by
  classical
  let e : ι ≃ Unit ⊕ₗ QRTailIdx ι := headTailLexEquiv (α := ι)
  let Ablk : Matrix (Unit ⊕ₗ QRTailIdx ι) (Unit ⊕ₗ QRTailIdx ι) R := Matrix.reindex e e A
  have hSlice :
      A.submatrix
          (fun i : QRTailIdx ι => headTailEquiv.symm (Sum.inr i))
          (fun j : QRTailIdx ι => headTailEquiv.symm (Sum.inr j)) =
        Ablk.toBlocks₂₂ := by
    simpa [Ablk, e] using qr_headTailSlice_eq_tailBlock A
  have hA21 : Ablk.toBlocks₂₁ = 0 := by
    simpa [QRReady, Ablk, e] using hA
  rcases (show HasQR Ablk.toBlocks₂₂ by rwa [hSlice] at hP) with
    ⟨⟨Q', R'⟩, hProp', hEq'⟩
  let Qblk : Matrix (Unit ⊕ₗ QRTailIdx ι) (Unit ⊕ₗ QRTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 Q'
  let Rblk : Matrix (Unit ⊕ₗ QRTailIdx ι) (Unit ⊕ₗ QRTailIdx ι) R :=
    fromBlocks Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ 0 R'
  have hEqA :
      A =
        (Matrix.reindex e.symm e.symm Qblk) *
        (Matrix.reindex e.symm e.symm Rblk) := by
    simpa [Qblk, Rblk, Ablk, e] using
      (MatDecompFormal.Components.lift_two_factor_from_zero_block21
        (A := A)
        (e := e)
        (subF₁ := Q')
        (subF₂ := R')
        hA21 hEq')
  refine ⟨(Matrix.reindex e.symm e.symm Qblk, Matrix.reindex e.symm e.symm Rblk), ⟨?_, ?_⟩, hEqA⟩
  · exact
      (isOrthogonalMatrix_reindex
        (e := e)
        (Q := Matrix.reindex e.symm e.symm Qblk)).2
        (by simpa [Qblk] using isOrthogonalMatrix_blockDiag_one hProp'.1)
  · have hRblk : IsUpperTriangular Rblk := by
      rw [show Rblk = (fromBlocks Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ 0 R' :
        Matrix (Unit ⊕ₗ QRTailIdx ι) (Unit ⊕ₗ QRTailIdx ι) R) by rfl]
      have hUpper := hProp'.2
      dsimp [IsUpperTriangular, BlockTriangular] at hUpper ⊢
      intro i j hij
      rcases i with (_ | i)
      · rcases j with (_ | j)
        · simpa using hij
        · exfalso
          exact Sum.Lex.not_inr_lt_inl hij
      · rcases j with (_ | j)
        · simp
        · exact hUpper (Sum.Lex.inr_lt_inr_iff.mp hij)
    have hRreindexed : IsUpperTriangular ((Matrix.reindex e e) (Matrix.reindex e.symm e.symm Rblk)) := by
      simpa using hRblk
    exact
      (isUpperTriangular_reindex
        (e := e)
        (h_mono := headTailLexEquiv_strictMono (α := ι))
        (A := Matrix.reindex e.symm e.symm Rblk)).2 hRreindexed

end RecursiveLift

end MatDecompFormal.Instances
