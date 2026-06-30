/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.Jordan.GeneralizedCompanion
import MatDecompFormal.Instances.RationalCanonical.Details

universe u

namespace MatDecompFormal.Instances

open Matrix
open scoped Polynomial

/-!
# Elementary-Factor Companion Form

This file records the data shape used between rational canonical form and
generalized Jordan blocks.  The RCF-to-elementary-factor theorem is represented
by an explicitly suffixed bridge until the invariant-factor factorization
algebra is fully instantiated.
-/

/--
Data witnessing that a matrix is a block diagonal matrix of companion blocks
for elementary factors `pᵢ ^ kᵢ`, with each `pᵢ` monic and irreducible.
-/
structure ElementaryFactorData
    (K : Type u) [Field K] {ι : Type u}
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) where
  factorIdx : Type u
  [fintype_factorIdx : Fintype factorIdx]
  [decEq_factorIdx : DecidableEq factorIdx]
  [linearOrder_factorIdx : LinearOrder factorIdx]
  poly : factorIdx → K[X]
  poly_monic : ∀ i, (poly i).Monic
  poly_irreducible : ∀ i, Irreducible (poly i)
  exponent : factorIdx → Nat
  exponent_pos : ∀ i, 0 < exponent i
  blockIndex :
    ι ≃ (i : factorIdx) × Fin ((poly i ^ exponent i).natDegree)
  block_form :
    Matrix.reindex blockIndex blockIndex A =
      Matrix.blockDiagonal' fun i => companionMatrixFin (poly i ^ exponent i)

attribute [instance] ElementaryFactorData.fintype_factorIdx
attribute [instance] ElementaryFactorData.decEq_factorIdx
attribute [instance] ElementaryFactorData.linearOrder_factorIdx

/-- Matrix-level elementary-factor companion-form predicate. -/
def HasElementaryFactorCompanionForm
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  Nonempty (ElementaryFactorData K A)

/-- Elementary-factor companion block data gives generalized Jordan form. -/
theorem hasGeneralizedJordanMatrix_of_elementaryFactorData
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K}
    (data : ElementaryFactorData K A) :
    HasGeneralizedJordanMatrix A := by
  classical
  letI : LinearOrder ((i : data.factorIdx) × Fin ((data.poly i ^ data.exponent i).natDegree)) :=
    LinearOrder.lift'
      (Fintype.equivFin
        ((i : data.factorIdx) × Fin ((data.poly i ^ data.exponent i).natDegree)))
      (Fintype.equivFin
        ((i : data.factorIdx) × Fin ((data.poly i ^ data.exponent i).natDegree))).injective
  have hblocks :
      ∀ i : data.factorIdx,
        HasGeneralizedJordanMatrix (companionMatrixFin (data.poly i ^ data.exponent i)) := by
    intro i
    have hpow_monic : (data.poly i ^ data.exponent i).Monic :=
      (data.poly_monic i).pow (data.exponent i)
    have hnatDegree_pos : 0 < (data.poly i ^ data.exponent i).natDegree := by
      rw [(data.poly_monic i).natDegree_pow]
      exact Nat.mul_pos (data.exponent_pos i) (data.poly_irreducible i).natDegree_pos
    exact companion_power_hasGeneralizedJordan
      (K := K) (ι := Fin ((data.poly i ^ data.exponent i).natDegree))
      (data.exponent i) (data.poly_monic i) (data.poly_irreducible i)
      (data.exponent_pos i)
      (singleCompanionBlockForm_companionMatrixFin
        (data.poly i ^ data.exponent i) hpow_monic hnatDegree_pos)
  have hBlockDiagonal :
      HasGeneralizedJordanMatrix
        (Matrix.blockDiagonal' fun i =>
          companionMatrixFin (data.poly i ^ data.exponent i)) :=
    hasGeneralizedJordanMatrix_blockDiagonal'
      (fun i => companionMatrixFin (data.poly i ^ data.exponent i)) hblocks
  have hReindexed :
      HasGeneralizedJordanMatrix
        (Matrix.reindex data.blockIndex data.blockIndex A) := by
    rw [data.block_form]
    exact hBlockDiagonal
  have hBack := hasGeneralizedJordanMatrix_reindex (e := data.blockIndex.symm) hReindexed
  simpa [Matrix.reindex_apply] using hBack

/--
Squarefree elementary-factor companion form gives generalized Jordan form
without the companion-power bridge: every block is the exponent-one companion
case proved in `GeneralizedCompanion`.
-/
theorem hasGeneralizedJordanMatrix_of_elementaryFactorData_exponent_one
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K}
    (data : ElementaryFactorData K A)
    (hexp : ∀ i, data.exponent i = 1) :
    HasGeneralizedJordanMatrix A := by
  classical
  letI : LinearOrder ((i : data.factorIdx) × Fin ((data.poly i ^ data.exponent i).natDegree)) :=
    LinearOrder.lift'
      (Fintype.equivFin
        ((i : data.factorIdx) × Fin ((data.poly i ^ data.exponent i).natDegree)))
      (Fintype.equivFin
        ((i : data.factorIdx) × Fin ((data.poly i ^ data.exponent i).natDegree))).injective
  have hblocks :
      ∀ i : data.factorIdx,
        HasGeneralizedJordanMatrix (companionMatrixFin (data.poly i ^ data.exponent i)) := by
    intro i
    have hpow_monic : (data.poly i ^ data.exponent i).Monic :=
      (data.poly_monic i).pow (data.exponent i)
    have hnatDegree_pos : 0 < (data.poly i ^ data.exponent i).natDegree := by
      rw [(data.poly_monic i).natDegree_pow]
      exact Nat.mul_pos (data.exponent_pos i) (data.poly_irreducible i).natDegree_pos
    have hcomp :
        SingleCompanionBlockForm
          (companionMatrixFin (data.poly i ^ data.exponent i))
          (data.poly i ^ (1 : Nat)) := by
      simpa [hexp i] using
        (singleCompanionBlockForm_companionMatrixFin
          (data.poly i ^ data.exponent i) hpow_monic hnatDegree_pos)
    exact companion_power_one_hasGeneralizedJordan
      (K := K) (ι := Fin ((data.poly i ^ data.exponent i).natDegree))
      (data.poly_monic i) (data.poly_irreducible i) hcomp
  have hBlockDiagonal :
      HasGeneralizedJordanMatrix
        (Matrix.blockDiagonal' fun i =>
          companionMatrixFin (data.poly i ^ data.exponent i)) :=
    hasGeneralizedJordanMatrix_blockDiagonal'
      (fun i => companionMatrixFin (data.poly i ^ data.exponent i)) hblocks
  have hReindexed :
      HasGeneralizedJordanMatrix
        (Matrix.reindex data.blockIndex data.blockIndex A) := by
    rw [data.block_form]
    exact hBlockDiagonal
  have hBack := hasGeneralizedJordanMatrix_reindex (e := data.blockIndex.symm) hReindexed
  simpa [Matrix.reindex_apply] using hBack

/-- Elementary-factor companion form gives generalized Jordan form. -/
theorem hasGeneralizedJordanMatrix_of_elementaryFactorCompanionForm
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K}
    (hA : HasElementaryFactorCompanionForm A) :
    HasGeneralizedJordanMatrix A := by
  rcases hA with ⟨data⟩
  exact hasGeneralizedJordanMatrix_of_elementaryFactorData data

/-- Convert an explicit two-sided inverse into the matrix invertibility predicate. -/
lemma invertibleMatrix_of_hasMatrixInverse_elementary
    {K ι : Type u} [Field K] [Fintype ι] [DecidableEq ι]
    {P Pinv : Matrix ι ι K}
    (hInv : HasMatrixInverse P Pinv) :
    InvertibleMatrix P := by
  exact ⟨⟨P, Pinv, hInv.2, hInv.1⟩, rfl⟩

/--
Internal bridge from rational canonical form to elementary-factor companion
form.  This bridge is intentionally suffixed and must not appear in the final
public Jordan theorem.
-/
structure RationalCanonicalToElementaryBridge
    (K : Type u) [Field K] : Type (u + 1) where
  elementary_form_of_rational_canonical :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
      {A : Matrix ι ι K},
      IsRationalCanonicalMatrix A →
        HasElementaryFactorCompanionForm A

/--
Rational-canonical form gives generalized Jordan form once the
rational-canonical-to-elementary bridge is supplied.
-/
theorem hasGeneralizedJordanMatrix_of_hasRationalCanonical_elementary_bridge
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (elementaryBridge : RationalCanonicalToElementaryBridge K)
    {A : Matrix ι ι K}
    (hA : HasRationalCanonical A) :
    HasGeneralizedJordanMatrix A := by
  rcases hA with ⟨P, Pinv, C, hInv, hC, hEq⟩
  have hElementaryC : HasElementaryFactorCompanionForm C :=
    elementaryBridge.elementary_form_of_rational_canonical hC
  have hGeneralizedC : HasGeneralizedJordanMatrix C :=
    hasGeneralizedJordanMatrix_of_elementaryFactorCompanionForm hElementaryC
  rcases hGeneralizedC with ⟨S, J, hS, hJ, hCJ⟩
  refine ⟨P * S, J, ?_, hJ, ?_⟩
  · exact (invertibleMatrix_of_hasMatrixInverse_elementary hInv).mul hS
  · have hP : InvertibleMatrix P :=
      invertibleMatrix_of_hasMatrixInverse_elementary hInv
    haveI : Invertible P := hP.invertible
    haveI : Invertible S := hS.invertible
    have hPinv_eq : P⁻¹ = Pinv := by
      apply Matrix.inv_eq_right_inv
      exact hInv.2
    calc
      A = P * C * Pinv := hEq
      _ = P * (S * J * S⁻¹) * Pinv := by
        rw [hCJ]
      _ = P * (S * J * S⁻¹) * P⁻¹ := by
        rw [hPinv_eq]
      _ = (P * S) * J * (P * S)⁻¹ := by
        rw [Matrix.mul_inv_rev]
        simp [Matrix.mul_assoc]
end MatDecompFormal.Instances
