/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Components.Lifting.LowLevel
import MatDecompFormal.Components.Properties.Reindex
import MatDecompFormal.Instances.PLU.Strategy
import MatDecompFormal.Instances.PLU.Details

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Components
open MatDecompFormal.Components.Properties

/-!
# PLU Direct Support

This file isolates the remaining non-framework mathematical content for PLU as
 the single lift-side hook still needed by the current head-tail strategy core.
It also contains concrete helper lemmas for the zero-column branch.
-/

variable {ι : Type} {R : Type*} [Fintype ι] [LinearOrder ι]

section ZeroColumnHelpers

variable [Semiring R] [Nonempty ι]

lemma headTailSlice_eq_tailBlock
    {ι : Type} {R : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι R) :
    A.submatrix
        (fun i : PLUTailIdx ι => headTailEquiv.symm (Sum.inr i))
        (fun j : PLUTailIdx ι => headTailEquiv.symm (Sum.inr j)) =
      (Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A).toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.reindex_apply, headTailLexEquiv]

lemma zeroColumn_headTail_blocks
    (A : Matrix ι ι R)
    (hZero : PLUZeroColumnReady ι A) :
    let Ablk := Matrix.reindex (headTailLexEquiv (α := ι)) (headTailLexEquiv (α := ι)) A
    Ablk.toBlocks₁₁ = 0 ∧ Ablk.toBlocks₂₁ = 0 := by
  classical
  dsimp
  constructor
  · ext i j
    have hhead := hZero (headElem (α := ι))
    simpa [Matrix.toBlocks₁₁, Matrix.reindex_apply, headTailLexEquiv_symm_apply_inl] using hhead
  · ext i j
    have hcol := hZero i
    simpa [Matrix.toBlocks₂₁, Matrix.reindex_apply, headTailLexEquiv_symm_apply_inl] using hcol

lemma isPermutation_blockDiag_one
    {β : Type*} [Fintype β] [DecidableEq β]
    {P' : Matrix β β R} (hP' : IsPermutation P') :
    IsPermutation
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 P' : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
  classical
  rcases hP' with ⟨σ, rfl⟩
  let Aplain : Matrix (Unit ⊕ β) (Unit ⊕ β) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 ((Equiv.toPEquiv σ).toMatrix)
  have hplain : IsPermutation Aplain := by
    refine ⟨Equiv.Perm.sumCongr (Equiv.refl Unit) σ, ?_⟩
    ext i j
    cases i <;> cases j <;> simp [Aplain]
  have hreindex :
      (Aplain.reindex (sumToLexEquiv Unit β) (sumToLexEquiv Unit β)) =
        (fromBlocks (1 : Matrix Unit Unit R) 0 0 ((Equiv.toPEquiv σ).toMatrix) :
          Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
    ext i j
    cases i <;> cases j <;> rfl
  have hlex :
      IsPermutation (Aplain.reindex (sumToLexEquiv Unit β) (sumToLexEquiv Unit β)) :=
    (isPermutation_reindex (e := sumToLexEquiv Unit β) (A := Aplain)).1 hplain
  simpa [hreindex] using hlex

lemma isUpperTriangular_zeroColumnUpper
    {β : Type*} [LinearOrder β]
    (A₁₂ : Matrix Unit β R) {U' : Matrix β β R} (hU' : IsUpperTriangular U') :
    IsUpperTriangular
      (fromBlocks (0 : Matrix Unit Unit R) A₁₂ 0 U' : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
  dsimp [IsUpperTriangular, BlockTriangular] at hU' ⊢
  intro i j hij
  rcases i with (_ | i)
  · rcases j with (_ | j)
    · simpa using hij
    · exfalso
      simpa using hij
  · rcases j with (_ | j)
    · simp
    · simpa using hU' (by simpa using hij)

lemma isUnitLowerTriangular_blockDiag_one
    {β : Type*} [LinearOrder β]
    {L' : Matrix β β R} (hL' : IsUnitLowerTriangular L') :
    IsUnitLowerTriangular
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 L' : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
  rcases hL' with ⟨hLower, hdiag⟩
  constructor
  · dsimp [IsLowerTriangular, IsUpperTriangular, BlockTriangular] at hLower ⊢
    intro i j hij
    rcases i with (_ | i)
    · rcases j with (_ | j)
      · simpa using hij
      · simp
    · rcases j with (_ | j)
      · simp
      · exact hLower (by simpa using hij)
  · funext x
    rcases x with (_ | x)
    · simp
    · have hx := congrArg (fun f => f x) hdiag
      simpa using hx


end ZeroColumnHelpers

section PivotReadyHelpers

variable [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
lemma pivotLowerFactor_mul_headBlock
    [DivisionRing R]
    (A : Matrix ι ι R)
    (hPivot : PLUPivotReady ι A) :
    let A' := pluHeadTailPlain ι A
    pluPivotLowerFactor ι A * A'.toBlocks₁₁ = A'.toBlocks₂₁ := by
  classical
  ext i j
  cases j
  have h_inv :
      (A (headElem (α := ι)) (headElem (α := ι)))⁻¹ * A (headElem (α := ι)) (headElem (α := ι)) = 1 :=
    inv_mul_cancel₀ hPivot
  simp [pluPivotLowerFactor, pluHeadTailPlain, pluHeadInv, Matrix.mul_apply,
    Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.reindex_apply, h_inv, mul_assoc]

lemma isUnitLowerTriangular_pivotLower
    [Semiring R]
    {β : Type*} [LinearOrder β]
    (L₂₁ : Matrix β Unit R) {L' : Matrix β β R} (hL' : IsUnitLowerTriangular L') :
    IsUnitLowerTriangular
      (fromBlocks (1 : Matrix Unit Unit R) 0 L₂₁ L' : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
  rcases hL' with ⟨hLower, hdiag⟩
  constructor
  · dsimp [IsLowerTriangular, IsUpperTriangular, BlockTriangular] at hLower ⊢
    intro i j hij
    rcases i with (_ | i)
    · rcases j with (_ | j)
      · simpa using hij
      · exfalso
        simpa using hij
    · rcases j with (_ | j)
      · simp
      · exact hLower (by simpa using hij)
  · funext x
    rcases x with (_ | x)
    · simp
    · have hx := congrArg (fun f => f x) hdiag
      simpa using hx

lemma isUpperTriangular_pivotUpper
    [Semiring R]
    {β : Type*} [LinearOrder β]
    (A₁₁ : Matrix Unit Unit R) (A₁₂ : Matrix Unit β R) {U' : Matrix β β R}
    (hU' : IsUpperTriangular U') :
    IsUpperTriangular
      (fromBlocks A₁₁ A₁₂ 0 U' : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) R) := by
  dsimp [IsUpperTriangular, BlockTriangular] at hU' ⊢
  intro i j hij
  rcases i with (_ | i)
  · rcases j with (_ | j)
    · simpa using hij
    · exfalso
      simpa using hij
  · rcases j with (_ | j)
    · simp
    · exact hU' (by simpa using hij)


lemma pivotReady_plain_equation
    [DivisionRing R]
    (A : Matrix ι ι R)
    (hPivot : PLUPivotReady ι A)
    {P' L' U' : Matrix (PLUTailIdx ι) (PLUTailIdx ι) R}
    (hEq' : P' * pluSchurSlice ι A = L' * U') :
    let Aplain := pluHeadTailPlain ι A
    let l := pluPivotLowerFactor ι A
    let L21 : Matrix (PLUTailIdx ι) Unit R := P' * l
    let Pplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R :=
      fromBlocks (1 : Matrix Unit Unit R) 0 0 P'
    let Lplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R :=
      fromBlocks (1 : Matrix Unit Unit R) 0 L21 L'
    let Uplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R :=
      fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ 0 U'
    Pplain * Aplain = Lplain * Uplain := by
  classical
  dsimp
  let Aplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R := pluHeadTailPlain ι A
  let l : Matrix (PLUTailIdx ι) Unit R := pluPivotLowerFactor ι A
  let L21 : Matrix (PLUTailIdx ι) Unit R := P' * l
  have hlA11 : l * Aplain.toBlocks₁₁ = Aplain.toBlocks₂₁ := by
    simpa [l, Aplain] using pivotLowerFactor_mul_headBlock A hPivot
  have hA21_factor : L21 * Aplain.toBlocks₁₁ = P' * Aplain.toBlocks₂₁ := by
    calc
      (P' * l) * Aplain.toBlocks₁₁ = P' * (l * Aplain.toBlocks₁₁) := by
        rw [Matrix.mul_assoc]
      _ = P' * Aplain.toBlocks₂₁ := by
        rw [hlA11]
  have hSchur_restore : pluSchurSlice ι A + l * Aplain.toBlocks₁₂ = Aplain.toBlocks₂₂ := by
    dsimp [pluSchurSlice, pluPivotLowerFactor, pluHeadTailPlain, l, Aplain]
    abel
  have hA22_factor : L21 * Aplain.toBlocks₁₂ + L' * U' = P' * Aplain.toBlocks₂₂ := by
    calc
      (P' * l) * Aplain.toBlocks₁₂ + L' * U' = (P' * l) * Aplain.toBlocks₁₂ + P' * pluSchurSlice ι A := by
        rw [hEq']
      _ = P' * (l * Aplain.toBlocks₁₂) + P' * pluSchurSlice ι A := by
        rw [Matrix.mul_assoc]
      _ = P' * (l * Aplain.toBlocks₁₂ + pluSchurSlice ι A) := by
        rw [← Matrix.mul_add]
      _ = P' * Aplain.toBlocks₂₂ := by
        rw [add_comm, hSchur_restore]
  let Pplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 P'
  let Lplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 L21 L'
  let Uplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R :=
    fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ 0 U'
  calc
    Pplain * Aplain
        = Pplain *
            (fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ :
              Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R) := by
              simpa using congrArg (fun M => Pplain * M) (fromBlocks_toBlocks Aplain).symm
    _ = fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂
          (P' * Aplain.toBlocks₂₁) (P' * Aplain.toBlocks₂₂) := by
          simpa [Pplain] using
            (block_P_mul_A
              (A₁₁ := Aplain.toBlocks₁₁)
              (A₁₂ := Aplain.toBlocks₁₂)
              (A₂₁ := Aplain.toBlocks₂₁)
              (A₂₂ := Aplain.toBlocks₂₂)
              (P' := P'))
    _ = fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂
          (L21 * Aplain.toBlocks₁₁) (L21 * Aplain.toBlocks₁₂ + L' * U') := by
          rw [← hA21_factor, ← hA22_factor]
    _ = Lplain * Uplain := by
          symm
          simpa [Lplain, Uplain, L21] using
            (block_L_mul_U
              (L₂₁ := L21)
              (L' := L')
              (U₁₁ := Aplain.toBlocks₁₁)
              (U₁₂ := Aplain.toBlocks₁₂)
              (U' := U'))


end PivotReadyHelpers

section ZeroColumnLift

variable [DecidableEq ι] [Semiring R] [Nonempty ι]

/--
Concrete lift for the zero-column branch of the active head-tail PLU strategy.
-/
theorem zeroColumn_pluHeadTailSubmatrixLift
    (A : Matrix ι ι R)
    (hZero : PLUZeroColumnReady ι A)
    (hP :
      HasPLU
        (A.submatrix
          (fun i : PLUTailIdx ι => headTailEquiv.symm (Sum.inr i))
          (fun j : PLUTailIdx ι => headTailEquiv.symm (Sum.inr j)))) :
    HasPLU A := by
  classical
  let e0 : ι ≃ Unit ⊕ PLUTailIdx ι := headTailEquiv (α := ι)
  let s : Unit ⊕ PLUTailIdx ι ≃ Unit ⊕ₗ PLUTailIdx ι := sumToLexEquiv Unit (PLUTailIdx ι)
  let e : ι ≃ Unit ⊕ₗ PLUTailIdx ι := headTailLexEquiv (α := ι)
  let Aplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R := Matrix.reindex e0 e0 A
  have hSlice :
      A.submatrix
          (fun i : PLUTailIdx ι => headTailEquiv.symm (Sum.inr i))
          (fun j : PLUTailIdx ι => headTailEquiv.symm (Sum.inr j)) =
        Aplain.toBlocks₂₂ := by
    simpa [Aplain, e0] using
      (submatrix_inr_inr_eq_toBlocks₂₂ e0 e0 A)
  have hPplain : HasPLU Aplain.toBlocks₂₂ := by
    rwa [hSlice] at hP
  have hA11 : Aplain.toBlocks₁₁ = 0 := by
    ext i j
    have h := hZero (e0.symm (Sum.inl i))
    simpa [Aplain, e0, Matrix.toBlocks₁₁, Matrix.reindex_apply] using h
  have hA21 : Aplain.toBlocks₂₁ = 0 := by
    ext i j
    have h := hZero (e0.symm (Sum.inr i))
    simpa [Aplain, e0, Matrix.toBlocks₂₁, Matrix.reindex_apply] using h
  rcases hPplain with ⟨⟨P', L', U'⟩, ⟨hPerm', hL', hU'⟩, hEq'⟩
  let Pplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 P'
  let Lplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 L'
  let Uplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R :=
    fromBlocks (0 : Matrix Unit Unit R) Aplain.toBlocks₁₂ 0 U'
  have hPlainEq : Pplain * Aplain = Lplain * Uplain := by
    calc
      Pplain * Aplain
          = Pplain *
              (fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ :
                Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R) := by
                simpa using congrArg (fun M => Pplain * M) (fromBlocks_toBlocks Aplain).symm
      _ = fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂
            (P' * Aplain.toBlocks₂₁) (P' * Aplain.toBlocks₂₂) := by
            simpa [Pplain] using
              (block_P_mul_A
                (A₁₁ := Aplain.toBlocks₁₁)
                (A₁₂ := Aplain.toBlocks₁₂)
                (A₂₁ := Aplain.toBlocks₂₁)
                (A₂₂ := Aplain.toBlocks₂₂)
                (P' := P'))
      _ = fromBlocks (0 : Matrix Unit Unit R) Aplain.toBlocks₁₂ 0 (P' * Aplain.toBlocks₂₂) := by
            rw [hA11, hA21]
            simp
      _ = fromBlocks (0 : Matrix Unit Unit R) Aplain.toBlocks₁₂ 0 (L' * U') := by
            rw [hEq']
      _ = Lplain * Uplain := by
            symm
            simpa [Lplain, Uplain] using
              (block_diag_L_mul_block_U
                (L' := L')
                (U₁₂ := Aplain.toBlocks₁₂)
                (U' := U'))
  let Pblk : Matrix (Unit ⊕ₗ PLUTailIdx ι) (Unit ⊕ₗ PLUTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 P'
  let Lblk : Matrix (Unit ⊕ₗ PLUTailIdx ι) (Unit ⊕ₗ PLUTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 0 L'
  let Ublk : Matrix (Unit ⊕ₗ PLUTailIdx ι) (Unit ⊕ₗ PLUTailIdx ι) R :=
    fromBlocks (0 : Matrix Unit Unit R) (Matrix.reindex s s Aplain).toBlocks₁₂ 0 U'
  have hAblk : Matrix.reindex s s Aplain = Matrix.reindex e e A := by
    ext i j
    simp [Aplain, e0, e, s, headTailLexEquiv, Matrix.reindex_apply]
  have hUblk_def :
      Ublk = fromBlocks (0 : Matrix Unit Unit R) (Matrix.reindex e e A).toBlocks₁₂ 0 U' := by
    ext i j
    rcases i with (_ | i) <;> rcases j with (_ | j) <;>
      simp [Ublk, hAblk]
  have hBlkEq : Pblk * Matrix.reindex e e A = Lblk * Ublk := by
    have hReindexed := congrArg (Matrix.reindex s s) hPlainEq
    have : Pblk * Matrix.reindex s s Aplain = Lblk * Ublk := by
      simpa [Pblk, Lblk, Ublk] using hReindexed
    rw [hAblk] at this
    exact this
  have hTransport :=
    schur_case_transport_back
      (A := A)
      (e := e)
      (P_blk := Pblk)
      (L_blk := Lblk)
      (U_blk := Ublk)
      hBlkEq
  have hPermBlk : IsPermutation Pblk :=
    isPermutation_blockDiag_one hPerm'
  have hLblk : IsUnitLowerTriangular Lblk := by
    rw [show Lblk =
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 L' :
        Matrix (Unit ⊕ₗ PLUTailIdx ι) (Unit ⊕ₗ PLUTailIdx ι) R) by rfl]
    constructor
    · dsimp [IsLowerTriangular, IsUpperTriangular, BlockTriangular] at hL' ⊢
      rcases hL' with ⟨hLower, _⟩
      intro i j hij
      rcases i with (_ | i)
      · rcases j with (_ | j)
        · simpa using hij
        · simp
      · rcases j with (_ | j)
        · simp
        · exact hLower (Sum.Lex.inr_lt_inr_iff.mp hij)
    · rcases hL' with ⟨_, hdiag⟩
      funext x
      rcases x with (_ | x)
      · simp
      · have hx := congrArg (fun f => f x) hdiag
        simpa using hx
  have hUblk : IsUpperTriangular Ublk := by
    rw [hUblk_def]
    dsimp [IsUpperTriangular, BlockTriangular] at hU' ⊢
    intro i j hij
    rcases i with (_ | i)
    · rcases j with (_ | j)
      · simpa using hij
      · exfalso
        exact Sum.Lex.not_inr_lt_inl hij
    · rcases j with (_ | j)
      · simp
      · exact hU' (Sum.Lex.inr_lt_inr_iff.mp hij)
  have hPerm : IsPermutation (Matrix.reindex e.symm e.symm Pblk) := by
    exact
      (isPermutation_reindex (e := e) (A := Matrix.reindex e.symm e.symm Pblk)).2
        (by simpa using hPermBlk)
  have hL : IsUnitLowerTriangular (Matrix.reindex e.symm e.symm Lblk) := by
    exact
      (isUnitLowerTriangular_reindex
        (e := e)
        (h_mono := headTailLexEquiv_strictMono (α := ι))
        (A := Matrix.reindex e.symm e.symm Lblk)).2
        (by simpa using hLblk)
  have hU : IsUpperTriangular (Matrix.reindex e.symm e.symm Ublk) := by
    exact
      (isUpperTriangular_reindex
        (e := e)
        (h_mono := headTailLexEquiv_strictMono (α := ι))
        (A := Matrix.reindex e.symm e.symm Ublk)).2
        (by simpa using hUblk)
  refine ⟨(Matrix.reindex e.symm e.symm Pblk,
      Matrix.reindex e.symm e.symm Lblk,
      Matrix.reindex e.symm e.symm Ublk), ?_, ?_⟩
  · exact ⟨hPerm, hL, hU⟩
  · exact hTransport

end ZeroColumnLift

section PivotLift

/--
Concrete lift for the pivot-ready Schur-complement branch of the active
head-tail PLU strategy.
-/

theorem nontrivial_pivotReady_pluHeadTailSchurLift
    {ι : Type} [DivisionRing R] (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι) (nι : Nonempty ι)
    [Nontrivial ι]
    (A : Matrix ι ι R)
    (hPivot : PLUPivotReady ι A)
    (hP : HasPLU (pluSchurSlice ι A)) :
    HasPLU A := by
  classical
  rcases hP with ⟨⟨P', L', U'⟩, ⟨hPerm', hL', hU'⟩, hEq'⟩
  let e0 : ι ≃ Unit ⊕ PLUTailIdx ι := headTailEquiv (α := ι)
  let s : Unit ⊕ PLUTailIdx ι ≃ Unit ⊕ₗ PLUTailIdx ι := sumToLexEquiv Unit (PLUTailIdx ι)
  let e : ι ≃ Unit ⊕ₗ PLUTailIdx ι := headTailLexEquiv (α := ι)
  let Aplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R := pluHeadTailPlain ι A
  let Ablk : Matrix (Unit ⊕ₗ PLUTailIdx ι) (Unit ⊕ₗ PLUTailIdx ι) R := Matrix.reindex e e A
  let l : Matrix (PLUTailIdx ι) Unit R := pluPivotLowerFactor ι A
  let L21 : Matrix (PLUTailIdx ι) Unit R := P' * l
  let Pplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R := fromBlocks (1 : Matrix Unit Unit R) 0 0 P'
  let Lplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R := fromBlocks (1 : Matrix Unit Unit R) 0 L21 L'
  let Uplain : Matrix (Unit ⊕ PLUTailIdx ι) (Unit ⊕ PLUTailIdx ι) R := fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ 0 U'
  let Pblk : Matrix (Unit ⊕ₗ PLUTailIdx ι) (Unit ⊕ₗ PLUTailIdx ι) R := fromBlocks (1 : Matrix Unit Unit R) 0 0 P'
  let Lblk : Matrix (Unit ⊕ₗ PLUTailIdx ι) (Unit ⊕ₗ PLUTailIdx ι) R := fromBlocks (1 : Matrix Unit Unit R) 0 L21 L'
  let Ublk : Matrix (Unit ⊕ₗ PLUTailIdx ι) (Unit ⊕ₗ PLUTailIdx ι) R := fromBlocks Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ 0 U'
  have hPlainEq := pivotReady_plain_equation A hPivot hEq'
  have hAblk : Matrix.reindex s s Aplain = Ablk := by
    simpa [Aplain, Ablk, e0, e, s, headTailLexEquiv] using
      (reindex_reindex e0 e0 s s A)
  have hA11blk : Aplain.toBlocks₁₁ = Ablk.toBlocks₁₁ := by
    simpa using congrArg Matrix.toBlocks₁₁ hAblk
  have hA12blk : Aplain.toBlocks₁₂ = Ablk.toBlocks₁₂ := by
    simpa using congrArg Matrix.toBlocks₁₂ hAblk
  have hPblk_def : Matrix.reindex s s Pplain = Pblk := by
    simpa [Pplain, Pblk] using
      (reindex_sumToLex_fromBlocks
        (A₁₁ := (1 : Matrix Unit Unit R)) (A₁₂ := 0) (A₂₁ := 0) (A₂₂ := P'))
  have hLblk_def : Matrix.reindex s s Lplain = Lblk := by
    simpa [Lplain, Lblk] using
      (reindex_sumToLex_fromBlocks
        (A₁₁ := (1 : Matrix Unit Unit R)) (A₁₂ := 0) (A₂₁ := L21) (A₂₂ := L'))
  have hUblk_def : Matrix.reindex s s Uplain = Ublk := by
    simpa [Uplain, Ublk, hA11blk, hA12blk] using
      (reindex_sumToLex_fromBlocks
        (A₁₁ := Aplain.toBlocks₁₁) (A₁₂ := Aplain.toBlocks₁₂) (A₂₁ := 0) (A₂₂ := U'))
  have hReindexed := congrArg (Matrix.reindex s s) hPlainEq
  have hBlkEq : Pblk * Ablk = Lblk * Ublk := by
    rw [← hPblk_def, ← hAblk, ← hLblk_def, ← hUblk_def]
    simpa using hReindexed
  have hTransport :=
    schur_case_transport_back
      (A := A)
      (e := e)
      (P_blk := Pblk)
      (L_blk := Lblk)
      (U_blk := Ublk)
      hBlkEq
  have hPermBlk : IsPermutation Pblk := by
    simpa [Pblk] using isPermutation_blockDiag_one (β := PLUTailIdx ι) hPerm'
  have hLblk : IsUnitLowerTriangular Lblk := by
    rcases hL' with ⟨hLower, hdiag⟩
    constructor
    · dsimp [IsLowerTriangular, IsUpperTriangular, BlockTriangular, Lblk] at hLower ⊢
      intro i j hij
      rcases i with (_ | i)
      · rcases j with (_ | j)
        · simpa using hij
        · exfalso
          exact Sum.Lex.not_inr_lt_inl hij
      · rcases j with (_ | j)
        · simp
        · exact hLower (Sum.Lex.inr_lt_inr_iff.mp hij)
    · funext x
      rcases x with (_ | x)
      · simp [Lblk]
      · have hx := congrArg (fun f => f x) hdiag
        simpa [Lblk] using hx
  have hUblk : IsUpperTriangular Ublk := by
    dsimp [IsUpperTriangular, BlockTriangular, Ublk] at hU' ⊢
    intro i j hij
    rcases i with (_ | i)
    · rcases j with (_ | j)
      · simpa using hij
      · exfalso
        exact Sum.Lex.not_inr_lt_inl hij
    · rcases j with (_ | j)
      · simp
      · exact hU' (Sum.Lex.inr_lt_inr_iff.mp hij)
  have hPerm : IsPermutation (Matrix.reindex e.symm e.symm Pblk) := by
    exact
      (isPermutation_reindex (e := e) (A := Matrix.reindex e.symm e.symm Pblk)).2
        (by simpa using hPermBlk)
  have hL : IsUnitLowerTriangular (Matrix.reindex e.symm e.symm Lblk) := by
    exact
      (isUnitLowerTriangular_reindex
        (e := e)
        (h_mono := headTailLexEquiv_strictMono (α := ι))
        (A := Matrix.reindex e.symm e.symm Lblk)).2
        (by simpa using hLblk)
  have hU : IsUpperTriangular (Matrix.reindex e.symm e.symm Ublk) := by
    exact
      (isUpperTriangular_reindex
        (e := e)
        (h_mono := headTailLexEquiv_strictMono (α := ι))
        (A := Matrix.reindex e.symm e.symm Ublk)).2
        (by simpa using hUblk)
  refine ⟨(Matrix.reindex e.symm e.symm Pblk,
      Matrix.reindex e.symm e.symm Lblk,
      Matrix.reindex e.symm e.symm Ublk), ?_, ?_⟩
  · exact ⟨hPerm, hL, hU⟩
  · exact hTransport

end PivotLift

/--
Direct PLU lift for the current head-tail submatrix strategy core, with
 the subsingleton case discharged concretely.
-/
theorem pluHeadTailSubmatrixLift [DivisionRing R] :
    SquareStrategyLiftType
      (fun x : SquareUniverse R => HasPLU x.A)
      pluHeadTailSubmatrixStrategyCore := by
  intro ι fι dι oι nι A hA hP
  by_cases h_sub : Subsingleton ι
  · letI := h_sub
    exact base_plu_subsingleton A
  · letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp h_sub
    by_cases hPivot : PLUPivotReady ι A
    · have hslice :
          ((pluHeadTailSubmatrixStrategyCore.strategy fι dι oι nι).reduction.slice A hA) =
            pluSchurSlice ι A := by
        dsimp [pluHeadTailSubmatrixStrategyCore, pluHeadTailReduction,
          pluPivotSchurReduction, pluZeroColumnReduction,
          MatDecompFormal.Abstractions.ReductionMethod.try_else]
        rw [dif_pos hPivot]
      exact nontrivial_pivotReady_pluHeadTailSchurLift
        fι dι oι nι A hPivot (hslice ▸ hP)
    · have hZero : PLUZeroColumnReady ι A := hA.resolve_left hPivot
      have hslice :
          ((pluHeadTailSubmatrixStrategyCore.strategy fι dι oι nι).reduction.slice A hA) =
            A.submatrix
              (fun i : PLUTailIdx ι => headTailEquiv.symm (Sum.inr i))
              (fun j : PLUTailIdx ι => headTailEquiv.symm (Sum.inr j)) := by
        dsimp [pluHeadTailSubmatrixStrategyCore, pluHeadTailReduction,
          pluPivotSchurReduction, pluZeroColumnReduction,
          MatDecompFormal.Abstractions.ReductionMethod.try_else]
        rw [dif_neg hPivot]
        rfl
      exact zeroColumn_pluHeadTailSubmatrixLift A hZero (hslice ▸ hP)

end MatDecompFormal.Instances
