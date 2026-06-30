/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Components.Lifting.LowLevel
import MatDecompFormal.Components.Properties.Reindex
import MatDecompFormal.Components.BlockAlgebra
import MatDecompFormal.Instances.LU.Strategy

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Abstractions
open MatDecompFormal.Components
open MatDecompFormal.Components.Properties

/-!
# LU Direct Hooks

This file contains the proof-side transport and lift hooks for the no-pivot LU
strategy. The transform is identity; the lift consumes recursive pivot-readiness
evidence and assembles a Schur-complement LU block factorization.
-/

variable {ι : Type*} {R : Type*} [Fintype ι] [LinearOrder ι]

section PivotLift

variable [DecidableEq ι] [Nonempty ι] [DivisionRing R]

omit [DecidableEq ι] in
lemma luPivotLowerFactor_mul_headBlock
    (A : Matrix ι ι R)
    (hPivot : LUPivotReady ι A) :
    let A' := luHeadTailPlain ι A
    luPivotLowerFactor ι A * A'.toBlocks₁₁ = A'.toBlocks₂₁ := by
  classical
  ext i j
  cases j
  have h_inv :
      (A (headElem (α := ι)) (headElem (α := ι)))⁻¹ *
          A (headElem (α := ι)) (headElem (α := ι)) = 1 :=
    inv_mul_cancel₀ hPivot
  simp [luPivotLowerFactor, pluPivotLowerFactor, luHeadTailPlain, pluHeadTailPlain, pluHeadInv,
    Matrix.mul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.reindex_apply, h_inv,
    mul_assoc]

lemma luPivotReady_plain_equation
    (A : Matrix ι ι R)
    (hPivot : LUPivotReady ι A)
    {L' U' : Matrix (LUTailIdx ι) (LUTailIdx ι) R}
    (hEq' : luSchurSlice ι A = L' * U') :
    let Aplain := luHeadTailPlain ι A
    let l := luPivotLowerFactor ι A
    let Lplain : Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R :=
      fromBlocks (1 : Matrix Unit Unit R) 0 l L'
    let Uplain : Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R :=
      fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ 0 U'
    (1 : Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R) * Aplain =
      Lplain * Uplain := by
  classical
  dsimp
  let Aplain : Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R := luHeadTailPlain ι A
  let l : Matrix (LUTailIdx ι) Unit R := luPivotLowerFactor ι A
  have hlA11 : l * Aplain.toBlocks₁₁ = Aplain.toBlocks₂₁ := by
    simpa [l, Aplain] using luPivotLowerFactor_mul_headBlock A hPivot
  have hSchur_restore :
      luSchurSlice ι A + l * Aplain.toBlocks₁₂ = Aplain.toBlocks₂₂ := by
    dsimp [luSchurSlice, pluSchurSlice, luPivotLowerFactor, pluPivotLowerFactor,
      luHeadTailPlain, pluHeadTailPlain, l, Aplain]
    abel
  calc
    (1 : Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R) * Aplain = Aplain := by
      simp
    _ = fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₂₁
          Aplain.toBlocks₂₂ := by
        simpa using (fromBlocks_toBlocks Aplain).symm
    _ = fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ (l * Aplain.toBlocks₁₁)
          (l * Aplain.toBlocks₁₂ + L' * U') := by
        rw [hlA11]
        congr 1
        calc
          Aplain.toBlocks₂₂ = luSchurSlice ι A + l * Aplain.toBlocks₁₂ := by
            simpa using hSchur_restore.symm
          _ = l * Aplain.toBlocks₁₂ + L' * U' := by
            rw [hEq']
            abel
    _ =
        (fromBlocks (1 : Matrix Unit Unit R) 0 l L' :
          Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R) *
        (fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ 0 U' :
          Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R) := by
          symm
          exact block_L_mul_U l L' Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ U'

theorem luHeadTailSchurLift
    (A : Matrix ι ι R)
    (hPivot : LUPivotReady ι A)
    (hTail : HasLU (luSchurSlice ι A)) :
    HasLU A := by
  classical
  rcases hTail with ⟨⟨L', U'⟩, ⟨hL', hU'⟩, hEq'⟩
  let e0 : ι ≃ Unit ⊕ LUTailIdx ι := headTailEquiv (α := ι)
  let s : Unit ⊕ LUTailIdx ι ≃ Unit ⊕ₗ LUTailIdx ι := sumToLexEquiv Unit (LUTailIdx ι)
  let e : ι ≃ Unit ⊕ₗ LUTailIdx ι := headTailLexEquiv (α := ι)
  let Aplain : Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R := luHeadTailPlain ι A
  let Ablk : Matrix (Unit ⊕ₗ LUTailIdx ι) (Unit ⊕ₗ LUTailIdx ι) R := Matrix.reindex e e A
  let l : Matrix (LUTailIdx ι) Unit R := luPivotLowerFactor ι A
  let Lplain : Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 l L'
  let Uplain : Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R :=
    fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ 0 U'
  have hEqSchur : luSchurSlice ι A = L' * U' := by
    simpa [HasLU, LU_Schema] using hEq'
  have hPlainEq :
      (1 : Matrix (Unit ⊕ LUTailIdx ι) (Unit ⊕ LUTailIdx ι) R) * Aplain =
        Lplain * Uplain := by
    simpa [Lplain, Uplain, Aplain, l] using
      luPivotReady_plain_equation (A := A) hPivot hEqSchur
  let Lblk : Matrix (Unit ⊕ₗ LUTailIdx ι) (Unit ⊕ₗ LUTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 l L'
  let Ublk : Matrix (Unit ⊕ₗ LUTailIdx ι) (Unit ⊕ₗ LUTailIdx ι) R :=
    fromBlocks Ablk.toBlocks₁₁ Ablk.toBlocks₁₂ 0 U'
  have hAblk : Matrix.reindex s s Aplain = Ablk := by
    simpa [Aplain, Ablk, e0, e, s, headTailLexEquiv] using
      (reindex_reindex e0 e0 s s A)
  have hA11blk : Aplain.toBlocks₁₁ = Ablk.toBlocks₁₁ := by
    simpa using congrArg Matrix.toBlocks₁₁ hAblk
  have hA12blk : Aplain.toBlocks₁₂ = Ablk.toBlocks₁₂ := by
    simpa using congrArg Matrix.toBlocks₁₂ hAblk
  have hLblk_def : Matrix.reindex s s Lplain = Lblk := by
    simpa [Lplain, Lblk, l] using
      (reindex_sumToLex_fromBlocks
        (A₁₁ := (1 : Matrix Unit Unit R)) (A₁₂ := 0) (A₂₁ := l) (A₂₂ := L'))
  have hUblk_def : Matrix.reindex s s Uplain = Ublk := by
    simpa [Uplain, Ublk, hA11blk, hA12blk] using
      (reindex_sumToLex_fromBlocks
        (A₁₁ := Aplain.toBlocks₁₁) (A₁₂ := Aplain.toBlocks₁₂) (A₂₁ := 0) (A₂₂ := U'))
  have hReindexed := congrArg (Matrix.reindex s s) hPlainEq
  have hBlkEq :
      (1 : Matrix (Unit ⊕ₗ LUTailIdx ι) (Unit ⊕ₗ LUTailIdx ι) R) * Ablk =
        Lblk * Ublk := by
    rw [← hAblk, ← hLblk_def, ← hUblk_def]
    simpa using hReindexed
  have hTransport :=
    schur_case_transport_back
      (A := A)
      (e := e)
      (P_blk := (1 : Matrix (Unit ⊕ₗ LUTailIdx ι) (Unit ⊕ₗ LUTailIdx ι) R))
      (L_blk := Lblk)
      (U_blk := Ublk)
      hBlkEq
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
  let L : Matrix ι ι R := Matrix.reindex e.symm e.symm Lblk
  let U : Matrix ι ι R := Matrix.reindex e.symm e.symm Ublk
  have hL : IsUnitLowerTriangular L := by
    exact
      (isUnitLowerTriangular_reindex
        (e := e)
        (h_mono := headTailLexEquiv_strictMono (α := ι))
        (A := L)).2
        (by simpa [L] using hLblk)
  have hU : IsUpperTriangular U := by
    exact
      (isUpperTriangular_reindex
        (e := e)
        (h_mono := headTailLexEquiv_strictMono (α := ι))
        (A := U)).2
        (by simpa [U] using hUblk)
  refine ⟨(L, U), ?_, ?_⟩
  · exact ⟨hL, hU⟩
  · simpa [L, U, LU_Schema, Matrix.one_mul] using hTransport

end PivotLift

/-- Proof-side LU hooks for the no-pivot strategy core. -/
noncomputable def lu_strategy_proof {R : Type*} [DivisionRing R] :
    SquareStrategyProofData R
      (fun x : SquareUniverse R => LURecursivePivotReady x.A → HasLU x.A)
      lu_strategy_core where
  transport := by
    intro ι fι dι oι nι A B hBA hP hReady
    rcases hBA with rfl | ⟨t, rfl⟩
    · exact hP hReady
    · cases t
      exact hP hReady
  lift := by
    intro ι fι dι oι nι A hA hP hReady
    by_cases hbase : Fintype.card ι ≤ 1
    · have h_sub : Subsingleton ι := by
        classical
        exact Fintype.card_le_one_iff_subsingleton.mp hbase
      letI := h_sub
      exact base_lu_subsingleton A
    · have hcard : 1 < Fintype.card ι := Nat.lt_of_not_ge hbase
      letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hcard
      have hReady' :
          LUPivotReady ι A ∧ LURecursivePivotReady (luSchurSlice ι A) := by
        exact (luRecursivePivotReady_step_iff (A := A) hbase).1 hReady
      rcases hReady' with ⟨hPivot, hTail⟩
      have hslice :
          ((lu_strategy_core.strategy fι dι oι nι).reduction.slice A hA) =
            luSchurSlice ι A := by
        rfl
      exact luHeadTailSchurLift A hPivot (hP (hslice ▸ hTail))

end MatDecompFormal.Instances
