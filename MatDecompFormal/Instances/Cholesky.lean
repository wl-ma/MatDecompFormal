import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.IsDiag

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework

open scoped ComplexOrder

/-!
# Cholesky-style decomposition via LDL

This file now uses a genuine head-tail Schur-complement strategy core on the
framework side. The current proof-side lift still delegates to mathlib's `LDL`
result, but the base case is now handled internally by a trivial subsingleton
witness rather than the direct theorem.

The theorem `exists_cholesky_decomposition_direct` below is intentionally kept as
a historical/direct LDL-based lemma and as a local comparison point. It is not the
main decomposition theorem and it is not the route used by the recursive
framework proof. The current main statement is `exists_cholesky_decomposition`,
which is assembled from `cholesky_strategy_data` via
`mkSquareSubtypeInductionInstanceFromStrategy` and discharged through
`SquareSubtypeInductionInstance.prove_for_matrix`.
-/

section Presentation

variable {ι R : Type*}

/--
Cholesky-style schema on finite square matrices.

Equation form: `A = L * D * Lᵀ`, where `D` is diagonal.
-/
def Cholesky_Schema [Fintype ι] [Semiring R] : DecompositionSchema ι ι R where
  Factors := Matrix ι ι R × Matrix ι ι R
  property := fun (_L, D) => D.IsDiag
  equation := fun A (L, D) => A = L * D * Lᵀ

/-- Existence proposition for the Cholesky-style wrapper. -/
def HasCholesky [Fintype ι] [Semiring R] (A : Matrix ι ι R) : Prop :=
  HasDecomposition Cholesky_Schema A

noncomputable def finiteLinearOrderLocallyFiniteOrderBot
    (α : Type*) [Fintype α] [LinearOrder α] : LocallyFiniteOrderBot α := by
  letI : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  by_cases h : Nonempty α
  · letI := h
    letI : OrderBot α := Fintype.toOrderBot α
    infer_instance
  · letI : IsEmpty α := not_nonempty_iff.mp h
    exact IsEmpty.toLocallyFiniteOrderBot

/--
Early direct LDL-based Cholesky-style existence theorem.

This theorem is deliberately not the canonical proof path for the decomposition
framework. It proves the existence statement directly from mathlib's `LDL`
construction, without going through `SquareStrategyData`,
`mkSquareSubtypeInductionInstanceFromStrategy`, or
`SquareSubtypeInductionInstance.prove_for_matrix`.

Use `exists_cholesky_decomposition` as the main framework-routed theorem.
-/
theorem exists_cholesky_decomposition_direct
    {ι R : Type*} [Fintype ι] [LinearOrder ι]
    [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hA : A.PosDef) :
    HasCholesky A := by
  letI : WellFoundedLT ι := inferInstance
  letI : LocallyFiniteOrder ι := Fintype.toLocallyFiniteOrder
  letI : LocallyFiniteOrderBot ι := finiteLinearOrderLocallyFiniteOrderBot ι
  refine ⟨(LDL.lower hA, LDL.diag hA), ?_, ?_⟩
  · change (LDL.diag hA).IsDiag
    simpa [LDL.diag] using Matrix.isDiag_diagonal (LDL.diagEntries hA)
  · simpa [Cholesky_Schema, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (LDL.lower_conj_diag (hS := hA)).symm

/-- Trivial subsingleton Cholesky witness, used for the zero-dimensional base case. -/
theorem base_cholesky_subsingleton
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R] [Subsingleton ι]
    (A : Matrix ι ι R) :
    HasCholesky A := by
  refine ⟨(1, A), ?_, ?_⟩
  · intro i j hij
    exfalso
    exact hij (Subsingleton.elim _ _)
  · simpa [Cholesky_Schema]

abbrev CholeskyTailIdx (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { a : ι // a ≠ headElem (α := ι) }

noncomputable def choleskyHeadTailPlain
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*}
    (A : Matrix ι ι R) : Matrix (Unit ⊕ CholeskyTailIdx ι) (Unit ⊕ CholeskyTailIdx ι) R :=
  Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A

noncomputable def choleskyHeadInv
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Inv R]
    (A : Matrix ι ι R) : Matrix Unit Unit R :=
  fun _ _ => (A (headElem (α := ι)) (headElem (α := ι)))⁻¹

noncomputable def choleskyLowerFactor
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Ring R] [Inv R]
    (A : Matrix ι ι R) : Matrix (CholeskyTailIdx ι) Unit R :=
  let A' := choleskyHeadTailPlain ι A
  A'.toBlocks₂₁ * choleskyHeadInv ι A

noncomputable def choleskySchurSlice
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Ring R] [Inv R]
    (A : Matrix ι ι R) : Matrix (CholeskyTailIdx ι) (CholeskyTailIdx ι) R :=
  let A' := choleskyHeadTailPlain ι A
  A'.toBlocks₂₂ - choleskyLowerFactor ι A * A'.toBlocks₁₂

noncomputable def choleskyHeadTailReduction
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Ring R] [Inv R] :
    ReductionMethod ι ι (CholeskyTailIdx ι) (CholeskyTailIdx ι) R where
  IsSliceable := fun _ => True
  slice := fun A _ => choleskySchurSlice ι A
  reconstruct := fun A _ slice_sol =>
    let A' := choleskyHeadTailPlain ι A
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    let L₂₁ := choleskyLowerFactor ι A
    let A₂₂ := slice_sol + L₂₁ * A₁₂
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).reindex (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm
  reconstruct_slice_eq := by
    intro A _
    classical
    let A' : Matrix (Unit ⊕ CholeskyTailIdx ι) (Unit ⊕ CholeskyTailIdx ι) R :=
      Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A
    let Hinv : Matrix Unit Unit R := choleskyHeadInv ι A
    have h_reconstructed_eq_A' :
        fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁
          (A'.toBlocks₂₂ - (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂ +
            (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂) = A' := by
      have h22 :
          A'.toBlocks₂₂ - (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂ +
              (A'.toBlocks₂₁ * Hinv) * A'.toBlocks₁₂ = A'.toBlocks₂₂ := by
        abel
      rw [h22]
      exact fromBlocks_toBlocks A'
    change
      (fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁
        (A'.toBlocks₂₂ - A'.toBlocks₂₁ * Hinv * A'.toBlocks₁₂ +
          A'.toBlocks₂₁ * Hinv * A'.toBlocks₁₂)).reindex
          (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm = A
    rw [h_reconstructed_eq_A']
    ext i j
    simp [A']

def Cholesky_P {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (x : SquareUniverse R) : Prop :=
  x.A.PosDef → HasCholesky x.A

lemma posDef_reindex_equiv
    {R α β : Type*} [RCLike R]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {A : Matrix α α R} (hA : A.PosDef) :
    (Matrix.reindex e e A).PosDef := by
  refine ⟨?_, ?_⟩
  · simpa [Matrix.reindex] using hA.1.submatrix e.symm
  · intro x hx
    have hx' : x ∘ e ≠ 0 := by
      intro hzero
      apply hx
      funext i
      simpa using congrFun hzero (e.symm i)
    have hpos := hA.2 (x ∘ e) hx'
    have hmul : (Matrix.reindex e e A) *ᵥ x = (A *ᵥ (x ∘ e)) ∘ e.symm := by
      simpa [Matrix.reindex] using
        (Matrix.submatrix_mulVec_equiv A x e.symm e.symm)
    rw [hmul, dotProduct_comp_equiv_symm (u := star x) (x := A *ᵥ (x ∘ e)) (e := e)]
    simpa [Function.comp_def] using hpos

section RecursiveHelpers

variable [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]

omit [DecidableEq ι] in
lemma choleskyHeadBlock_posDef
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef) :
    (choleskyHeadTailPlain ι A).toBlocks₁₁.PosDef := by
  let Aplain := choleskyHeadTailPlain ι A
  have hhead : 0 < A (headElem (α := ι)) (headElem (α := ι)) := hPos.diag_pos
  have hdiag :
      Aplain.toBlocks₁₁ = diagonal (fun _ : Unit => A (headElem (α := ι)) (headElem (α := ι))) := by
    ext i j
    cases i
    cases j
    simp [Aplain, choleskyHeadTailPlain, Matrix.toBlocks₁₁, Matrix.reindex_apply]
  rw [hdiag]
  exact Matrix.PosDef.diagonal (fun _ => by simpa using hhead)

omit [DecidableEq ι] in
lemma choleskyHeadInv_eq_inv
    {R : Type*} [Field R]
    (A : Matrix ι ι R) :
    choleskyHeadInv ι A = (choleskyHeadTailPlain ι A).toBlocks₁₁⁻¹ := by
  let A11 := (choleskyHeadTailPlain ι A).toBlocks₁₁
  rw [Matrix.inv_subsingleton A11]
  ext i j
  cases i
  cases j
  simp [A11, choleskyHeadInv, choleskyHeadTailPlain, Matrix.toBlocks₁₁, Matrix.reindex_apply,
    Ring.inverse_eq_inv]

omit [DecidableEq ι] in
lemma choleskyHeadTailPlain_fromBlocks
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R)
    (hHermA : A.IsHermitian) :
    let Aplain := choleskyHeadTailPlain ι A
    fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₁₂ᵀ Aplain.toBlocks₂₂ = Aplain := by
  classical
  intro Aplain
  have hHerm : Aplain.IsHermitian := by
    simpa [Aplain, choleskyHeadTailPlain] using hHermA.submatrix ((headTailEquiv (α := ι)).symm)
  have h21 : Aplain.toBlocks₂₁ = Aplain.toBlocks₁₂ᵀ := by
    ext i j
    have hEq := congrArg (fun M => M (Sum.inr i) (Sum.inl j)) hHerm.eq
    simpa [Aplain, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂] using hEq.symm
  calc
    fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₁₂ᵀ Aplain.toBlocks₂₂
        = fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ := by rw [h21]
    _ = Aplain := fromBlocks_toBlocks Aplain

lemma choleskySchurSlice_posSemidef
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef) :
    (choleskySchurSlice ι A).PosSemidef := by
  classical
  let Aplain : Matrix (Unit ⊕ CholeskyTailIdx ι) (Unit ⊕ CholeskyTailIdx ι) R :=
    choleskyHeadTailPlain ι A
  let A11 : Matrix Unit Unit R := Aplain.toBlocks₁₁
  let B : Matrix Unit (CholeskyTailIdx ι) R := Aplain.toBlocks₁₂
  let D : Matrix (CholeskyTailIdx ι) (CholeskyTailIdx ι) R := Aplain.toBlocks₂₂
  have hAplainPos : Aplain.PosDef := posDef_reindex_equiv (e := headTailEquiv (α := ι)) hPos
  have hA11Pos : A11.PosDef := choleskyHeadBlock_posDef A hPos
  letI : Invertible A11 := hA11Pos.isUnit.invertible
  have hInv : choleskyHeadInv ι A = A11⁻¹ := by
    simpa [A11, Aplain] using choleskyHeadInv_eq_inv A
  have hFrom : fromBlocks A11 B Bᴴ D = Aplain := by
    simpa [A11, B, D, Aplain, Matrix.conjTranspose_eq_transpose_of_trivial] using
      choleskyHeadTailPlain_fromBlocks A hPos.1
  have h21 : Aplain.toBlocks₂₁ = Bᴴ := by
    ext i j
    have hEq := congrArg (fun M => M (Sum.inr i) (Sum.inl j)) hAplainPos.1.eq
    simpa [Aplain, B, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hEq.symm
  have hFull : (fromBlocks A11 B Bᴴ D).PosSemidef := by
    rw [hFrom]
    exact hAplainPos.posSemidef
  have hSchur : (D - Bᴴ * A11⁻¹ * B).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ (A := A11) (B := B) (D := D) hA11Pos).1 hFull
  rw [← h21] at hSchur
  simpa [choleskySchurSlice, choleskyLowerFactor, choleskyHeadTailPlain, Aplain, A11, B, D, hInv,
    Matrix.conjTranspose_eq_transpose_of_trivial, mul_assoc] using hSchur

lemma choleskySchurSlice_dotProduct_pos
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef)
    {y : CholeskyTailIdx ι → R} (hy : y ≠ 0) :
    0 < star y ⬝ᵥ (choleskySchurSlice ι A *ᵥ y) := by
  classical
  let Aplain : Matrix (Unit ⊕ CholeskyTailIdx ι) (Unit ⊕ CholeskyTailIdx ι) R :=
    choleskyHeadTailPlain ι A
  let A11 : Matrix Unit Unit R := Aplain.toBlocks₁₁
  let B : Matrix Unit (CholeskyTailIdx ι) R := Aplain.toBlocks₁₂
  let D : Matrix (CholeskyTailIdx ι) (CholeskyTailIdx ι) R := Aplain.toBlocks₂₂
  have hAplainPos : Aplain.PosDef := posDef_reindex_equiv (e := headTailEquiv (α := ι)) hPos
  have hA11Pos : A11.PosDef := choleskyHeadBlock_posDef A hPos
  letI : Invertible A11 := hA11Pos.isUnit.invertible
  have hInv : choleskyHeadInv ι A = A11⁻¹ := by
    simpa [A11, Aplain] using choleskyHeadInv_eq_inv A
  have hFrom : fromBlocks A11 B Bᴴ D = Aplain := by
    simpa [A11, B, D, Aplain, Matrix.conjTranspose_eq_transpose_of_trivial] using
      choleskyHeadTailPlain_fromBlocks A hPos.1
  have h21 : Aplain.toBlocks₂₁ = Bᴴ := by
    ext i j
    have hEq := congrArg (fun M => M (Sum.inr i) (Sum.inl j)) hAplainPos.1.eq
    simpa [Aplain, B, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hEq.symm
  let x : Unit → R := -((A11⁻¹ * B) *ᵥ y)
  have hxy : Sum.elim x y ≠ 0 := by
    intro hzero
    apply hy
    funext i
    exact congrFun hzero (Sum.inr i)
  have hquad := hAplainPos.2 (Sum.elim x y) hxy
  rw [← hFrom] at hquad
  rw [dotProduct_mulVec] at hquad
  have hschurEq :
      star (Sum.elim x y) ᵥ* (fromBlocks A11 B Bᴴ D) ⬝ᵥ (Sum.elim x y) =
        star (x + (A11⁻¹ * B) *ᵥ y) ᵥ* A11 ⬝ᵥ (x + (A11⁻¹ * B) *ᵥ y) +
          star y ᵥ* (D - Bᴴ * A11⁻¹ * B) ⬝ᵥ y := by
    simpa using
      (Matrix.schur_complement_eq₁₁ (A := A11) (B := B) (D := D) x y hA11Pos.1)
  rw [hschurEq] at hquad
  have hxzero : x + (A11⁻¹ * B) *ᵥ y = 0 := by
    ext u
    cases u
    simp [x]
  rw [hxzero, dotProduct_zero, zero_add, ← dotProduct_mulVec] at hquad
  have hslice : choleskySchurSlice ι A = D - Bᴴ * A11⁻¹ * B := by
    rw [show choleskySchurSlice ι A = D - Aplain.toBlocks₂₁ * A11⁻¹ * B by
      simp [choleskySchurSlice, choleskyLowerFactor, choleskyHeadTailPlain, Aplain, A11, B, D, hInv,
        Matrix.conjTranspose_eq_transpose_of_trivial, mul_assoc]]
    rw [h21]
  simpa [dotProduct_mulVec, hslice] using hquad


lemma choleskySchurSlice_posDef
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef) :
    (choleskySchurSlice ι A).PosDef := by
  refine ⟨(choleskySchurSlice_posSemidef A hPos).1, ?_⟩
  intro y hy
  exact choleskySchurSlice_dotProduct_pos A hPos hy

omit [DecidableEq ι] in
lemma choleskyLowerFactor_mul_headBlock
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef) :
    let Aplain := choleskyHeadTailPlain ι A
    let A11 : Matrix Unit Unit R := Aplain.toBlocks₁₁
    choleskyLowerFactor ι A * A11 = Aplain.toBlocks₂₁ := by
  classical
  intro Aplain A11
  letI : Invertible A11 := (choleskyHeadBlock_posDef A hPos).isUnit.invertible
  have hInv : choleskyHeadInv ι A = A11⁻¹ := by
    simpa [A11, Aplain] using choleskyHeadInv_eq_inv A
  have hA11EntryPos : 0 < A11 () () := by
    simpa [A11] using (choleskyHeadBlock_posDef A hPos).diag_pos
  have hA11EntryNe : A11 () () ≠ 0 := ne_of_gt hA11EntryPos
  ext i j
  cases j
  simp [choleskyLowerFactor, choleskyHeadTailPlain, Aplain, A11, hInv, Matrix.mul_apply]
  rw [mul_assoc]
  have hcancel : (A11 () ())⁻¹ * A11 () () = 1 := inv_mul_cancel₀ hA11EntryNe
  have hcancel' :
      ((A.submatrix ⇑headTailEquiv.symm ⇑headTailEquiv.symm).toBlocks₁₁ () ())⁻¹ *
          (A.submatrix ⇑headTailEquiv.symm ⇑headTailEquiv.symm).toBlocks₁₁ () () = 1 := by
    simpa [A11] using hcancel
  rw [hcancel', mul_one]


end RecursiveHelpers

lemma isDiag_subsingleton
    {α R : Type*} [Subsingleton α] [Zero R] (D : Matrix α α R) :
    D.IsDiag := by
  intro i j hij
  exfalso
  exact hij (Subsingleton.elim _ _)

lemma isDiag_reindex_equiv
    {α β R : Type*} [DecidableEq α] [DecidableEq β] [Zero R]
    (e : α ≃ β) {D : Matrix α α R} (hD : D.IsDiag) :
    (Matrix.reindex e e D).IsDiag := by
  intro i j hij
  apply hD
  intro hEq
  apply hij
  exact e.symm.injective hEq

section RecursiveHelpers

variable [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]

lemma choleskyHeadBlock_mul_lowerFactorTranspose
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef) :
    let Aplain := choleskyHeadTailPlain ι A
    let A11 : Matrix Unit Unit R := Aplain.toBlocks₁₁
    A11 * (choleskyLowerFactor ι A)ᵀ = Aplain.toBlocks₁₂ := by
  classical
  intro Aplain A11
  have h21 : Aplain.toBlocks₂₁ = Aplain.toBlocks₁₂ᵀ := by
    have hAplainPos : Aplain.PosDef := posDef_reindex_equiv (e := headTailEquiv (α := ι)) hPos
    ext i j
    have hEq := congrArg (fun M => M (Sum.inr i) (Sum.inl j)) hAplainPos.1.eq
    simpa [Aplain, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂] using hEq.symm
  have hlower : choleskyLowerFactor ι A * A11 = Aplain.toBlocks₂₁ :=
    choleskyLowerFactor_mul_headBlock A hPos
  have htranspose := congrArg Matrix.transpose hlower
  simpa [Matrix.transpose_mul, h21, A11, Matrix.transpose_submatrix, Matrix.submatrix_id_id]
    using htranspose

omit [DecidableEq ι] in
lemma choleskySchur_restore
    {R : Type*} [Ring R] [Inv R]
    (A : Matrix ι ι R) :
    let Aplain := choleskyHeadTailPlain ι A
    choleskySchurSlice ι A + choleskyLowerFactor ι A * Aplain.toBlocks₁₂ = Aplain.toBlocks₂₂ := by
  classical
  intro Aplain
  dsimp [choleskySchurSlice, choleskyLowerFactor, choleskyHeadTailPlain, Aplain]
  abel


theorem choleskyHeadTailSchurLift
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R)
    (hPos : A.PosDef)
    (hP : HasCholesky (choleskySchurSlice ι A)) :
    HasCholesky A := by
  classical
  let Aplain : Matrix (Unit ⊕ CholeskyTailIdx ι) (Unit ⊕ CholeskyTailIdx ι) R :=
    choleskyHeadTailPlain ι A
  let A11 : Matrix Unit Unit R := Aplain.toBlocks₁₁
  let A12 : Matrix Unit (CholeskyTailIdx ι) R := Aplain.toBlocks₁₂
  let l : Matrix (CholeskyTailIdx ι) Unit R := choleskyLowerFactor ι A
  rcases hP with ⟨factors, hDiag', hEq'⟩
  rcases factors with ⟨L', D'⟩
  have hEqSchur : choleskySchurSlice ι A = L' * D' * L'ᵀ := by
    simpa [HasCholesky, Cholesky_Schema] using hEq'
  let Lplain : Matrix (Unit ⊕ CholeskyTailIdx ι) (Unit ⊕ CholeskyTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 l L'
  let Dplain : Matrix (Unit ⊕ CholeskyTailIdx ι) (Unit ⊕ CholeskyTailIdx ι) R :=
    fromBlocks A11 0 0 D'
  have hA11Diag : A11.IsDiag := isDiag_subsingleton A11
  have hDplainDiag : Dplain.IsDiag := by
    simpa [Dplain] using Matrix.IsDiag.fromBlocks hA11Diag hDiag'
  have hlower : l * A11 = Aplain.toBlocks₂₁ :=
    choleskyLowerFactor_mul_headBlock A hPos
  have hupper : A11 * lᵀ = A12 :=
    choleskyHeadBlock_mul_lowerFactorTranspose A hPos
  have hrestore : choleskySchurSlice ι A + l * A12 = Aplain.toBlocks₂₂ :=
    choleskySchur_restore A
  have hEqPlain : Aplain = Lplain * Dplain * Lplainᵀ := by
    calc
      Aplain = fromBlocks A11 A12 Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ := by
        simpa [Aplain] using (fromBlocks_toBlocks Aplain).symm
      _ = fromBlocks A11 (A11 * lᵀ) (l * A11)
            (l * (A11 * lᵀ) + L' * D' * L'ᵀ) := by
        rw [hupper, hlower]
        congr 1
        have hrestore' : Aplain.toBlocks₂₂ = l * A12 + L' * D' * L'ᵀ := by
          calc
            Aplain.toBlocks₂₂ = choleskySchurSlice ι A + l * A12 := by
              simpa [add_comm] using hrestore.symm
            _ = l * A12 + L' * D' * L'ᵀ := by
              rw [hEqSchur]
              abel
        exact hrestore'
      _ = Lplain * Dplain * Lplainᵀ := by
        simp [Lplain, Dplain, Matrix.fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_assoc]
  let L : Matrix ι ι R :=
    Matrix.reindex (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm Lplain
  let D : Matrix ι ι R :=
    Matrix.reindex (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm Dplain
  refine ⟨(L, D), ?_, ?_⟩
  · exact isDiag_reindex_equiv (e := (headTailEquiv (α := ι)).symm) hDplainDiag
  · have hEqPlain' : Aplain = Lplain * (Dplain * Lplainᵀ) := by
        simpa [Matrix.mul_assoc] using hEqPlain
    have hEqRe := congrArg
        (Matrix.reindex (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm)
        hEqPlain'
    have hRhsReindex :
        Matrix.reindex (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm
            (Lplain * (Dplain * Lplainᵀ)) = L * (D * Lᵀ) := by
      simp [L, D, Matrix.transpose_reindex, Matrix.submatrix_mul_equiv, Matrix.mul_assoc]
    rw [hRhsReindex] at hEqRe
    simpa [Aplain, choleskyHeadTailPlain, Cholesky_Schema, Matrix.mul_assoc] using hEqRe


end RecursiveHelpers

noncomputable def cholesky_strategy_core {R : Type*} [RCLike R] [TrivialStar R] : SquareStrategyCore R where
  SliceIdx := fun {ι} fι dι oι nι => @CholeskyTailIdx ι fι oι nι
  sliceFintype := by
    intro ι fι dι oι nι
    infer_instance
  sliceDecEq := by
    intro ι fι dι oι nι
    infer_instance
  sliceLinearOrder := by
    intro ι fι dι oι nι
    infer_instance
  strategy := by
    intro ι fι dι oι nι
    refine
      { transform := trivialSquareTransform _
        reduction := choleskyHeadTailReduction ι
        goal_is_sliceable := by rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (CholeskyTailIdx ι)
        μ_mono := ?_
        slice_progress := ?_ }
    · intro A t
      cases t
      simp
    · intro A hA
      have hlt : Fintype.card (CholeskyTailIdx ι) < Fintype.card ι := by
        simpa [CholeskyTailIdx] using
          (Fintype.card_subtype_lt
            (p := fun a : ι => a ≠ headElem (α := ι))
            (x := headElem (α := ι)) (by simp))
      simpa using hlt
  μ_eq := by
    intro ι fι dι oι nι A
    rfl
  μ_slice_eq := by
    intro ι fι dι oι nι B
    rfl

def Cholesky_P_sub {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (x_sub : PosSquareUniverse R) : Prop :=
  Cholesky_P (x_sub : SquareUniverse R)

@[simp] theorem cholesky_P_compat
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (x_sub : PosSquareUniverse R) :
    Cholesky_P_sub x_sub ↔ Cholesky_P (x_sub : SquareUniverse R) :=
  Iff.rfl

theorem cholesky_base_univ
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (x : SquareUniverse R) :
    ((∀ (x_sub : PosSquareUniverse R), (x_sub : SquareUniverse R) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      Cholesky_P x := by
  intro hx hPos
  have hzero : Fintype.card x.ι = 0 := by
    have hxcard : Fintype.card x.ι ≤ 0 := by
      rcases hx with hnot | hle
      · by_contra hnotzero
        have hposCard : 0 < Fintype.card x.ι := Nat.pos_of_ne_zero (fun hz => hnotzero (hz.le))
        let x_sub : PosSquareUniverse R := ⟨x, hposCard⟩
        exact hnot x_sub rfl
      · simpa [squareSubtypeμ, squareSubtypeμBase] using hle
    exact Nat.le_zero.mp hxcard
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  letI : Subsingleton x.ι := by infer_instance
  exact base_cholesky_subsingleton x.A

noncomputable def cholesky_strategy_proof {R : Type*} [RCLike R] [TrivialStar R] :
    SquareStrategyProofData R Cholesky_P cholesky_strategy_core where
  transport := by
    intro ι fι dι oι nι A B hBA hP
    rcases hBA with rfl | ⟨t, rfl⟩
    · exact hP
    · cases t
      simpa using hP
  lift := by
    intro ι fι dι oι nι A hA hP
    intro hPos
    have hSlicePos : (choleskySchurSlice ι A).PosDef :=
      choleskySchurSlice_posDef A hPos
    exact choleskyHeadTailSchurLift A hPos (hP hSlicePos)

noncomputable def cholesky_strategy_data {R : Type*} [RCLike R] [TrivialStar R] : SquareStrategyData R Cholesky_P :=
  mkSquareStrategyData cholesky_strategy_core cholesky_strategy_proof

noncomputable def cholesky_framework_inst {R : Type*} [RCLike R] [TrivialStar R] : SquareSubtypeInductionInstance R :=
  mkSquareSubtypeInductionInstanceFromStrategy
    Cholesky_P
    cholesky_base_univ
    cholesky_strategy_data

/--
Primary Cholesky-style theorem routed through the generic subtype-induction
template, now using a genuine Schur-complement strategy core.
-/
theorem exists_cholesky_decomposition
    {R : Type*} [RCLike R] [TrivialStar R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) (hA : A.PosDef) :
    HasCholesky A := by
  have hP :
      (cholesky_framework_inst : SquareSubtypeInductionInstance R).P
        (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := cholesky_framework_inst) A
  exact hP hA

end Presentation

end MatDecompFormal.Instances
