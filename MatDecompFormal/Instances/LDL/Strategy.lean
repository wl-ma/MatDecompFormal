import MatDecompFormal.Instances.LDL.Details
import MatDecompFormal.Components.Properties.Reindex
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Framework.HeadTail
import MatDecompFormal.Framework.Reindex
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties
open MatDecompFormal.Framework

open scoped ComplexOrder

/-!
# LDL Schur-complement strategy

This file uses a genuine head-tail Schur-complement strategy core for an LDL
decomposition. The proof-side lift is the recursive Schur-complement
reconstruction `ldlHeadTailSchurLift`, while the base case is handled internally
by an empty-index witness.
-/

section Presentation

variable {ι R : Type*}

abbrev LDLTailIdx (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { a : ι // a ≠ headElem (α := ι) }

noncomputable def ldlHeadTailPlain
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*}
    (A : Matrix ι ι R) : Matrix (Unit ⊕ LDLTailIdx ι) (Unit ⊕ LDLTailIdx ι) R :=
  Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A

noncomputable def ldlHeadInv
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Inv R]
    (A : Matrix ι ι R) : Matrix Unit Unit R :=
  fun _ _ => (A (headElem (α := ι)) (headElem (α := ι)))⁻¹

noncomputable def ldlLowerFactor
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Ring R] [Inv R]
    (A : Matrix ι ι R) : Matrix (LDLTailIdx ι) Unit R :=
  let A' := ldlHeadTailPlain ι A
  A'.toBlocks₂₁ * ldlHeadInv ι A

noncomputable def ldlSchurSlice
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Ring R] [Inv R]
    (A : Matrix ι ι R) : Matrix (LDLTailIdx ι) (LDLTailIdx ι) R :=
  let A' := ldlHeadTailPlain ι A
  A'.toBlocks₂₂ - ldlLowerFactor ι A * A'.toBlocks₁₂

noncomputable def ldlHeadTailReduction
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {R : Type*} [Ring R] [Inv R] :
    ReductionMethod ι ι (LDLTailIdx ι) (LDLTailIdx ι) R where
  IsSliceable := fun _ => True
  slice := fun A _ => ldlSchurSlice ι A
  reconstruct := fun A _ slice_sol =>
    let A' := ldlHeadTailPlain ι A
    let A₁₁ := A'.toBlocks₁₁
    let A₁₂ := A'.toBlocks₁₂
    let A₂₁ := A'.toBlocks₂₁
    let L₂₁ := ldlLowerFactor ι A
    let A₂₂ := slice_sol + L₂₁ * A₁₂
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).reindex (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm
  reconstruct_slice_eq := by
    intro A _
    classical
    let A' : Matrix (Unit ⊕ LDLTailIdx ι) (Unit ⊕ LDLTailIdx ι) R :=
      Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A
    let Hinv : Matrix Unit Unit R := ldlHeadInv ι A
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

def LDL_P {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (x : SquareUniverse R) : Prop :=
  x.A.PosDef → HasLDLDecomposition x.A

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
lemma ldlHeadBlock_posDef
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef) :
    (ldlHeadTailPlain ι A).toBlocks₁₁.PosDef := by
  let Aplain := ldlHeadTailPlain ι A
  have hhead : 0 < A (headElem (α := ι)) (headElem (α := ι)) := hPos.diag_pos
  have hdiag :
      Aplain.toBlocks₁₁ = diagonal (fun _ : Unit => A (headElem (α := ι)) (headElem (α := ι))) := by
    ext i j
    cases i
    cases j
    simp [Aplain, ldlHeadTailPlain, Matrix.toBlocks₁₁, Matrix.reindex_apply]
  rw [hdiag]
  exact Matrix.PosDef.diagonal (fun _ => by simpa using hhead)

omit [DecidableEq ι] in
lemma ldlHeadInv_eq_inv
    {R : Type*} [Field R]
    (A : Matrix ι ι R) :
    ldlHeadInv ι A = (ldlHeadTailPlain ι A).toBlocks₁₁⁻¹ := by
  let A11 := (ldlHeadTailPlain ι A).toBlocks₁₁
  rw [Matrix.inv_subsingleton A11]
  ext i j
  cases i
  cases j
  simp [A11, ldlHeadInv, ldlHeadTailPlain, Matrix.toBlocks₁₁, Matrix.reindex_apply,
    Ring.inverse_eq_inv]

omit [DecidableEq ι] in
lemma ldlHeadTailPlain_fromBlocks
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R)
    (hHermA : A.IsHermitian) :
    let Aplain := ldlHeadTailPlain ι A
    fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₁₂ᵀ
      Aplain.toBlocks₂₂ = Aplain := by
  classical
  intro Aplain
  have hHerm : Aplain.IsHermitian := by
    simpa [Aplain, ldlHeadTailPlain] using
      hHermA.submatrix ((headTailEquiv (α := ι)).symm)
  have h21 : Aplain.toBlocks₂₁ = Aplain.toBlocks₁₂ᵀ := by
    ext i j
    have hEq := congrArg (fun M => M (Sum.inr i) (Sum.inl j)) hHerm.eq
    simpa [Aplain, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂] using hEq.symm
  calc
    fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₁₂ᵀ Aplain.toBlocks₂₂
        = fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₂₁
            Aplain.toBlocks₂₂ := by rw [h21]
    _ = Aplain := fromBlocks_toBlocks Aplain

lemma ldlSchurSlice_posSemidef
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef) :
    (ldlSchurSlice ι A).PosSemidef := by
  classical
  let Aplain : Matrix (Unit ⊕ LDLTailIdx ι) (Unit ⊕ LDLTailIdx ι) R :=
    ldlHeadTailPlain ι A
  let A11 : Matrix Unit Unit R := Aplain.toBlocks₁₁
  let B : Matrix Unit (LDLTailIdx ι) R := Aplain.toBlocks₁₂
  let D : Matrix (LDLTailIdx ι) (LDLTailIdx ι) R := Aplain.toBlocks₂₂
  have hAplainPos : Aplain.PosDef := posDef_reindex_equiv (e := headTailEquiv (α := ι)) hPos
  have hA11Pos : A11.PosDef := ldlHeadBlock_posDef A hPos
  letI : Invertible A11 := hA11Pos.isUnit.invertible
  have hInv : ldlHeadInv ι A = A11⁻¹ := by
    simpa [A11, Aplain] using ldlHeadInv_eq_inv A
  have hFrom : fromBlocks A11 B Bᴴ D = Aplain := by
    simpa [A11, B, D, Aplain, Matrix.conjTranspose_eq_transpose_of_trivial] using
      ldlHeadTailPlain_fromBlocks A hPos.1
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
  simpa [ldlSchurSlice, ldlLowerFactor, ldlHeadTailPlain, Aplain, A11, B, D, hInv,
    Matrix.conjTranspose_eq_transpose_of_trivial, mul_assoc] using hSchur

lemma ldlSchurSlice_dotProduct_pos
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef)
    {y : LDLTailIdx ι → R} (hy : y ≠ 0) :
    0 < star y ⬝ᵥ (ldlSchurSlice ι A *ᵥ y) := by
  classical
  let Aplain : Matrix (Unit ⊕ LDLTailIdx ι) (Unit ⊕ LDLTailIdx ι) R :=
    ldlHeadTailPlain ι A
  let A11 : Matrix Unit Unit R := Aplain.toBlocks₁₁
  let B : Matrix Unit (LDLTailIdx ι) R := Aplain.toBlocks₁₂
  let D : Matrix (LDLTailIdx ι) (LDLTailIdx ι) R := Aplain.toBlocks₂₂
  have hAplainPos : Aplain.PosDef := posDef_reindex_equiv (e := headTailEquiv (α := ι)) hPos
  have hA11Pos : A11.PosDef := ldlHeadBlock_posDef A hPos
  letI : Invertible A11 := hA11Pos.isUnit.invertible
  have hInv : ldlHeadInv ι A = A11⁻¹ := by
    simpa [A11, Aplain] using ldlHeadInv_eq_inv A
  have hFrom : fromBlocks A11 B Bᴴ D = Aplain := by
    simpa [A11, B, D, Aplain, Matrix.conjTranspose_eq_transpose_of_trivial] using
      ldlHeadTailPlain_fromBlocks A hPos.1
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
  have hslice : ldlSchurSlice ι A = D - Bᴴ * A11⁻¹ * B := by
    rw [show ldlSchurSlice ι A = D - Aplain.toBlocks₂₁ * A11⁻¹ * B by
      simp [ldlSchurSlice, ldlLowerFactor, ldlHeadTailPlain,
        Aplain, A11, B, D, hInv]]
    rw [h21]
  simpa [dotProduct_mulVec, hslice] using hquad


lemma ldlSchurSlice_posDef
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef) :
    (ldlSchurSlice ι A).PosDef := by
  refine ⟨(ldlSchurSlice_posSemidef A hPos).1, ?_⟩
  intro y hy
  exact ldlSchurSlice_dotProduct_pos A hPos hy

omit [DecidableEq ι] in
lemma ldlLowerFactor_mul_headBlock
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef) :
    let Aplain := ldlHeadTailPlain ι A
    let A11 : Matrix Unit Unit R := Aplain.toBlocks₁₁
    ldlLowerFactor ι A * A11 = Aplain.toBlocks₂₁ := by
  classical
  intro Aplain A11
  letI : Invertible A11 := (ldlHeadBlock_posDef A hPos).isUnit.invertible
  have hInv : ldlHeadInv ι A = A11⁻¹ := by
    simpa [A11, Aplain] using ldlHeadInv_eq_inv A
  have hA11EntryPos : 0 < A11 () () := by
    simpa [A11] using (ldlHeadBlock_posDef A hPos).diag_pos
  have hA11EntryNe : A11 () () ≠ 0 := ne_of_gt hA11EntryPos
  ext i j
  cases j
  simp [ldlLowerFactor, ldlHeadTailPlain, Aplain, A11, hInv, Matrix.mul_apply]
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

lemma ldlHeadBlock_mul_lowerFactorTranspose
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R) (hPos : A.PosDef) :
    let Aplain := ldlHeadTailPlain ι A
    let A11 : Matrix Unit Unit R := Aplain.toBlocks₁₁
    A11 * (ldlLowerFactor ι A)ᵀ = Aplain.toBlocks₁₂ := by
  classical
  intro Aplain A11
  have h21 : Aplain.toBlocks₂₁ = Aplain.toBlocks₁₂ᵀ := by
    have hAplainPos : Aplain.PosDef := posDef_reindex_equiv (e := headTailEquiv (α := ι)) hPos
    ext i j
    have hEq := congrArg (fun M => M (Sum.inr i) (Sum.inl j)) hAplainPos.1.eq
    simpa [Aplain, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂] using hEq.symm
  have hlower : ldlLowerFactor ι A * A11 = Aplain.toBlocks₂₁ :=
    ldlLowerFactor_mul_headBlock A hPos
  have htranspose := congrArg Matrix.transpose hlower
  simpa [Matrix.transpose_mul, h21, A11, Matrix.transpose_submatrix, Matrix.submatrix_id_id]
    using htranspose

omit [DecidableEq ι] in
lemma ldlSchur_restore
    {R : Type*} [Ring R] [Inv R]
    (A : Matrix ι ι R) :
    let Aplain := ldlHeadTailPlain ι A
    ldlSchurSlice ι A + ldlLowerFactor ι A * Aplain.toBlocks₁₂ = Aplain.toBlocks₂₂ := by
  classical
  intro Aplain
  dsimp [ldlSchurSlice, ldlLowerFactor, ldlHeadTailPlain, Aplain]
  abel


theorem ldlHeadTailSchurLift
    {R : Type*} [RCLike R] [TrivialStar R]
    (A : Matrix ι ι R)
    (hPos : A.PosDef)
    (hP : HasLDLDecomposition (ldlSchurSlice ι A)) :
    HasLDLDecomposition A := by
  classical
  let Aplain : Matrix (Unit ⊕ LDLTailIdx ι) (Unit ⊕ LDLTailIdx ι) R :=
    ldlHeadTailPlain ι A
  let A11 : Matrix Unit Unit R := Aplain.toBlocks₁₁
  let A12 : Matrix Unit (LDLTailIdx ι) R := Aplain.toBlocks₁₂
  let l : Matrix (LDLTailIdx ι) Unit R := ldlLowerFactor ι A
  rcases hP with ⟨factors, hProps', hEq'⟩
  rcases factors with ⟨L', D'⟩
  rcases hProps' with ⟨hL', hDiag', hPosD'⟩
  have hEqSchur : ldlSchurSlice ι A = L' * D' * L'ᵀ := by
    simpa [HasLDLDecomposition, LDL_Schema] using hEq'
  let Lplain : Matrix (Unit ⊕ LDLTailIdx ι) (Unit ⊕ LDLTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 l L'
  let Dplain : Matrix (Unit ⊕ LDLTailIdx ι) (Unit ⊕ LDLTailIdx ι) R :=
    fromBlocks A11 0 0 D'
  let s : Unit ⊕ LDLTailIdx ι ≃ Unit ⊕ₗ LDLTailIdx ι :=
    sumToLexEquiv Unit (LDLTailIdx ι)
  let e : ι ≃ Unit ⊕ₗ LDLTailIdx ι := headTailLexEquiv (α := ι)
  let Lblk : Matrix (Unit ⊕ₗ LDLTailIdx ι) (Unit ⊕ₗ LDLTailIdx ι) R :=
    fromBlocks (1 : Matrix Unit Unit R) 0 l L'
  have hA11Diag : A11.IsDiag := isDiag_subsingleton A11
  have hDplainDiag : Dplain.IsDiag := by
    simpa [Dplain] using Matrix.IsDiag.fromBlocks hA11Diag hDiag'
  have hA11Positive : PositiveDiagonal A11 := by
    intro i
    cases i
    simpa [A11] using (ldlHeadBlock_posDef A hPos).diag_pos
  have hDplainPositive : PositiveDiagonal Dplain := by
    intro x
    rcases x with (_ | x)
    · simpa [Dplain, PositiveDiagonal] using hA11Positive ()
    · simpa [Dplain, PositiveDiagonal] using hPosD' x
  have hLblk : IsUnitLowerTriangular Lblk := by
    rcases hL' with ⟨hLower, hdiag⟩
    constructor
    · dsimp [IsLowerTriangular, IsUpperTriangular, BlockTriangular, Lblk] at hLower ⊢
      intro i j hij
      rcases i with (_ | i)
      · rcases j with (_ | j)
        · simp at hij
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
  have hlower : l * A11 = Aplain.toBlocks₂₁ :=
    ldlLowerFactor_mul_headBlock A hPos
  have hupper : A11 * lᵀ = A12 :=
    ldlHeadBlock_mul_lowerFactorTranspose A hPos
  have hrestore : ldlSchurSlice ι A + l * A12 = Aplain.toBlocks₂₂ :=
    ldlSchur_restore A
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
            Aplain.toBlocks₂₂ = ldlSchurSlice ι A + l * A12 := by
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
  · refine ⟨?_, ?_, ?_⟩
    · have hLlex :
          IsUnitLowerTriangular (Matrix.reindex e.symm e.symm Lblk) := by
        exact
          (isUnitLowerTriangular_reindex
            (e := e)
            (h_mono := headTailLexEquiv_strictMono (α := ι))
            (A := Matrix.reindex e.symm e.symm Lblk)).2
            (by simpa using hLblk)
      have hL_eq : Matrix.reindex e.symm e.symm Lblk = L := by
        have hLblk_eq : Matrix.reindex s s Lplain = Lblk := by
          simpa [Lplain, Lblk, s] using
            (reindex_sumToLex_fromBlocks
              (A₁₁ := (1 : Matrix Unit Unit R)) (A₁₂ := 0) (A₂₁ := l) (A₂₂ := L'))
        calc
          Matrix.reindex e.symm e.symm Lblk =
              Matrix.reindex e.symm e.symm (Matrix.reindex s s Lplain) := by
            rw [hLblk_eq]
          _ = L := by
            ext i j
            simp [L, Lplain, e, s, headTailLexEquiv, Matrix.reindex_apply]
      simpa [hL_eq] using hLlex
    · exact isDiag_reindex_equiv (e := (headTailEquiv (α := ι)).symm) hDplainDiag
    · exact positiveDiagonal_reindex_equiv (e := (headTailEquiv (α := ι)).symm) hDplainPositive
  · have hEqPlain' : Aplain = Lplain * (Dplain * Lplainᵀ) := by
        simpa [Matrix.mul_assoc] using hEqPlain
    have hEqRe := congrArg
        (Matrix.reindex (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm)
        hEqPlain'
    have hRhsReindex :
        Matrix.reindex (headTailEquiv (α := ι)).symm (headTailEquiv (α := ι)).symm
            (Lplain * (Dplain * Lplainᵀ)) = L * (D * Lᵀ) := by
      simp [L, D, Matrix.submatrix_mul_equiv]
    rw [hRhsReindex] at hEqRe
    simpa [Aplain, ldlHeadTailPlain, LDL_Schema, Matrix.mul_assoc] using hEqRe


end RecursiveHelpers

noncomputable def ldl_strategy_core {R : Type*} [RCLike R] [TrivialStar R] :
    SquareStrategyCore R where
  SliceIdx := fun {ι} fι dι oι nι => @LDLTailIdx ι fι oι nι
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
        reduction := ldlHeadTailReduction (R := R) ι
        goal_is_sliceable := by rfl
        μ := fun _ => Fintype.card ι
        μ_slice := fun _ => Fintype.card (LDLTailIdx ι)
        μ_mono := ?_
        slice_progress := ?_ }
    · intro A t
      cases t
      simp
    · intro A hA
      have hlt : Fintype.card (LDLTailIdx ι) < Fintype.card ι := by
        simpa [LDLTailIdx] using
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

def LDL_P_sub {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (x_sub : PosSquareUniverse R) : Prop :=
  LDL_P (x_sub : SquareUniverse R)

@[simp] theorem ldl_P_compat
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (x_sub : PosSquareUniverse R) :
    LDL_P_sub x_sub ↔ LDL_P (x_sub : SquareUniverse R) :=
  Iff.rfl

theorem ldl_base_univ
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (x : SquareUniverse R) :
    ((∀ (x_sub : PosSquareUniverse R), (x_sub : SquareUniverse R) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      LDL_P x := by
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
  exact base_ldl_empty x.A

noncomputable def ldl_strategy_proof {R : Type*} [RCLike R] [TrivialStar R] :
    SquareStrategyProofData R LDL_P ldl_strategy_core where
  transport := by
    intro ι fι dι oι nι A B hBA hP
    rcases hBA with rfl | ⟨t, rfl⟩
    · exact hP
    · simpa [ldl_strategy_core, trivialSquareTransform] using hP
  lift := by
    intro ι fι dι oι nι A hA hP hPos
    have hSlicePos : (ldlSchurSlice ι A).PosDef :=
      ldlSchurSlice_posDef A hPos
    exact ldlHeadTailSchurLift A hPos
      (by
        refine hP ?_
        simpa [ldl_strategy_core, ldlHeadTailReduction] using hSlicePos)

noncomputable def ldl_strategy_data {R : Type*} [RCLike R] [TrivialStar R] :
    SquareStrategyData R LDL_P :=
  mkSquareStrategyData ldl_strategy_core ldl_strategy_proof

end Presentation

end MatDecompFormal.Instances
