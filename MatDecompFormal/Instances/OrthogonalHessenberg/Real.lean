/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.OrthogonalHessenberg.Concrete
import MatDecompFormal.Instances.QR.Givens
import MatDecompFormal.Instances.QR.Householder
import MatDecompFormal.Instances.QR.Recursive

universe u

namespace MatDecompFormal.Instances

open Matrix
open InnerProductSpace
open MatDecompFormal.Framework

/-!
# Real Orthogonal Hessenberg Reduction

This file instantiates the same boundary-column descent template as the complex
unitary development, but with real orthogonal similarities and transpose.
-/

/-- Matrix-level real orthogonal Hessenberg reduction target. -/
def HasOrthogonalHessenberg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : Prop :=
  ∃ Q : Matrix ι ι ℝ, ∃ H : Matrix ι ι ℝ,
    IsOrthogonalMatrix Q ∧
    IsUpperHessenberg H ∧
    A = Q * H * Qᵀ

/-- Real Hessenberg reduction whose final orthogonal factor is a Householder product. -/
def HasHouseholderProductHessenberg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : Prop :=
  ∃ Q : Matrix ι ι ℝ, ∃ H : Matrix ι ι ℝ,
    IsHouseholderProduct Q ∧
    IsOrthogonalMatrix Q ∧
    IsUpperHessenberg H ∧
    A = Q * H * Qᵀ

/-- Real Hessenberg reduction whose final orthogonal factor is a Givens product. -/
def HasGivensProductHessenberg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : Prop :=
  ∃ Q : Matrix ι ι ℝ, ∃ H : Matrix ι ι ℝ,
    IsGivensProduct Q ∧
    IsOrthogonalMatrix Q ∧
    IsUpperHessenberg H ∧
    A = Q * H * Qᵀ

/--
Product-level Hessenberg trace predicate.

This records a finite list of elementary factors whose product is the final
orthogonal similarity factor. It is a witness-level strengthening of ordinary
Hessenberg reduction, but does not by itself assert an executable pivot policy.
-/
def OrthogonalHessenbergTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (StepProp : Matrix ι ι ℝ → Prop) (A : Matrix ι ι ℝ) : Prop :=
  ∃ steps : List (Matrix ι ι ℝ), ∃ Q H : Matrix ι ι ℝ,
    (∀ M ∈ steps, StepProp M) ∧
    matrixProduct steps = Q ∧
    IsOrthogonalMatrix Q ∧
    IsUpperHessenberg H ∧
    A = Q * H * Qᵀ

abbrev HouseholderHessenbergTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : Prop :=
  OrthogonalHessenbergTrace IsHouseholderMatrix A

abbrev GivensHessenbergTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : Prop :=
  OrthogonalHessenbergTrace IsGivensMatrix A

theorem hasOrthogonalHessenberg_of_hasHouseholderProductHessenberg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℝ} :
    HasHouseholderProductHessenberg A → HasOrthogonalHessenberg A := by
  intro hA
  rcases hA with ⟨Q, H, _hQprod, hQ, hH, hEq⟩
  exact ⟨Q, H, hQ, hH, hEq⟩

theorem hasOrthogonalHessenberg_of_hasGivensProductHessenberg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℝ} :
    HasGivensProductHessenberg A → HasOrthogonalHessenberg A := by
  intro hA
  rcases hA with ⟨Q, H, _hQprod, hQ, hH, hEq⟩
  exact ⟨Q, H, hQ, hH, hEq⟩

theorem hasHouseholderProductHessenberg_of_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℝ} :
    HouseholderHessenbergTrace A → HasHouseholderProductHessenberg A := by
  intro hA
  rcases hA with ⟨steps, Q, H, hsteps, hprod, hQ, hH, hEq⟩
  exact ⟨Q, H, ⟨steps, hsteps, hprod⟩, hQ, hH, hEq⟩

theorem hasGivensProductHessenberg_of_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℝ} :
    GivensHessenbergTrace A → HasGivensProductHessenberg A := by
  intro hA
  rcases hA with ⟨steps, Q, H, hsteps, hprod, hQ, hH, hEq⟩
  exact ⟨Q, H, ⟨steps, hsteps, hprod⟩, hQ, hH, hEq⟩

theorem hasOrthogonalHessenberg_of_householderTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℝ} :
    HouseholderHessenbergTrace A → HasOrthogonalHessenberg A :=
  hasOrthogonalHessenberg_of_hasHouseholderProductHessenberg ∘
    hasHouseholderProductHessenberg_of_trace

theorem hasOrthogonalHessenberg_of_givensTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℝ} :
    GivensHessenbergTrace A → HasOrthogonalHessenberg A :=
  hasOrthogonalHessenberg_of_hasGivensProductHessenberg ∘
    hasGivensProductHessenberg_of_trace

/--
Boundary-aware real orthogonal Hessenberg target.

The same orthogonal similarity that reduces `A` must transform the protected
boundary column into a first-entry-only column.
-/
def HasOrthogonalHessenbergBoundary
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (c : Matrix ι Unit ℝ) : Prop :=
  ∃ Q : Matrix ι ι ℝ, ∃ H : Matrix ι ι ℝ,
    IsOrthogonalMatrix Q ∧
    IsUpperHessenberg H ∧
    A = Q * H * Qᵀ ∧
    ∀ i : ι, i ≠ headElem (α := ι) → (Qᵀ * c) i () = 0

/-- Boundary-universe real orthogonal Hessenberg predicate. -/
def OrthogonalHessenbergBoundary_P (x : HessenbergBoundaryUniverse.{u} ℝ) : Prop :=
  ∀ (_h : Nonempty x.ι), @HasOrthogonalHessenbergBoundary x.ι x.fintype_ι
    x.decEq_ι x.linOrder_ι _h x.A x.c

/-- An orthogonal matrix gives the explicit inverse witness used by ordinary Hessenberg. -/
theorem hasMatrixInverse_of_isOrthogonalMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Matrix ι ι ℝ} (hQ : IsOrthogonalMatrix Q) :
    HasMatrixInverse Q Qᵀ := by
  constructor
  · exact hQ
  · have hQT : IsOrthogonalMatrix Qᵀ := isOrthogonalMatrix_transpose hQ
    simpa [IsOrthogonalMatrix] using hQT

/-- Forget the orthogonal condition from a real orthogonal Hessenberg witness. -/
theorem hasHessenberg_of_hasOrthogonalHessenberg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℝ} :
    HasOrthogonalHessenberg A → HasHessenberg A := by
  intro hA
  rcases hA with ⟨Q, H, hQ, hH, hEq⟩
  exact ⟨Q, Qᵀ, H, hasMatrixInverse_of_isOrthogonalMatrix hQ, hH, hEq⟩

/-- Subsingleton matrices have the trivial real orthogonal Hessenberg decomposition. -/
theorem base_orthogonalHessenberg_subsingleton
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Subsingleton ι]
    (A : Matrix ι ι ℝ) :
    HasOrthogonalHessenberg A := by
  refine ⟨1, A, isOrthogonalMatrix_one, ?_, ?_⟩
  · exact isUpperHessenberg_subsingleton A
  · simp

/-- Boundary object obtained by applying a real orthogonal similarity. -/
noncomputable def orthogonalHessenbergBoundarySimilarityObject
    (x : HessenbergBoundaryUniverse.{u} ℝ)
    (Q : Matrix x.ι x.ι ℝ) : HessenbergBoundaryUniverse.{u} ℝ :=
  { ι := x.ι
    A := Qᵀ * x.A * Q
    c := Qᵀ * x.c }

/-- One-step real orthogonal boundary oracle for Hessenberg reduction. -/
structure OrthogonalHessenbergBoundaryStepOracle where
  Q :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℝ,
      Matrix x_sub.1.ι x_sub.1.ι ℝ
  orthogonal_Q :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℝ,
      IsOrthogonalMatrix (Q x_sub)
  ready :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℝ,
      HessenbergBoundaryReady
        (orthogonalHessenbergBoundarySimilarityObject
          (x_sub : HessenbergBoundaryUniverse.{u} ℝ) (Q x_sub))

/-- Orthogonally transformed positive boundary object. -/
noncomputable def orthogonalHessenbergBoundaryStepObject
    (oracle : OrthogonalHessenbergBoundaryStepOracle.{u})
    (x_sub : PosHessenbergBoundaryUniverse ℝ) :
    PosHessenbergBoundaryUniverse ℝ :=
  ⟨orthogonalHessenbergBoundarySimilarityObject
      (x_sub : HessenbergBoundaryUniverse.{u} ℝ) (oracle.Q x_sub),
    by simpa [orthogonalHessenbergBoundarySimilarityObject] using x_sub.2⟩

/-- Relation generated by one oracle-provided real orthogonal similarity step. -/
def orthogonalHessenbergBoundaryStepRel
    (oracle : OrthogonalHessenbergBoundaryStepOracle.{u})
    (y_sub x_sub : PosHessenbergBoundaryUniverse ℝ) : Prop :=
  y_sub = orthogonalHessenbergBoundaryStepObject oracle x_sub

/-- Boundary target transport across a same-index real orthogonal similarity. -/
theorem orthogonalHessenbergBoundary_transport_orthogonalSimilarity
    (x : HessenbergBoundaryUniverse.{u} ℝ)
    (Q : Matrix x.ι x.ι ℝ)
    (hQ : IsOrthogonalMatrix Q)
    (hY :
      OrthogonalHessenbergBoundary_P
        (orthogonalHessenbergBoundarySimilarityObject x Q)) :
    OrthogonalHessenbergBoundary_P x := by
  intro hxNonempty
  have hY' :
      HasOrthogonalHessenbergBoundary (Qᵀ * x.A * Q) (Qᵀ * x.c) := by
    simpa [orthogonalHessenbergBoundarySimilarityObject] using hY hxNonempty
  rcases hY' with ⟨S, H, hS, hH, hEqY, hBoundaryY⟩
  have hQQT : Q * Qᵀ = 1 := (hasMatrixInverse_of_isOrthogonalMatrix hQ).2
  refine ⟨Q * S, H, isOrthogonalMatrix_mul hQ hS, hH, ?_, ?_⟩
  · calc
      x.A = (Q * Qᵀ) * x.A * (Q * Qᵀ) := by
        simp [hQQT]
      _ = Q * (Qᵀ * x.A * Q) * Qᵀ := by
        simp [Matrix.mul_assoc]
      _ = Q * (S * H * Sᵀ) * Qᵀ := by
        rw [hEqY]
      _ = (Q * S) * H * (Q * S)ᵀ := by
        rw [Matrix.transpose_mul]
        simp [Matrix.mul_assoc]
  · intro i hi
    have hboundary := hBoundaryY i hi
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using hboundary

/-- Block-diagonal tail orthogonal lift for the boundary target. -/
theorem hasOrthogonalHessenbergBoundary_fromBlocks_of_tail
    {β : Type*} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    (A₁₁ : Matrix Unit Unit ℝ) (A₁₂ : Matrix Unit β ℝ)
    (A₂₁ : Matrix β Unit ℝ) (A₂₂ : Matrix β β ℝ)
    (c : Matrix (Unit ⊕ₗ β) Unit ℝ)
    (hc : ∀ i : β, c (Sum.inrₗ i) () = 0)
    (hTail : HasOrthogonalHessenbergBoundary A₂₂ A₂₁) :
    HasOrthogonalHessenbergBoundary (ι := Unit ⊕ₗ β)
      (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℝ)
      c := by
  rcases hTail with ⟨Qtail, Htail, hQtail, hHTail, hEqTail, hBoundaryTail⟩
  let Qblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℝ := hessenbergBlockDiagOne Qtail
  let Hblk : Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℝ :=
    fromBlocks A₁₁ (A₁₂ * Qtail) (Qtailᵀ * A₂₁) Htail
  have hInvTail : HasMatrixInverse Qtail Qtailᵀ :=
    hasMatrixInverse_of_isOrthogonalMatrix hQtail
  have hQblk_transpose :
      Qblkᵀ = hessenbergBlockDiagOne Qtailᵀ := by
    change (hessenbergBlockDiagOne Qtail)ᵀ = hessenbergBlockDiagOne Qtailᵀ
    rw [hessenbergBlockDiagOne, hessenbergBlockDiagOne]
    rw [Matrix.fromBlocks_transpose]
    simp
  refine ⟨Qblk, Hblk, ?_, ?_, ?_, ?_⟩
  · exact isOrthogonalMatrix_blockDiag_one hQtail
  · exact
      isUpperHessenberg_fromBlocks_ready
        A₁₁ (A₁₂ * Qtail) (Qtailᵀ * A₂₁) Htail hBoundaryTail hHTail
  · rw [hQblk_transpose]
    simpa [Qblk, Hblk] using
      hessenbergBlockDiagOne_parentBlock_eq
        A₁₁ A₁₂ A₂₁ A₂₂ Htail Qtail Qtailᵀ hInvTail hEqTail
  · intro i hi
    cases h : ofLex i with
    | inl u =>
        cases u
        have hi_eq : i = (Sum.inlₗ () : Unit ⊕ₗ β) := by
          rw [← toLex_ofLex i, h]
        exact False.elim (hi (by simpa [headElem_sumLex_unit] using hi_eq))
    | inr j =>
        have hi_eq : i = (Sum.inrₗ j : Unit ⊕ₗ β) := by
          rw [← toLex_ofLex i, h]
        subst i
        have htail :=
          hessenbergBlockDiagOne_mul_readyColumn_tail Qtailᵀ c hc j
        rw [hQblk_transpose]
        exact htail

/-- Lift from a ready boundary object and its recursive real orthogonal tail witness. -/
theorem orthogonalHessenbergBoundary_lift_from_ready
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ)
    (hReady : HessenbergBoundaryReady (x_sub : HessenbergBoundaryUniverse.{u} ℝ))
    (hTail : OrthogonalHessenbergBoundary_P (hessenbergBoundarySliceSub x_sub)) :
    OrthogonalHessenbergBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} ℝ) := by
  intro hxNonempty
  letI : Nonempty x_sub.1.ι := hxNonempty
  let β := HessenbergTailIdx x_sub.1.ι
  let Aplain : Matrix (Unit ⊕ β) (Unit ⊕ β) ℝ :=
    hessenbergBoundaryHeadTailMatrix x_sub.1.ι x_sub.1.A
  let cblk : Matrix (Unit ⊕ₗ β) Unit ℝ :=
    Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι)) (Equiv.refl Unit) x_sub.1.c
  by_cases hβ : Nonempty β
  · letI : Nonempty β := hβ
    have hTailBoundary :
        HasOrthogonalHessenbergBoundary Aplain.toBlocks₂₂ Aplain.toBlocks₂₁ := by
      have hP := hTail hβ
      simpa [hessenbergBoundarySliceSub, hessenbergTailSlice_eq_boundaryLowerRightBlock,
        hessenbergBoundaryLowerLeftColumn, Aplain] using hP
    have hcblk : ∀ i : β, cblk (Sum.inrₗ i) () = 0 := by
      intro i
      simpa [cblk, headTailLexEquiv_symm_apply_inr] using
        hReady hxNonempty i i.2
    have hBlock : HasOrthogonalHessenbergBoundary (ι := Unit ⊕ₗ β)
        (fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ :
          Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℝ)
        cblk :=
      hasOrthogonalHessenbergBoundary_fromBlocks_of_tail Aplain.toBlocks₁₁ Aplain.toBlocks₁₂
        Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ cblk hcblk hTailBoundary
    have hLexEq :
        Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι))
          (headTailLexEquiv (α := x_sub.1.ι)) x_sub.1.A =
        (fromBlocks Aplain.toBlocks₁₁ Aplain.toBlocks₁₂ Aplain.toBlocks₂₁ Aplain.toBlocks₂₂ :
          Matrix (Unit ⊕ₗ β) (Unit ⊕ₗ β) ℝ) := by
      simpa [Aplain, β] using hessenbergBoundaryHeadTailLex_fromBlocks x_sub.1.ι x_sub.1.A
    have hLex : HasOrthogonalHessenbergBoundary
        (Matrix.reindex (headTailLexEquiv (α := x_sub.1.ι))
          (headTailLexEquiv (α := x_sub.1.ι)) x_sub.1.A)
        cblk := by
      rw [hLexEq]
      exact hBlock
    rcases hLex with ⟨Q, H, hQ, hH, hEq, hBoundary⟩
    let e := headTailLexEquiv (α := x_sub.1.ι)
    let Q0 : Matrix x_sub.1.ι x_sub.1.ι ℝ := Matrix.reindex e.symm e.symm Q
    let H0 : Matrix x_sub.1.ι x_sub.1.ι ℝ := Matrix.reindex e.symm e.symm H
    refine ⟨Q0, H0, ?_, ?_, ?_, ?_⟩
    · exact (isOrthogonalMatrix_reindex e.symm Q).1 hQ
    · exact
        (isUpperHessenberg_reindex_strictMono
          (e := e.symm)
          (h_mono := by
            intro x y hxy
            have hxy' : e (e.symm x) < e (e.symm y) := by
              simpa using hxy
            exact (headTailLexEquiv_strictMono (α := x_sub.1.ι)).lt_iff_lt.mp hxy')
          (A := H)).2 hH
    · have hback := congrArg (Matrix.reindex e.symm e.symm) hEq
      simpa [Q0, H0, e, Matrix.transpose_reindex, Matrix.submatrix_mul_equiv,
        Matrix.mul_assoc] using hback
    · intro i hi
      have hb : (Qᵀ * cblk) (e i) () = 0 := by
        apply hBoundary
        intro heq
        apply hi
        have hhead := headElem_map_strictMono e
          (headTailLexEquiv_strictMono (α := x_sub.1.ι))
        exact e.injective (by simpa [hhead] using heq)
      have hmul := reindex_mul_column e Qᵀ x_sub.1.c
      have hb_re := congrFun (congrFun hmul i) ()
      have hb0 : ((Matrix.reindex e.symm e.symm Qᵀ) * x_sub.1.c) i () = 0 := by
        rw [← hb_re]
        exact hb
      simpa [Q0, Matrix.transpose_reindex] using hb0
  · have hsub : Subsingleton x_sub.1.ι := by
      refine ⟨?_⟩
      intro a b
      by_cases ha : a = headElem (α := x_sub.1.ι)
      · by_cases hb : b = headElem (α := x_sub.1.ι)
        · rw [ha, hb]
        · have : Nonempty β := ⟨⟨b, hb⟩⟩
          exact False.elim (hβ this)
      · have : Nonempty β := ⟨⟨a, ha⟩⟩
        exact False.elim (hβ this)
    letI : Subsingleton x_sub.1.ι := hsub
    refine ⟨1, x_sub.1.A, isOrthogonalMatrix_one, ?_, ?_, ?_⟩
    · exact isUpperHessenberg_subsingleton x_sub.1.A
    · simp
    · intro i hi
      exact False.elim (hi (Subsingleton.elim _ _))

/-- Proof-side data for the real orthogonal boundary-column descent. -/
structure OrthogonalHessenbergBoundaryProofData where
  r_sub :
    PosHessenbergBoundaryUniverse ℝ → PosHessenbergBoundaryUniverse ℝ → Prop
  IsSliceable_sub : PosHessenbergBoundaryUniverse ℝ → Prop
  slice_sub :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℝ,
      IsSliceable_sub x_sub → HessenbergBoundaryUniverse.{u} ℝ
  transport_sub :
    ∀ {x_sub y_sub : PosHessenbergBoundaryUniverse ℝ},
      r_sub y_sub x_sub →
        OrthogonalHessenbergBoundary_P (y_sub : HessenbergBoundaryUniverse.{u} ℝ) →
          OrthogonalHessenbergBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} ℝ)
  lift_from_slice_sub :
    ∀ (x_sub : PosHessenbergBoundaryUniverse ℝ) (hx : IsSliceable_sub x_sub),
      OrthogonalHessenbergBoundary_P (slice_sub x_sub hx) →
        OrthogonalHessenbergBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} ℝ)
  reach_sub :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℝ,
      hessenbergBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} ℝ) >
        hessenbergBoundaryμBase →
        Σ' (y_sub : PosHessenbergBoundaryUniverse ℝ),
          Σ' (hy : IsSliceable_sub y_sub),
            r_sub y_sub x_sub ∧
              hessenbergBoundaryμ (slice_sub y_sub hy) <
                hessenbergBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} ℝ)

/-- Convert a real orthogonal one-step oracle into proof-side descent data. -/
noncomputable def orthogonalHessenbergBoundaryProofDataOfStepOracle
    (oracle : OrthogonalHessenbergBoundaryStepOracle.{u}) :
    OrthogonalHessenbergBoundaryProofData.{u} where
  r_sub := orthogonalHessenbergBoundaryStepRel oracle
  IsSliceable_sub := fun x_sub =>
    HessenbergBoundaryReady (x_sub : HessenbergBoundaryUniverse.{u} ℝ)
  slice_sub := fun x_sub _ => hessenbergBoundarySliceSub x_sub
  transport_sub := by
    intro x_sub y_sub hrel hP
    subst hrel
    exact
      orthogonalHessenbergBoundary_transport_orthogonalSimilarity
        (x_sub : HessenbergBoundaryUniverse.{u} ℝ)
        (oracle.Q x_sub) (oracle.orthogonal_Q x_sub) hP
  lift_from_slice_sub := by
    intro x_sub hx hP
    exact orthogonalHessenbergBoundary_lift_from_ready x_sub hx hP
  reach_sub := by
    intro x_sub hgt
    let y_sub := orthogonalHessenbergBoundaryStepObject oracle x_sub
    have hslice : HessenbergBoundaryReady (y_sub : HessenbergBoundaryUniverse.{u} ℝ) := by
      simpa [y_sub, orthogonalHessenbergBoundaryStepObject] using oracle.ready x_sub
    have hmono :
        hessenbergBoundaryμ (y_sub : HessenbergBoundaryUniverse.{u} ℝ) ≤
          hessenbergBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} ℝ) := by
      simp [y_sub, orthogonalHessenbergBoundaryStepObject,
        orthogonalHessenbergBoundarySimilarityObject, hessenbergBoundaryμ]
    exact
      ⟨y_sub, hslice, rfl,
        lt_of_lt_of_le (hessenbergBoundarySliceProgress y_sub) hmono⟩

/-- Boundary base case for the real orthogonal target. -/
theorem orthogonalHessenbergBoundary_base_univ
    (x : HessenbergBoundaryUniverse.{u} ℝ) :
    ((∀ x_sub : PosHessenbergBoundaryUniverse ℝ,
        (x_sub : HessenbergBoundaryUniverse ℝ) ≠ x) ∨
      hessenbergBoundaryμ x ≤ hessenbergBoundaryμBase) →
      OrthogonalHessenbergBoundary_P x := by
  intro hx hne
  have hzero : Fintype.card x.ι = 0 :=
    hessenbergBoundaryBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  exact False.elim (IsEmpty.false (Classical.choice hne))

/-- Subtype-induction instance for the real orthogonal boundary-column descent. -/
noncomputable def orthogonalHessenbergBoundary_framework_inst
    (proofData : OrthogonalHessenbergBoundaryProofData.{u}) :
    SubtypeInductionInstance
      (HessenbergBoundaryUniverse.{u} ℝ)
      (PosHessenbergBoundaryUniverse ℝ)
      (fun x => (x : HessenbergBoundaryUniverse.{u} ℝ)) where
  μ := hessenbergBoundaryμ
  μ_base := hessenbergBoundaryμBase
  P := OrthogonalHessenbergBoundary_P
  P_sub := fun x_sub =>
    OrthogonalHessenbergBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} ℝ)
  P_compat := by
    intro x_sub
    rfl
  r_sub := proofData.r_sub
  IsSliceable_sub := proofData.IsSliceable_sub
  slice_sub := proofData.slice_sub
  transport_sub := by
    intro x_sub y_sub hrel hP
    exact proofData.transport_sub hrel hP
  lift_from_slice_sub := by
    intro x_sub hx hP
    exact proofData.lift_from_slice_sub x_sub hx hP
  reach_sub := by
    intro x_sub hgt
    exact proofData.reach_sub x_sub hgt
  base_univ := orthogonalHessenbergBoundary_base_univ

/-- Boundary-column framework theorem for real orthogonal Hessenberg reduction. -/
theorem exists_orthogonalHessenbergBoundary_framework
    (proofData : OrthogonalHessenbergBoundaryProofData.{u})
    (x : HessenbergBoundaryUniverse.{u} ℝ) :
    OrthogonalHessenbergBoundary_P x := by
  let inst :
      SubtypeInductionInstance
        (HessenbergBoundaryUniverse.{u} ℝ)
        (PosHessenbergBoundaryUniverse ℝ)
        (fun x => (x : HessenbergBoundaryUniverse.{u} ℝ)) :=
    orthogonalHessenbergBoundary_framework_inst proofData
  exact
    (SubtypeInductionInstance.prove inst) x

/-- Forget the protected boundary-column condition from a real orthogonal boundary witness. -/
theorem hasOrthogonalHessenberg_of_hasOrthogonalHessenbergBoundary
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι ℝ} {c : Matrix ι Unit ℝ} :
    HasOrthogonalHessenbergBoundary A c → HasOrthogonalHessenberg A := by
  intro h
  rcases h with ⟨Q, H, hQ, hHess, hEq, _hBoundary⟩
  exact ⟨Q, H, hQ, hHess, hEq⟩

/--
Real orthogonal Hessenberg reduction through the boundary-column descent driver,
conditional on a real orthogonal one-step oracle.
-/
theorem exists_orthogonal_hessenberg_reduction_of_oracle
    (oracle : OrthogonalHessenbergBoundaryStepOracle.{u})
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    HasOrthogonalHessenberg A := by
  by_cases hne : Nonempty ι
  · let x : HessenbergBoundaryUniverse.{u} ℝ :=
      { ι := ι
        A := A
        c := 0 }
    have hP : OrthogonalHessenbergBoundary_P x :=
      exists_orthogonalHessenbergBoundary_framework
        (orthogonalHessenbergBoundaryProofDataOfStepOracle oracle) x
    have hBoundary : HasOrthogonalHessenbergBoundary A (0 : Matrix ι Unit ℝ) := by
      simpa [x] using hP hne
    exact hasOrthogonalHessenberg_of_hasOrthogonalHessenbergBoundary hBoundary
  · letI : IsEmpty ι := not_nonempty_iff.mp hne
    letI : Subsingleton ι := by infer_instance
    exact base_orthogonalHessenberg_subsingleton A

/-- Boundary column as a vector in real Euclidean space. -/
noncomputable def realBoundaryColumnVec
    {ι : Type u} [Fintype ι] (c : Matrix ι Unit ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => c i ())

lemma realBoundaryColumnVec_ne_zero
    {ι : Type u} [Fintype ι] {c : Matrix ι Unit ℝ} (hc : c ≠ 0) :
    realBoundaryColumnVec c ≠ 0 := by
  intro hvec
  apply hc
  have hfun : (fun i => c i ()) = 0 := (WithLp.toLp_eq_zero 2).mp hvec
  ext i j
  cases j
  exact congrFun hfun i

/-- Normalized nonzero real boundary column. -/
noncomputable def normalizedRealBoundaryColumn
    {ι : Type u} [Fintype ι] (c : Matrix ι Unit ℝ) (_hc : c ≠ 0) :
    EuclideanSpace ℝ ι :=
  (‖realBoundaryColumnVec c‖)⁻¹ • realBoundaryColumnVec c

lemma normalizedRealBoundaryColumn_norm
    {ι : Type u} [Fintype ι] (c : Matrix ι Unit ℝ) (hc : c ≠ 0) :
    ‖normalizedRealBoundaryColumn c hc‖ = 1 := by
  simpa [normalizedRealBoundaryColumn] using
    (norm_smul_inv_norm (realBoundaryColumnVec_ne_zero hc))

lemma real_orthonormal_singleton_head_const
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (v : EuclideanSpace ℝ ι) (hv : ‖v‖ = 1) :
    Orthonormal ℝ
      (({headElem (α := ι)} : Set ι).restrict (fun _ : ι => v)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hi : i.1 = headElem (α := ι) := Set.mem_singleton_iff.mp i.2
  have hj : j.1 = headElem (α := ι) := Set.mem_singleton_iff.mp j.2
  have hij : i = j := by
    apply Subtype.ext
    rw [hi, hj]
  subst hij
  simp [inner_self_eq_norm_sq_to_K, hv]

/--
A real orthonormal basis whose head vector is the normalized active boundary
column, with the standard basis used in the zero-column case.
-/
noncomputable def realBoundaryColumnBasis
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (c : Matrix ι Unit ℝ) :
    OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) := by
  classical
  by_cases hc : c = 0
  · exact EuclideanSpace.basisFun ι ℝ
  · exact Classical.choose
      (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℝ) (E := EuclideanSpace ℝ ι) (ι := ι)
        (card_ι := by simp)
        (s := {headElem (α := ι)})
        (v := fun _ : ι => normalizedRealBoundaryColumn c hc)
        (real_orthonormal_singleton_head_const
          (normalizedRealBoundaryColumn c hc)
          (normalizedRealBoundaryColumn_norm c hc)))

lemma realBoundaryColumnBasis_head
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (c : Matrix ι Unit ℝ) (hc : c ≠ 0) :
    realBoundaryColumnBasis c (headElem (α := ι)) =
      normalizedRealBoundaryColumn c hc := by
  classical
  unfold realBoundaryColumnBasis
  simp [hc]
  simpa using
    Classical.choose_spec
      (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℝ) (E := EuclideanSpace ℝ ι) (ι := ι)
        (card_ι := by simp)
        (s := {headElem (α := ι)})
        (v := fun _ : ι => normalizedRealBoundaryColumn c hc)
        (real_orthonormal_singleton_head_const
          (normalizedRealBoundaryColumn c hc)
          (normalizedRealBoundaryColumn_norm c hc)))
      (headElem (α := ι)) (by simp)

/-- Matrix whose columns are a real orthonormal basis of `EuclideanSpace ℝ ι`. -/
noncomputable def matrixOfRealOrthonormalBasis
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    Matrix ι ι ℝ :=
  (EuclideanSpace.basisFun ι ℝ).toBasis.toMatrix b.toBasis

lemma matrixOfRealOrthonormalBasis_orthogonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    IsOrthogonalMatrix (matrixOfRealOrthonormalBasis b) := by
  have hmem : matrixOfRealOrthonormalBasis b ∈ Matrix.orthogonalGroup ι ℝ :=
    (EuclideanSpace.basisFun ι ℝ).toMatrix_orthonormalBasis_mem_orthogonal b
  exact (Matrix.mem_orthogonalGroup_iff' (A := matrixOfRealOrthonormalBasis b)).1 hmem

@[simp] lemma matrixOfRealOrthonormalBasis_col
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (j : ι) :
    Matrix.col (matrixOfRealOrthonormalBasis b) j = ⇑(b j) := rfl

lemma matrixOfRealOrthonormalBasis_mulVec_single
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (j : ι) :
    (matrixOfRealOrthonormalBasis b) *ᵥ (Pi.single j (1 : ℝ) : ι → ℝ) = ⇑(b j) := by
  simp_rw [mulVec_single_one, matrixOfRealOrthonormalBasis_col]

lemma matrix_one_mulVec_single_real
    {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) :
    (1 : Matrix ι ι ℝ) *ᵥ (Pi.single j (1 : ℝ) : ι → ℝ) =
      (Pi.single j (1 : ℝ) : ι → ℝ) := by
  rw [one_mulVec]

lemma transpose_matrixOfRealOrthonormalBasis_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (j : ι) :
    (matrixOfRealOrthonormalBasis b)ᵀ *ᵥ ⇑(b j) =
      (Pi.single j (1 : ℝ) : ι → ℝ) := by
  calc
    (matrixOfRealOrthonormalBasis b)ᵀ *ᵥ ⇑(b j)
        = (matrixOfRealOrthonormalBasis b)ᵀ *ᵥ
            ((matrixOfRealOrthonormalBasis b) *ᵥ (Pi.single j (1 : ℝ) : ι → ℝ)) := by
      rw [matrixOfRealOrthonormalBasis_mulVec_single]
    _ = ((matrixOfRealOrthonormalBasis b)ᵀ * (matrixOfRealOrthonormalBasis b)) *ᵥ
          (Pi.single j (1 : ℝ) : ι → ℝ) := by
      rw [Matrix.mulVec_mulVec]
    _ = (Pi.single j (1 : ℝ) : ι → ℝ) := by
      rw [matrixOfRealOrthonormalBasis_orthogonal b, matrix_one_mulVec_single_real]

/-- Concrete real orthogonal factor that clears the active boundary column. -/
noncomputable def orthogonalBoundaryStepQ
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    Matrix x_sub.1.ι x_sub.1.ι ℝ := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact matrixOfRealOrthonormalBasis (realBoundaryColumnBasis x_sub.1.c)

lemma orthogonalBoundaryStepQ_orthogonal
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    IsOrthogonalMatrix (orthogonalBoundaryStepQ x_sub) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact matrixOfRealOrthonormalBasis_orthogonal (realBoundaryColumnBasis x_sub.1.c)

lemma orthogonalBoundaryStepQ_ready
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℝ) :
    HessenbergBoundaryReady
      (orthogonalHessenbergBoundarySimilarityObject
        (x_sub : HessenbergBoundaryUniverse.{u} ℝ)
        (orthogonalBoundaryStepQ x_sub)) := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  intro _hne i hi
  by_cases hc : x_sub.1.c = 0
  · simp [orthogonalHessenbergBoundarySimilarityObject, hc]
  · let b : OrthonormalBasis x_sub.1.ι ℝ (EuclideanSpace ℝ x_sub.1.ι) :=
      realBoundaryColumnBasis x_sub.1.c
    let Q : Matrix x_sub.1.ι x_sub.1.ι ℝ := matrixOfRealOrthonormalBasis b
    let v : EuclideanSpace ℝ x_sub.1.ι := realBoundaryColumnVec x_sub.1.c
    have hbhead : b (headElem (α := x_sub.1.ι)) =
        normalizedRealBoundaryColumn x_sub.1.c hc := by
      simpa [b] using realBoundaryColumnBasis_head x_sub.1.c hc
    have hneNorm : ‖v‖ ≠ 0 := by
      simpa [v] using realBoundaryColumnVec_ne_zero hc
    have hvec : v = ‖v‖ • b (headElem (α := x_sub.1.ι)) := by
      calc
        v = ‖v‖ • ((‖v‖)⁻¹ • v) := by
          rw [smul_smul, mul_inv_cancel₀ hneNorm, one_smul]
      _ = ‖v‖ • b (headElem (α := x_sub.1.ι)) := by
          rw [hbhead]
          simp [normalizedRealBoundaryColumn, v]
    have hvec_ofLp :
        v.ofLp = ‖v‖ • (b (headElem (α := x_sub.1.ι))).ofLp := by
      exact congrArg WithLp.ofLp hvec
    have hmul :
        Qᵀ *ᵥ v.ofLp =
          ‖v‖ •
            (Pi.single (headElem (α := x_sub.1.ι)) (1 : ℝ) :
              x_sub.1.ι → ℝ) := by
      calc
        Qᵀ *ᵥ v.ofLp =
            Qᵀ *ᵥ (‖v‖ • (b (headElem (α := x_sub.1.ι))).ofLp) := by
              rw [hvec_ofLp]
        _ = ‖v‖ •
            (Qᵀ *ᵥ (b (headElem (α := x_sub.1.ι))).ofLp) := by
              rw [mulVec_smul]
        _ = ‖v‖ •
            (Pi.single (headElem (α := x_sub.1.ι)) (1 : ℝ) :
              x_sub.1.ι → ℝ) := by
              simpa [Q] using
                congrArg (‖v‖ • ·)
                  (transpose_matrixOfRealOrthonormalBasis_mulVec b
                    (headElem (α := x_sub.1.ι)))
    have hentry := congrFun hmul i
    have hzero :
        (Qᵀ *ᵥ v.ofLp) i = 0 := by
      simpa [hi] using hentry
    simpa [orthogonalHessenbergBoundarySimilarityObject, orthogonalBoundaryStepQ, Q, v,
      realBoundaryColumnVec, Matrix.mulVec, Matrix.mul_apply] using hzero

/-- Concrete nonconstructive real orthogonal boundary oracle. -/
noncomputable def orthogonalHessenbergBoundaryStepOracle :
    OrthogonalHessenbergBoundaryStepOracle.{u} where
  Q := orthogonalBoundaryStepQ
  orthogonal_Q := orthogonalBoundaryStepQ_orthogonal
  ready := orthogonalBoundaryStepQ_ready

/-- Unconditional real orthogonal Hessenberg reduction. -/
theorem exists_orthogonal_hessenberg_reduction
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    HasOrthogonalHessenberg A :=
  exists_orthogonal_hessenberg_reduction_of_oracle
    orthogonalHessenbergBoundaryStepOracle A

/--
Product-representable real orthogonal Hessenberg reduction.

This theorem records a Householder-product representation of the final
orthogonal factor. The product representation is recovered from final
orthogonality; it is not an exact boundary-step trace.
-/
theorem exists_householder_product_hessenberg_reduction
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    HasHouseholderProductHessenberg A := by
  rcases exists_orthogonal_hessenberg_reduction A with ⟨Q, H, hQ, hH, hEq⟩
  exact ⟨Q, H, isHouseholderProduct_of_isOrthogonalMatrix Q hQ, hQ, hH, hEq⟩

/--
Householder Hessenberg reduction with a final-factor product trace.

The product representation is recovered from final orthogonality; this theorem
does not expose the recursive boundary-step execution trace.
-/
theorem exists_householder_hessenberg_with_product_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    HouseholderHessenbergTrace A := by
  rcases exists_householder_product_hessenberg_reduction A with
    ⟨Q, H, hQprod, hQ, hH, hEq⟩
  rcases hQprod with ⟨steps, hsteps, hprod⟩
  exact ⟨steps, Q, H, hsteps, hprod, hQ, hH, hEq⟩

/--
Compatibility name for the final-factor product trace.
Prefer `exists_householder_hessenberg_with_product_trace` in new code.
-/
theorem exists_householder_hessenberg_with_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    HouseholderHessenbergTrace A :=
  exists_householder_hessenberg_with_product_trace A

end MatDecompFormal.Instances
