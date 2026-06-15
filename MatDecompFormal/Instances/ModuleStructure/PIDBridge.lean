import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.PID
import Mathlib.Data.Fintype.EquivFin
import MatDecompFormal.Instances.ModuleStructure.Details
import MatDecompFormal.Instances.ModuleStructure.Existence

universe u v

namespace MatDecompFormal.Instances

open Matrix
open scoped DirectSum

/-!
# PID Module Structure Bridge

This file contains the honest finite-presentation/cokernel bridge layer for
abstract finitely generated modules.

The project-level invariant-factor target in `Details.lean` is stronger than
the prime-power direct-sum statement currently exposed by mathlib.  Accordingly,
this file stops at the finite-presentation quotient data and the matrix
cokernel API; it does not manufacture the final
`PIDModuleDecompositionModel` equivalence without the missing invariant-factor
quotient theorem.
-/

variable {R : Type v} {rel gen : Type*} {M : Type u}

/--
The relation map represented by a presentation matrix.

Rows index relations and columns index generators.  The map sends relation
coefficients to the corresponding linear combination of rows in the free
generator module.
-/
noncomputable def presentationRelMap
    [CommRing R] [Fintype rel] (A : Matrix rel gen R) :
    (rel → R) →ₗ[R] gen → R :=
  Aᵀ.mulVecLin

/-- The cokernel module presented by the relation matrix `A`. -/
abbrev PresentedModule
    [CommRing R] [Fintype rel] (A : Matrix rel gen R) :=
  (gen → R) ⧸ LinearMap.range (presentationRelMap A)

/--
Data proving that a presented module quotient splits coordinatewise.

For a Smith diagonal relation matrix, the relation range should be a product of
principal ideals in each generator coordinate.  This structure records that
range identification and the resulting quotient-product equivalence.
-/
structure PresentedModuleProductQuotientData
    [CommRing R] [Fintype rel] [Fintype gen] [DecidableEq gen]
    (A : Matrix rel gen R) where
  columnSubmodule : gen → Submodule R R
  range_eq_pi :
    LinearMap.range (presentationRelMap A) =
      Submodule.pi Set.univ columnSubmodule
  quotientProductEquiv :
    PresentedModule A ≃ₗ[R] ∀ j : gen, R ⧸ columnSubmodule j

/--
If the relation range of a presentation matrix is a coordinatewise product of
submodules, its cokernel is the product of the coordinate quotients.
-/
noncomputable def presentedModuleProductQuotientDataOfRangeEqPi
    [CommRing R] [Fintype rel] [Fintype gen] [DecidableEq gen]
    (A : Matrix rel gen R) (columnSubmodule : gen → Submodule R R)
    (hRange :
      LinearMap.range (presentationRelMap A) =
        Submodule.pi Set.univ columnSubmodule) :
    PresentedModuleProductQuotientData A where
  columnSubmodule := columnSubmodule
  range_eq_pi := hRange
  quotientProductEquiv :=
    (Submodule.quotEquivOfEq
      (LinearMap.range (presentationRelMap A))
      (Submodule.pi Set.univ columnSubmodule)
      hRange).trans
      (Submodule.quotientPi columnSubmodule)

/--
Accessor for the quotient-product equivalence obtained from a coordinatewise
description of the relation range.
-/
noncomputable def presentedModuleQuotientProductEquivOfRangeEqPi
    [CommRing R] [Fintype rel] [Fintype gen] [DecidableEq gen]
    (A : Matrix rel gen R) (columnSubmodule : gen → Submodule R R)
    (hRange :
      LinearMap.range (presentationRelMap A) =
        Submodule.pi Set.univ columnSubmodule) :
    PresentedModule A ≃ₗ[R] ∀ j : gen, R ⧸ columnSubmodule j :=
  (presentedModuleProductQuotientDataOfRangeEqPi A columnSubmodule hRange).quotientProductEquiv

/--
For a Smith normal-form relation matrix, every generated relation lies in the
coordinatewise product of the Smith column ideals.

This is the easy inclusion in the cokernel splitting theorem: pivot columns
land in their principal ideals `(dᵢ)`, and non-pivot columns are zero.
-/
theorem range_presentationRelMap_le_pi_columnSubmodule_of_smith
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) :
    LinearMap.range (presentationRelMap D) ≤
      Submodule.pi Set.univ
        (fun j : gen =>
          SmithNormalFormData.columnSubmodule (R := R) (rel := rel)
            (gen := gen) (D := D) data j) := by
  classical
  intro x hx
  rcases hx with ⟨c, rfl⟩
  rw [Submodule.mem_pi]
  intro j _hj
  by_cases hcol : ∃ k : data.r, data.col k = j
  · let k : data.r := Classical.choose hcol
    have hkcol : data.col k = j := Classical.choose_spec hcol
    rw [← hkcol, data.columnSubmodule_col k]
    change (presentationRelMap D c) (data.col k) ∈
      Ideal.span ({data.diag k} : Set R)
    simp [presentationRelMap, Matrix.mulVecLin]
    exact Submodule.sum_mem _ (by
      intro i _hi
      by_cases hi : i = data.row k
      · subst i
        change c (data.row k) * D (data.row k) (data.col k) ∈
          Ideal.span ({data.diag k} : Set R)
        rw [data.entry_diag k]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · have hzero : D i (data.col k) = 0 := by
          apply data.entry_zero
          intro k'
          by_cases hcol' : data.col k' = data.col k
          · have hk' : k' = k := data.col_injective hcol'
            subst k'
            exact Or.inl (by intro hrow; exact hi hrow.symm)
          · exact Or.inr hcol'
        simp [hzero])
  · have hj : ∀ k : data.r, data.col k ≠ j := by
      intro k hk
      exact hcol ⟨k, hk⟩
    rw [data.columnSubmodule_eq_bot_of_not_col hj]
    change (presentationRelMap D c) j ∈ (⊥ : Submodule R R)
    simp [presentationRelMap, Matrix.mulVecLin]
    apply Finset.sum_eq_zero
    intro i _hi
    have hzero : D i j = 0 := by
      apply data.entry_zero
      intro k
      exact Or.inr (hj k)
    simp [hzero]

/--
Conversely, every vector whose pivot coordinates lie in the corresponding
Smith principal ideals and whose non-pivot coordinates are zero is generated by
the rows of the Smith relation matrix.
-/
theorem pi_columnSubmodule_le_range_presentationRelMap_of_smith
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) :
    Submodule.pi Set.univ (fun j : gen => data.columnSubmodule j) ≤
      LinearMap.range (presentationRelMap D) := by
  classical
  intro x hx
  rw [Submodule.mem_pi] at hx
  have hx_pivot :
      ∀ k : data.r, x (data.col k) ∈ Ideal.span ({data.diag k} : Set R) := by
    intro k
    simpa [data.columnSubmodule_col k] using hx (data.col k) (Set.mem_univ _)
  let coeff : data.r → R := fun k =>
    Classical.choose (Ideal.mem_span_singleton'.mp (hx_pivot k))
  have coeff_spec : ∀ k : data.r, coeff k * data.diag k = x (data.col k) := by
    intro k
    exact Classical.choose_spec (Ideal.mem_span_singleton'.mp (hx_pivot k))
  let c : rel → R := fun i =>
    if h : ∃ k : data.r, data.row k = i then coeff (Classical.choose h) else 0
  refine ⟨c, ?_⟩
  ext j
  by_cases hcol : ∃ k : data.r, data.col k = j
  · let k : data.r := Classical.choose hcol
    have hkcol : data.col k = j := Classical.choose_spec hcol
    rw [← hkcol]
    change (presentationRelMap D c) (data.col k) = x (data.col k)
    simp [presentationRelMap, Matrix.mulVecLin, Matrix.vecMul_eq_sum, Pi.smul_apply]
    rw [Finset.sum_eq_single (data.row k)]
    · have hrowExists : ∃ k' : data.r, data.row k' = data.row k := ⟨k, rfl⟩
      have hchoose : Classical.choose hrowExists = k :=
        data.row_injective (Classical.choose_spec hrowExists)
      simp [c, hrowExists, hchoose, data.entry_diag k, coeff_spec]
    · intro i _hi hi_ne
      by_cases hrow : ∃ k' : data.r, data.row k' = i
      · have hzero : D i (data.col k) = 0 := by
          apply data.entry_zero
          intro t
          by_cases htcol : data.col t = data.col k
          · have ht : t = k := data.col_injective htcol
            subst t
            exact Or.inl (by
              intro hrowtk
              exact hi_ne hrowtk.symm)
          · exact Or.inr htcol
        simp [c, hrow, hzero]
      · simp [c, hrow]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · have hjnot : ∀ k : data.r, data.col k ≠ j := by
      intro k hk
      exact hcol ⟨k, hk⟩
    have hxj_zero : x j = 0 := by
      have hxj := hx j (Set.mem_univ _)
      rw [data.columnSubmodule_eq_bot_of_not_col hjnot] at hxj
      simpa using hxj
    change (presentationRelMap D c) j = x j
    simp [presentationRelMap, Matrix.mulVecLin, Matrix.vecMul_eq_sum, Pi.smul_apply, hxj_zero]
    apply Finset.sum_eq_zero
    intro i _hi
    have hzero : D i j = 0 := by
      apply data.entry_zero
      intro k
      exact Or.inr (hjnot k)
    simp [hzero]

/-- Smith relation ranges are exactly the coordinatewise product of Smith column ideals. -/
theorem range_presentationRelMap_eq_pi_columnSubmodule_of_smith
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) :
    LinearMap.range (presentationRelMap D) =
      Submodule.pi Set.univ (fun j : gen => data.columnSubmodule j) :=
  le_antisymm
    (range_presentationRelMap_le_pi_columnSubmodule_of_smith data)
    (pi_columnSubmodule_le_range_presentationRelMap_of_smith data)

/--
Product quotient data for the cokernel of a Smith normal-form relation matrix.
-/
noncomputable def presentedModuleProductQuotientDataOfSmith
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) :
    PresentedModuleProductQuotientData D :=
  presentedModuleProductQuotientDataOfRangeEqPi D
    (fun j : gen => data.columnSubmodule j)
    (range_presentationRelMap_eq_pi_columnSubmodule_of_smith data)

/--
The cokernel of a Smith normal-form relation matrix is the product of its
coordinate cyclic quotients.
-/
noncomputable def presentedModuleQuotientProductEquivOfSmith
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) :
    PresentedModule D ≃ₗ[R] ∀ j : gen, R ⧸ data.columnSubmodule j :=
  (presentedModuleProductQuotientDataOfSmith data).quotientProductEquiv

namespace SmithNormalFormData

/--
Order generator coordinates by Smith pivot columns first, followed by all
non-pivot columns.

This order is the quotient-side companion of
`PIDInvariantFactorData.ofSmithNormalFormDataWithZeroTail`: the first block is
the ordered Smith diagonal, and the complement block contributes zero cyclic
factors `R/(0)`.
-/
noncomputable def generatorOrderEquiv
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) :
    Fin (Fintype.card data.r + Fintype.card ((Set.range data.col)ᶜ : Set gen)) ≃ gen := by
  classical
  exact
    finSumFinEquiv.symm.trans
      ((Equiv.sumCongr data.order
        (Fintype.equivFin ((Set.range data.col)ᶜ : Set gen)).symm).trans
        ((Equiv.sumCongr (Equiv.ofInjective data.col data.col_injective)
          (Equiv.refl ((Set.range data.col)ᶜ : Set gen))).trans
          (Equiv.Set.sumCompl (Set.range data.col))))

@[simp] theorem generatorOrderEquiv_castAdd
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D)
    (i : Fin (Fintype.card data.r)) :
    data.generatorOrderEquiv
        (Fin.castAdd (Fintype.card ((Set.range data.col)ᶜ : Set gen)) i) =
      data.col (data.order i) := by
  simp [generatorOrderEquiv]

@[simp] theorem generatorOrderEquiv_natAdd_eq
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D)
    (i : Fin (Fintype.card ((Set.range data.col)ᶜ : Set gen))) :
    data.generatorOrderEquiv (Fin.natAdd (Fintype.card data.r) i) =
      ((Fintype.equivFin ((Set.range data.col)ᶜ : Set gen)).symm i :
        ((Set.range data.col)ᶜ : Set gen)) := by
  simp [generatorOrderEquiv]

theorem generatorOrderEquiv_natAdd_not_col
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D)
    (i : Fin (Fintype.card ((Set.range data.col)ᶜ : Set gen))) :
    ∀ k : data.r,
      data.col k ≠ data.generatorOrderEquiv (Fin.natAdd (Fintype.card data.r) i) := by
  intro k hk
  have hnot :
      (((Fintype.equivFin ((Set.range data.col)ᶜ : Set gen)).symm i :
          ((Set.range data.col)ᶜ : Set gen)) : gen) ∉ Set.range data.col :=
    ((Fintype.equivFin ((Set.range data.col)ᶜ : Set gen)).symm i).property
  have hout := data.generatorOrderEquiv_natAdd_eq i
  rw [hout] at hk
  exact hnot ⟨k, hk⟩

/--
The Smith column submodule at the ordered generator coordinate is exactly the
principal ideal generated by the corresponding invariant factor, including the
zero tail for non-pivot columns.
-/
theorem columnSubmodule_generatorOrderEquiv
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D)
    (i : Fin (Fintype.card data.r + Fintype.card ((Set.range data.col)ᶜ : Set gen))) :
    data.columnSubmodule (data.generatorOrderEquiv i) =
      (Ideal.span ({(PIDInvariantFactorData.ofSmithNormalFormDataWithZeroTail data
        (Fintype.card ((Set.range data.col)ᶜ : Set gen))).invariantFactor i} : Set R) :
        Submodule R R) := by
  classical
  refine Fin.addCases ?left ?right i
  · intro i
    simp [PIDInvariantFactorData.ofSmithNormalFormDataWithZeroTail]
  · intro i
    rw [data.columnSubmodule_eq_bot_of_not_col
      (data.generatorOrderEquiv_natAdd_not_col i)]
    simp [PIDInvariantFactorData.ofSmithNormalFormDataWithZeroTail]

/--
Coordinate quotient products indexed by generator columns can be reordered into
the invariant-factor data with a zero tail for non-pivot columns.
-/
noncomputable def quotientProductEquivTorsionDataWithGeneratorZeroTail
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) :
    (∀ j : gen, R ⧸ data.columnSubmodule j) ≃ₗ[R]
      PIDModuleTorsionPart R
        (PIDInvariantFactorData.ofSmithNormalFormDataWithZeroTail data
          (Fintype.card ((Set.range data.col)ᶜ : Set gen))) := by
  classical
  let idx := Fin (Fintype.card data.r + Fintype.card ((Set.range data.col)ᶜ : Set gen))
  let torsionData := PIDInvariantFactorData.ofSmithNormalFormDataWithZeroTail data
    (Fintype.card ((Set.range data.col)ᶜ : Set gen))
  let e := data.generatorOrderEquiv
  let p : gen → Submodule R R := fun j => data.columnSubmodule j
  let q : idx → Submodule R R := fun i =>
    (Ideal.span ({torsionData.invariantFactor i} : Set R) : Submodule R R)
  have h : ∀ i : idx, p (e i) = q i := by
    intro i
    exact data.columnSubmodule_generatorOrderEquiv i
  let e₁ : ((j : gen) → R ⧸ p j) ≃ₗ[R] ((i : idx) → R ⧸ p (e i)) :=
    (LinearEquiv.piCongrLeft (R := R) (φ := fun j : gen => R ⧸ p j) e).symm
  let e₂ : ((i : idx) → R ⧸ p (e i)) ≃ₗ[R] ((i : idx) → R ⧸ q i) :=
    LinearEquiv.piCongrRight (R := R) (ι := idx)
      (φ := fun i : idx => R ⧸ p (e i))
      (ψ := fun i : idx => R ⧸ q i)
      (fun i => Submodule.quotEquivOfEq (p (e i)) (q i) (h i))
  exact e₁.trans e₂

end SmithNormalFormData

/--
Adding a rank-zero free part is linearly equivalent to leaving only the torsion
product.
-/
noncomputable def torsionPartEquivZeroFreeDecompositionModel
    [CommRing R] (torsionData : PIDInvariantFactorData.{u, v} R) :
    PIDModuleTorsionPart R torsionData ≃ₗ[R]
      PIDModuleDecompositionModel R 0 torsionData where
  toFun t := (0, t)
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      exact Fin.elim0 i
    · rfl
  map_add' _ _ := by
    apply Prod.ext <;> simp
  map_smul' _ _ := by
    apply Prod.ext <;> simp

namespace PIDInvariantFactorData

/--
Lift small-universe invariant-factor data into an arbitrary universe without
changing the invariant factors.
-/
noncomputable def uliftSmall
    {R : Type v} [Semiring R] (torsionData : PIDInvariantFactorData.{0, v} R) :
    PIDInvariantFactorData.{u, v} R where
  ι := ULift.{u, 0} torsionData.ι
  fintype_ι := inferInstance
  order :=
    (finCongr
      (Fintype.card_congr
        (Equiv.ulift : ULift.{u, 0} torsionData.ι ≃ torsionData.ι))).trans
      (torsionData.order.trans
        (Equiv.ulift : ULift.{u, 0} torsionData.ι ≃ torsionData.ι).symm)
  invariantFactor := fun i => torsionData.invariantFactor i.down
  divisibility_chain := by
    intro k hnext
    have hnext' : ((finCongr
        (Fintype.card_congr
          (Equiv.ulift : ULift.{u, 0} torsionData.ι ≃ torsionData.ι)) k :
        Fin (Fintype.card torsionData.ι)) : Nat) + 1 <
        Fintype.card torsionData.ι := by
      simpa using hnext
    simpa [finCongr] using
      torsionData.divisibility_chain
        (finCongr
          (Fintype.card_congr
            (Equiv.ulift : ULift.{u, 0} torsionData.ι ≃ torsionData.ι)) k)
        hnext'

/-- Reindex the torsion product along `uliftSmall`. -/
noncomputable def torsionPartEquivULiftSmall
    {R : Type v} [CommRing R] (torsionData : PIDInvariantFactorData.{0, v} R) :
    PIDModuleTorsionPart R torsionData ≃ₗ[R]
      PIDModuleTorsionPart R (uliftSmall.{u, v} torsionData) :=
  (LinearEquiv.piCongrLeft (R := R)
    (φ := fun i : torsionData.ι =>
      PIDCyclicSummand R (torsionData.invariantFactor i))
    (Equiv.ulift : ULift.{u, 0} torsionData.ι ≃ torsionData.ι)).symm

end PIDInvariantFactorData

/--
Transport quotient modules along a linear equivalence whose map carries one
quotiented submodule onto the other.
-/
noncomputable def quotientLinearEquivOfEqMap
    {V W : Type u} [Ring R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (e : V ≃ₗ[R] W) (p : Submodule R V) (q : Submodule R W)
    (hmap : Submodule.map e.toLinearMap p = q) :
    (V ⧸ p) ≃ₗ[R] (W ⧸ q) where
  toLinearMap :=
    p.mapQ q e.toLinearMap (by
      intro x hx
      change e x ∈ q
      rw [← hmap]
      exact ⟨x, hx, rfl⟩)
  invFun y :=
    q.mapQ p e.symm.toLinearMap (by
      intro y hy
      change e.symm y ∈ p
      have hy' : y ∈ Submodule.map e.toLinearMap p := by
        simpa [hmap] using hy
      rcases hy' with ⟨x, hx, hxy⟩
      have : e.symm y = x := by
        rw [← hxy]
        simp
      simpa [this] using hx) y
  left_inv x := by
    refine Quotient.inductionOn' x ?_
    intro x
    change (q.mapQ p e.symm.toLinearMap _)
        ((p.mapQ q e.toLinearMap _) (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk x
    rw [Submodule.mapQ_apply]
    rw [Submodule.mapQ_apply]
    simp
  right_inv y := by
    refine Quotient.inductionOn' y ?_
    intro y
    change (p.mapQ q e.toLinearMap _)
        ((q.mapQ p e.symm.toLinearMap _) (Submodule.Quotient.mk y)) =
      Submodule.Quotient.mk y
    rw [Submodule.mapQ_apply]
    rw [Submodule.mapQ_apply]
    simp

/--
The transpose action of an explicitly invertible square matrix on coordinate
vectors, packaged as a linear equivalence.
-/
noncomputable def transposeMulVecLinearEquiv
    {idx : Type u} [CommRing R] [Fintype idx] [DecidableEq idx]
    (Q : Matrix idx idx R) (hQ : GaussInvertibleMatrix Q) :
    (idx → R) ≃ₗ[R] idx → R := by
  classical
  let Qinv : Matrix idx idx R := Classical.choose hQ
  have hleft : Qinv * Q = 1 := (Classical.choose_spec hQ).1
  have hright : Q * Qinv = 1 := (Classical.choose_spec hQ).2
  refine
    { toLinearMap := Qᵀ.mulVecLin
      invFun := fun x => Qinvᵀ.mulVec x
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change Qinvᵀ.mulVec (Qᵀ.mulVec x) = x
    rw [Matrix.mulVec_mulVec]
    rw [← Matrix.transpose_mul, hright]
    simp
  · intro x
    change Qᵀ.mulVec (Qinvᵀ.mulVec x) = x
    rw [Matrix.mulVec_mulVec]
    rw [← Matrix.transpose_mul, hleft]
    simp

theorem presentationRelMap_mul_right_apply
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [Fintype gen] [DecidableEq gen]
    (A : Matrix rel gen R) (Q : Matrix gen gen R)
    (hQ : GaussInvertibleMatrix Q) (c : rel → R) :
    transposeMulVecLinearEquiv Q hQ (presentationRelMap A c) =
      presentationRelMap (A * Q) c := by
  ext j
  simp [transposeMulVecLinearEquiv, presentationRelMap, Matrix.transpose_mul]

/--
Right multiplication of a presentation matrix by an invertible generator
change-of-basis transports the relation submodule by the induced coordinate
linear equivalence.
-/
theorem range_presentationRelMap_mul_right
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [Fintype gen] [DecidableEq gen]
    (A : Matrix rel gen R) (Q : Matrix gen gen R)
    (hQ : GaussInvertibleMatrix Q) :
    Submodule.map (transposeMulVecLinearEquiv Q hQ).toLinearMap
        (LinearMap.range (presentationRelMap A)) =
      LinearMap.range (presentationRelMap (A * Q)) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨c, rfl⟩
    exact ⟨c, (presentationRelMap_mul_right_apply A Q hQ c).symm⟩
  · intro y hy
    rcases hy with ⟨c, rfl⟩
    refine ⟨presentationRelMap A c, ⟨c, rfl⟩, ?_⟩
    exact presentationRelMap_mul_right_apply A Q hQ c

theorem presentationRelMap_mul_left_apply
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel]
    (P : Matrix rel rel R) (A : Matrix rel gen R)
    (hP : GaussInvertibleMatrix P) (c : rel → R) :
    presentationRelMap (P * A) c =
      presentationRelMap A (transposeMulVecLinearEquiv P hP c) := by
  ext j
  simp [transposeMulVecLinearEquiv, presentationRelMap, Matrix.transpose_mul]

/--
Left multiplication of a presentation matrix by an invertible relation
change-of-basis preserves the generated relation submodule.
-/
theorem range_presentationRelMap_mul_left
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel]
    (P : Matrix rel rel R) (A : Matrix rel gen R)
    (hP : GaussInvertibleMatrix P) :
    LinearMap.range (presentationRelMap (P * A)) =
      LinearMap.range (presentationRelMap A) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨c, rfl⟩
    exact ⟨transposeMulVecLinearEquiv P hP c,
      (presentationRelMap_mul_left_apply P A hP c).symm⟩
  · intro y hy
    rcases hy with ⟨c, rfl⟩
    refine ⟨(transposeMulVecLinearEquiv P hP).symm c, ?_⟩
    rw [presentationRelMap_mul_left_apply P A hP]
    simp

/--
Two-sided presentation equivalence: row operations preserve the relation range,
while column operations transport it by the induced generator equivalence.
-/
theorem range_presentationRelMap_twoSided
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    (P : Matrix rel rel R) (Q : Matrix gen gen R) (A : Matrix rel gen R)
    (hP : GaussInvertibleMatrix P) (hQ : GaussInvertibleMatrix Q) :
    Submodule.map (transposeMulVecLinearEquiv Q hQ).toLinearMap
        (LinearMap.range (presentationRelMap A)) =
      LinearMap.range (presentationRelMap (P * A * Q)) := by
  rw [← range_presentationRelMap_mul_right (P * A) Q hQ]
  rw [range_presentationRelMap_mul_left P A hP]

/--
The cokernel presented by `A` is linearly equivalent to the cokernel presented
by any two-sided invertible row/column transform of `A`.
-/
noncomputable def presentedModuleEquivOfTwoSided
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    (P : Matrix rel rel R) (Q : Matrix gen gen R)
    (A D : Matrix rel gen R)
    (hP : GaussInvertibleMatrix P) (hQ : GaussInvertibleMatrix Q)
    (hD : D = P * A * Q) :
    PresentedModule A ≃ₗ[R] PresentedModule D :=
  quotientLinearEquivOfEqMap
    (transposeMulVecLinearEquiv Q hQ)
    (LinearMap.range (presentationRelMap A))
    (LinearMap.range (presentationRelMap D))
    (by
      rw [hD]
      exact range_presentationRelMap_twoSided P Q A hP hQ)

/--
Presentation-level PID structure data gives a concrete cokernel decomposition
of the presented module into coordinate cyclic quotients of the Smith matrix.
-/
noncomputable def presentedModuleQuotientProductEquivOfStructureData
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {A : Matrix rel gen R} (data : PIDModuleStructureData A) :
    PresentedModule A ≃ₗ[R]
      ∀ j : gen,
        R ⧸
          (SmithNormalFormData.columnSubmodule (R := R) (rel := rel)
            (gen := gen) (D := data.D) (Classical.choice data.smith_D) j) :=
  (presentedModuleEquivOfTwoSided data.P data.Q A data.D
    data.invertible_P data.invertible_Q data.equation).trans
    (presentedModuleQuotientProductEquivOfSmith (Classical.choice data.smith_D))

/--
Invariant-factor data for a presentation matrix, using the Smith pivot columns
followed by a zero factor for each non-pivot generator column.
-/
noncomputable def PIDModuleStructureData.torsionDataWithColumnComplementZeroTail
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {A : Matrix rel gen R} (data : PIDModuleStructureData A) :
    PIDInvariantFactorData R :=
  let smithData := Classical.choice data.smith_D
  PIDInvariantFactorData.ofSmithNormalFormDataWithZeroTail smithData
    (Fintype.card ((Set.range smithData.col)ᶜ : Set gen))

/--
Presentation-level PID structure data gives a full project-level decomposition
model for the cokernel of the presentation.

The free coordinates of a rectangular Smith cokernel are represented as zero
cyclic factors `R/(0)`, so the explicit free rank is `0`.
-/
noncomputable def presentedModuleEquivDecompositionModelOfStructureData
    {rel gen : Type u}
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {A : Matrix rel gen R} (data : PIDModuleStructureData A) :
    PresentedModule A ≃ₗ[R]
      PIDModuleDecompositionModel R 0
        data.torsionDataWithColumnComplementZeroTail := by
  classical
  let smithData := Classical.choice data.smith_D
  let torsionData := data.torsionDataWithColumnComplementZeroTail
  let e₁ := presentedModuleQuotientProductEquivOfStructureData data
  let e₂ := smithData.quotientProductEquivTorsionDataWithGeneratorZeroTail
  let e₃ := torsionPartEquivZeroFreeDecompositionModel torsionData
  exact e₁.trans (e₂.trans e₃)

/--
Matrix-level finite presentation data for an abstract module.

This is the planned `PresentedModule A` bridge surface: an abstract module is
identified with the cokernel of an explicit finite relation matrix.
-/
structure FinitePresentationMatrixData
    (R : Type v) (M : Type u) [CommRing R] [AddCommGroup M] [Module R M] where
  relRank : Nat
  genRank : Nat
  relationMatrix : Matrix (Fin relRank) (Fin genRank) R
  quotientEquiv :
    M ≃ₗ[R] (Fin genRank → R) ⧸
      LinearMap.range
        (presentationRelMap (R := R) (rel := Fin relRank)
          (gen := Fin genRank) relationMatrix)

namespace FinitePresentationMatrixData

variable [CommRing R] [AddCommGroup M] [Module R M]

/--
The same finite presentation matrix with row and column indices lifted into
the universe of `R`.

The public PID Smith theorem currently works with matrix index types in the
same universe as the coefficient ring.  This lifted view preserves the finite
presentation matrix while exposing it to that theorem.
-/
noncomputable def relationMatrixULift
    (data : FinitePresentationMatrixData R M) :
    Matrix (ULift.{v, 0} (Fin data.relRank))
      (ULift.{v, 0} (Fin data.genRank)) R :=
  Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm data.relationMatrix

/--
PID presentation structure for the lifted finite presentation matrix.

This is still presentation-level data; it deliberately does not claim the
abstract quotient has already been converted to ordered invariant factors.
-/
theorem relationMatrixULift_hasPresentedPIDModuleStructure
    [IsDomain R] [IsPrincipalIdealRing R]
    (data : FinitePresentationMatrixData R M) :
    HasPresentedPIDModuleStructure data.relationMatrixULift := by
  classical
  exact exists_presented_pid_module_structure data.relationMatrixULift

/--
The original relation map and the lifted relation map commute with the
coordinate reindexing equivalences.
-/
theorem relationMatrixULift_presentationRelMap
    (data : FinitePresentationMatrixData R M) (c : Fin data.relRank → R) :
    (LinearEquiv.funCongrLeft R R
      (Equiv.ulift : ULift.{v, 0} (Fin data.genRank) ≃ Fin data.genRank))
      (presentationRelMap data.relationMatrix c) =
    presentationRelMap data.relationMatrixULift
      ((LinearEquiv.funCongrLeft R R
        (Equiv.ulift : ULift.{v, 0} (Fin data.relRank) ≃ Fin data.relRank)) c) := by
  ext j
  simp [presentationRelMap, relationMatrixULift, Matrix.mulVecLin, Matrix.mulVec,
    Matrix.transpose_apply, Matrix.reindex_apply]
  change (∑ i : Fin data.relRank, c i * data.relationMatrix i j.down) =
    ∑ x : ULift.{v, 0} (Fin data.relRank),
      data.relationMatrix x.down j.down * c x.down
  exact Fintype.sum_equiv
    (Equiv.ulift.symm : Fin data.relRank ≃ ULift.{v, 0} (Fin data.relRank))
    (fun i : Fin data.relRank => c i * data.relationMatrix i j.down)
    (fun x : ULift.{v, 0} (Fin data.relRank) =>
      data.relationMatrix x.down j.down * c x.down)
    (by intro x; simp [mul_comm])

/--
The lifted generator-coordinate equivalence carries the original relation
submodule onto the relation submodule of the lifted matrix.
-/
theorem relationMatrixULift_range_eq_map
    (data : FinitePresentationMatrixData R M) :
    Submodule.map
      (LinearEquiv.funCongrLeft R R
        (Equiv.ulift : ULift.{v, 0} (Fin data.genRank) ≃ Fin data.genRank)).toLinearMap
      (LinearMap.range (presentationRelMap data.relationMatrix)) =
    LinearMap.range (presentationRelMap data.relationMatrixULift) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨c, rfl⟩
    exact ⟨_, (data.relationMatrixULift_presentationRelMap c).symm⟩
  · intro y hy
    rcases hy with ⟨cLift, rfl⟩
    let eRel := LinearEquiv.funCongrLeft R R
      (Equiv.ulift : ULift.{v, 0} (Fin data.relRank) ≃ Fin data.relRank)
    let c : Fin data.relRank → R := eRel.symm cLift
    refine ⟨presentationRelMap data.relationMatrix c, ⟨c, rfl⟩, ?_⟩
    change (LinearEquiv.funCongrLeft R R
      (Equiv.ulift : ULift.{v, 0} (Fin data.genRank) ≃ Fin data.genRank))
      (presentationRelMap data.relationMatrix c) =
      presentationRelMap data.relationMatrixULift cLift
    have h := data.relationMatrixULift_presentationRelMap c
    simpa [eRel, c] using h

/--
The abstract module is equivalent to the cokernel of the lifted relation
matrix, whose indices live in the coefficient-ring universe.
-/
noncomputable def quotientEquivULift
    (data : FinitePresentationMatrixData R M) :
    M ≃ₗ[R]
      (ULift.{v, 0} (Fin data.genRank) → R) ⧸
        LinearMap.range (presentationRelMap data.relationMatrixULift) :=
  data.quotientEquiv.trans
    (quotientLinearEquivOfEqMap
      (LinearEquiv.funCongrLeft R R
        (Equiv.ulift : ULift.{v, 0} (Fin data.genRank) ≃ Fin data.genRank))
      (LinearMap.range (presentationRelMap data.relationMatrix))
      (LinearMap.range (presentationRelMap data.relationMatrixULift))
      data.relationMatrixULift_range_eq_map)

end FinitePresentationMatrixData

/--
Quotient form supplied directly by `Module.FinitePresentation.exists_fin`.

The relation submodule is finitely generated, but no basis/order for its
chosen generators has yet been converted into an explicit relation matrix.
-/
structure FinitePresentationQuotientData
    (R : Type v) (M : Type u) [CommRing R] [AddCommGroup M] [Module R M] where
  genRank : Nat
  relations : Submodule R (Fin genRank → R)
  quotientEquiv : M ≃ₗ[R] (Fin genRank → R) ⧸ relations
  relations_fg : relations.FG

namespace FinitePresentationQuotientData

variable [CommRing R] [AddCommGroup M] [Module R M]

/--
Finite relation index type selected from the generators of the relation
submodule.
-/
abbrev RelationIndex (data : FinitePresentationQuotientData R M) :=
  data.relations.generators

/--
Relation matrix whose rows are the selected finite generators of the relation
submodule.
-/
noncomputable def relationMatrix
    (data : FinitePresentationQuotientData R M) :
    Matrix data.RelationIndex (Fin data.genRank) R :=
  fun r j => (r : Fin data.genRank → R) j

theorem range_presentationRelMap_relationMatrix
    (data : FinitePresentationQuotientData R M) :
    letI : Fintype data.RelationIndex :=
      Set.Finite.fintype data.relations_fg.finite_generators
    LinearMap.range (presentationRelMap (data.relationMatrix)) =
      data.relations := by
  classical
  letI : Fintype data.RelationIndex :=
    Set.Finite.fintype data.relations_fg.finite_generators
  calc
    LinearMap.range (presentationRelMap (data.relationMatrix)) =
        Submodule.span R (Set.range data.relationMatrix.row) := by
          simpa [presentationRelMap] using
            (range_vecMulLinear data.relationMatrix)
    _ = Submodule.span R (Set.range ((↑) :
          data.RelationIndex → (Fin data.genRank → R))) := by
          rfl
    _ = Submodule.span R data.relations.generators := by
          congr 1
          ext x
          simp
    _ = data.relations :=
          Submodule.span_generators data.relations

/-- Finset form of the selected relation generators. -/
noncomputable def relationFinset
    (data : FinitePresentationQuotientData R M) :
    Finset (Fin data.genRank → R) :=
  data.relations_fg.finite_generators.toFinset

/-- Relation matrix indexed by `Fin relRank`, suitable for Smith-normal-form APIs. -/
noncomputable def relationFinMatrix
    (data : FinitePresentationQuotientData R M) :
    Matrix (Fin data.relationFinset.card) (Fin data.genRank) R :=
  fun i j => ((data.relationFinset.equivFin.symm i :
    data.relationFinset) : Fin data.genRank → R) j

theorem range_presentationRelMap_relationFinMatrix
    (data : FinitePresentationQuotientData R M) :
    LinearMap.range (presentationRelMap (data.relationFinMatrix)) =
      data.relations := by
  classical
  calc
    LinearMap.range (presentationRelMap (data.relationFinMatrix)) =
        Submodule.span R (Set.range data.relationFinMatrix.row) := by
          simpa [presentationRelMap] using
            (range_vecMulLinear data.relationFinMatrix)
    _ = Submodule.span R (data.relationFinset : Set (Fin data.genRank → R)) := by
          congr 1
          ext x
          constructor
          · rintro ⟨i, rfl⟩
            exact (data.relationFinset.equivFin.symm i).2
          · intro hx
            refine ⟨data.relationFinset.equivFin ⟨x, hx⟩, ?_⟩
            ext j
            simp [relationFinMatrix]
    _ = Submodule.span R data.relations.generators := by
          congr 1
          ext x
          simp [relationFinset]
    _ = data.relations :=
          Submodule.span_generators data.relations

/--
Convert quotient-presentation data into an explicit relation matrix whose
cokernel is linearly equivalent to the original module.
-/
noncomputable def toMatrixData
    (data : FinitePresentationQuotientData R M) :
    FinitePresentationMatrixData R M := by
  classical
  letI : Fintype data.RelationIndex :=
    Set.Finite.fintype data.relations_fg.finite_generators
  exact
    { relRank := data.relationFinset.card
      genRank := data.genRank
      relationMatrix := data.relationFinMatrix
      quotientEquiv :=
        data.quotientEquiv.trans
          (Submodule.quotEquivOfEq data.relations
            (LinearMap.range (presentationRelMap data.relationFinMatrix))
            (data.range_presentationRelMap_relationFinMatrix).symm) }

end FinitePresentationQuotientData

/--
Every finitely generated module over a Noetherian commutative ring has the
finite quotient-presentation data used by the PID bridge.
-/
noncomputable def finitePresentationQuotientDataOfFinite
    (R : Type v) (M : Type u) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    FinitePresentationQuotientData R M := by
  letI : Module.FinitePresentation R M :=
    Module.finitePresentation_of_finite R M
  let h := Module.FinitePresentation.exists_fin R M
  let n : Nat := Classical.choose h
  let hn := Classical.choose_spec h
  let K : Submodule R (Fin n → R) := Classical.choose hn
  let hK := Classical.choose_spec hn
  let e : M ≃ₗ[R] (Fin n → R) ⧸ K := Classical.choose hK
  let hfg : K.FG := Classical.choose_spec hK
  exact
    { genRank := n
      relations := K
      quotientEquiv := e
      relations_fg := hfg }

theorem exists_finitePresentationQuotientData_of_finite
    (R : Type v) (M : Type u) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Nonempty (FinitePresentationQuotientData R M) :=
  ⟨finitePresentationQuotientDataOfFinite R M⟩

/--
Every finitely generated module over a Noetherian commutative ring has an
explicit finite presentation matrix.
-/
noncomputable def finitePresentationMatrixDataOfFinite
    (R : Type v) (M : Type u) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    FinitePresentationMatrixData R M :=
  (finitePresentationQuotientDataOfFinite R M).toMatrixData

theorem exists_finitePresentationMatrixData_of_finite
    (R : Type v) (M : Type u) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Nonempty (FinitePresentationMatrixData R M) :=
  ⟨finitePresentationMatrixDataOfFinite R M⟩

/--
PID specialization of the quotient-presentation bridge.

`IsPrincipalIdealRing` supplies the Noetherian hypothesis needed to turn
finite generation into finite presentation.
-/
noncomputable def finitePresentationQuotientDataOfPIDModule
    (R : Type v) (M : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    FinitePresentationQuotientData R M :=
  finitePresentationQuotientDataOfFinite R M

theorem exists_finitePresentationQuotientData_pid
    (R : Type v) (M : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Nonempty (FinitePresentationQuotientData R M) :=
  ⟨finitePresentationQuotientDataOfPIDModule R M⟩

/-- PID specialization of the explicit finite presentation matrix bridge. -/
noncomputable def finitePresentationMatrixDataOfPIDModule
    (R : Type v) (M : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    FinitePresentationMatrixData R M :=
  (finitePresentationQuotientDataOfPIDModule R M).toMatrixData

theorem exists_finitePresentationMatrixData_pid
    (R : Type v) (M : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Nonempty (FinitePresentationMatrixData R M) :=
  ⟨finitePresentationMatrixDataOfPIDModule R M⟩

/--
PID finite-presentation matrix data together with the presentation-level PID
structure of its universe-lifted relation matrix.
-/
theorem exists_finitePresentationMatrixData_pid_with_presented_structure
    (R : Type v) (M : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ data : FinitePresentationMatrixData R M,
      HasPresentedPIDModuleStructure data.relationMatrixULift := by
  classical
  let data := finitePresentationMatrixDataOfPIDModule R M
  exact ⟨data, data.relationMatrixULift_hasPresentedPIDModuleStructure⟩

/--
Unconditional finitely generated PID module decomposition in the project's
invariant-factor model.

The construction goes through a finite presentation matrix, Smith normal form
of its relation matrix, and the quotient equivalences above. Rectangular free
coordinates are encoded as zero cyclic factors `R/(0)`, so this witness uses
`freeRank = 0`.
-/
theorem exists_pid_module_structure
    (R : Type u) (M : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ freeRank torsionData,
      PIDModuleDecomposition R M freeRank torsionData := by
  classical
  let data := finitePresentationMatrixDataOfPIDModule R M
  rcases data.relationMatrixULift_hasPresentedPIDModuleStructure with
    ⟨structureData⟩
  let torsionData0 := structureData.torsionDataWithColumnComplementZeroTail
  let torsionData := PIDInvariantFactorData.uliftSmall.{u, u} torsionData0
  let ePresented :=
    presentedModuleEquivDecompositionModelOfStructureData structureData
  let eLift :
      PIDModuleDecompositionModel R 0 torsionData0 ≃ₗ[R]
        PIDModuleDecompositionModel R 0 torsionData :=
    LinearEquiv.prodCongr (LinearEquiv.refl R _)
      (PIDInvariantFactorData.torsionPartEquivULiftSmall.{u, u} torsionData0)
  let e : M ≃ₗ[R] PIDModuleDecompositionModel R 0 torsionData :=
    data.quotientEquivULift.trans (ePresented.trans eLift)
  exact ⟨0, torsionData, ⟨{ decompositionIso := e }⟩⟩

/-!
## Prime-power module decomposition bridge

Mathlib currently exposes the finitely generated PID module structure theorem
in elementary-divisor form: a free finitely supported part plus a finite direct
sum of prime-power cyclic quotients.  The project-level
`PIDModuleDecompositionModel` is stronger because it asks for invariant factors
ordered by divisibility.  The following data records the unconditional theorem
that is available today, without pretending that the prime-power summands have
already been merged into invariant factors.
-/

/--
Prime-power form of the finitely generated PID module decomposition supplied by
mathlib.

This is an honest unconditional decomposition target.  A separate CRT/invariant
factor merge theorem is still needed to convert this data into
`PIDModuleDecompositionData`.
-/
structure PIDPrimePowerModuleDecompositionData
    (R : Type v) (M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M] where
  freeRank : Nat
  ι : Type v
  fintype_ι : Fintype ι
  prime : ι → R
  irreducible_prime : ∀ i, Irreducible (prime i)
  exponent : ι → Nat
  decompositionIso :
    M ≃ₗ[R] (Fin freeRank →₀ R) ×
      ⨁ i : ι, R ⧸ R ∙ prime i ^ exponent i

attribute [instance] PIDPrimePowerModuleDecompositionData.fintype_ι

/--
Construct the prime-power decomposition data for a finitely generated module
over a PID from mathlib's structure theorem.
-/
noncomputable def pidPrimePowerModuleDecompositionDataOfFinite
    (R : Type v) (M : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    PIDPrimePowerModuleDecompositionData R M := by
  classical
  let h := Module.equiv_free_prod_directSum (R := R) (M := M)
  let freeRank := Classical.choose h
  let hfree := Classical.choose_spec h
  let ι := Classical.choose hfree
  let hι := Classical.choose_spec hfree
  let fintype_ι := Classical.choose hι
  let hfintype := Classical.choose_spec hι
  let prime := Classical.choose hfintype
  let hprime := Classical.choose_spec hfintype
  let hirr := Classical.choose hprime
  let hhirr := Classical.choose_spec hprime
  let exponent := Classical.choose hhirr
  let hIso := Classical.choose_spec hhirr
  exact
    { freeRank := freeRank
      ι := ι
      fintype_ι := fintype_ι
      prime := prime
      irreducible_prime := hirr
      exponent := exponent
      decompositionIso := Classical.choice hIso }

/--
Unconditional prime-power PID module decomposition theorem.

This is the strongest module-level classification result currently obtained
directly from mathlib in this bridge.  It is intentionally not named
`exists_pid_module_structure`, because the latter project's target requires an
ordered invariant-factor model.
-/
theorem exists_pid_primePower_module_decomposition
    (R : Type v) (M : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Nonempty (PIDPrimePowerModuleDecompositionData R M) :=
  ⟨pidPrimePowerModuleDecompositionDataOfFinite R M⟩

end MatDecompFormal.Instances
