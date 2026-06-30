/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.OrthogonalHessenberg.Direct

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Orthogonal/Unitary Hessenberg Framework Entry

The public theorem is routed through the boundary-column subtype descent
template.  It is conditional on a named unitary one-step oracle; constructing
that oracle by Householder or Givens transformations is the remaining concrete
numerical step from the plan.
-/

/-- Proof-side data for the unitary boundary-column descent. -/
structure UnitaryHessenbergBoundaryProofData where
  r_sub :
    PosHessenbergBoundaryUniverse ℂ → PosHessenbergBoundaryUniverse ℂ → Prop
  IsSliceable_sub : PosHessenbergBoundaryUniverse ℂ → Prop
  slice_sub :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℂ,
      IsSliceable_sub x_sub → HessenbergBoundaryUniverse.{u} ℂ
  transport_sub :
    ∀ {x_sub y_sub : PosHessenbergBoundaryUniverse ℂ},
      r_sub y_sub x_sub →
        UnitaryHessenbergBoundary_P (y_sub : HessenbergBoundaryUniverse.{u} ℂ) →
          UnitaryHessenbergBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
  lift_from_slice_sub :
    ∀ (x_sub : PosHessenbergBoundaryUniverse ℂ) (hx : IsSliceable_sub x_sub),
      UnitaryHessenbergBoundary_P (slice_sub x_sub hx) →
        UnitaryHessenbergBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
  reach_sub :
    ∀ x_sub : PosHessenbergBoundaryUniverse ℂ,
      hessenbergBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} ℂ) >
        hessenbergBoundaryμBase →
        Σ' (y_sub : PosHessenbergBoundaryUniverse ℂ),
          Σ' (hy : IsSliceable_sub y_sub),
            r_sub y_sub x_sub ∧
              hessenbergBoundaryμ (slice_sub y_sub hy) <
                hessenbergBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} ℂ)

/-- Convert a unitary one-step oracle into proof-side descent data. -/
noncomputable def unitaryHessenbergBoundaryProofDataOfStepOracle
    (oracle : UnitaryHessenbergBoundaryStepOracle.{u}) :
    UnitaryHessenbergBoundaryProofData.{u} where
  r_sub := unitaryHessenbergBoundaryStepRel oracle
  IsSliceable_sub := fun x_sub =>
    HessenbergBoundaryReady (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
  slice_sub := fun x_sub _ => hessenbergBoundarySliceSub x_sub
  transport_sub := by
    intro x_sub y_sub hrel hP
    subst hrel
    exact
      unitaryHessenbergBoundary_transport_unitarySimilarity
        (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
        (oracle.Q x_sub) (oracle.unitary_Q x_sub) hP
  lift_from_slice_sub := by
    intro x_sub hx hP
    exact unitaryHessenbergBoundary_lift_from_ready x_sub hx hP
  reach_sub := by
    intro x_sub hgt
    let y_sub := unitaryHessenbergBoundaryStepObject oracle x_sub
    have hslice : HessenbergBoundaryReady (y_sub : HessenbergBoundaryUniverse.{u} ℂ) := by
      simpa [y_sub, unitaryHessenbergBoundaryStepObject] using oracle.ready x_sub
    have hmono :
        hessenbergBoundaryμ (y_sub : HessenbergBoundaryUniverse.{u} ℂ) ≤
          hessenbergBoundaryμ (x_sub : HessenbergBoundaryUniverse.{u} ℂ) := by
      simp [y_sub, unitaryHessenbergBoundaryStepObject,
        unitaryHessenbergBoundarySimilarityObject, hessenbergBoundaryμ]
    exact
      ⟨y_sub, hslice, rfl,
        lt_of_lt_of_le (hessenbergBoundarySliceProgress y_sub) hmono⟩

/-- Boundary base case for the unitary target. -/
theorem unitaryHessenbergBoundary_base_univ
    (x : HessenbergBoundaryUniverse.{u} ℂ) :
    ((∀ x_sub : PosHessenbergBoundaryUniverse ℂ,
        (x_sub : HessenbergBoundaryUniverse ℂ) ≠ x) ∨
      hessenbergBoundaryμ x ≤ hessenbergBoundaryμBase) →
      UnitaryHessenbergBoundary_P x := by
  intro hx hne
  have hzero : Fintype.card x.ι = 0 :=
    hessenbergBoundaryBaseDimEqZero x hx
  letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hzero
  exact False.elim (IsEmpty.false (Classical.choice hne))

/-- Subtype-induction instance for the unitary boundary-column descent. -/
noncomputable def unitaryHessenbergBoundary_framework_inst
    (proofData : UnitaryHessenbergBoundaryProofData.{u}) :
    SubtypeInductionInstance
      (HessenbergBoundaryUniverse.{u} ℂ)
      (PosHessenbergBoundaryUniverse ℂ)
      (fun x => (x : HessenbergBoundaryUniverse.{u} ℂ)) where
  μ := hessenbergBoundaryμ
  μ_base := hessenbergBoundaryμBase
  P := UnitaryHessenbergBoundary_P
  P_sub := fun x_sub =>
    UnitaryHessenbergBoundary_P (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
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
  base_univ := unitaryHessenbergBoundary_base_univ

/-- Boundary-column framework theorem for unitary Hessenberg reduction. -/
theorem exists_unitaryHessenbergBoundary_framework
    (proofData : UnitaryHessenbergBoundaryProofData.{u})
    (x : HessenbergBoundaryUniverse.{u} ℂ) :
    UnitaryHessenbergBoundary_P x := by
  let inst :
      SubtypeInductionInstance
        (HessenbergBoundaryUniverse.{u} ℂ)
        (PosHessenbergBoundaryUniverse ℂ)
        (fun x => (x : HessenbergBoundaryUniverse.{u} ℂ)) :=
    unitaryHessenbergBoundary_framework_inst proofData
  exact
    (SubtypeInductionInstance.prove inst) x

/-- Forget the protected boundary-column condition from a unitary boundary witness. -/
theorem hasUnitaryHessenberg_of_hasUnitaryHessenbergBoundary
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} {c : Matrix ι Unit ℂ} :
    HasUnitaryHessenbergBoundary A c → HasUnitaryHessenberg A := by
  intro h
  rcases h with ⟨Q, H, hQ, hHess, hEq, _hBoundary⟩
  exact ⟨Q, H, hQ, hHess, hEq⟩

/--
Unitary Hessenberg reduction through the boundary-column descent driver,
conditional on a unitary one-step oracle.
-/
theorem exists_unitary_hessenberg_reduction
    (oracle : UnitaryHessenbergBoundaryStepOracle.{u})
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasUnitaryHessenberg A := by
  by_cases hne : Nonempty ι
  · let x : HessenbergBoundaryUniverse.{u} ℂ :=
      { ι := ι
        A := A
        c := 0 }
    have hP : UnitaryHessenbergBoundary_P x :=
      exists_unitaryHessenbergBoundary_framework
        (unitaryHessenbergBoundaryProofDataOfStepOracle oracle) x
    have hBoundary : HasUnitaryHessenbergBoundary A (0 : Matrix ι Unit ℂ) := by
      simpa [x] using hP hne
    exact hasUnitaryHessenberg_of_hasUnitaryHessenbergBoundary hBoundary
  · letI : IsEmpty ι := not_nonempty_iff.mp hne
    letI : Subsingleton ι := by infer_instance
    exact base_unitaryHessenberg_subsingleton A

/--
Ordinary Hessenberg reduction obtained from the same unitary boundary oracle by
forgetting unitarity. This confirms the new instance strengthens, rather than
replaces, the existing Hessenberg target.
-/
theorem exists_hessenberg_reduction_of_unitary_oracle
    (oracle : UnitaryHessenbergBoundaryStepOracle.{u})
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasHessenberg A :=
  hasHessenberg_of_hasUnitaryHessenberg
    (exists_unitary_hessenberg_reduction oracle A)

end MatDecompFormal.Instances
