/-
Copyright (c) 2026 Wanli Ma, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanli Ma, Zichen Wang
-/
import MatDecompFormal.Abstractions.Strategy
import MatDecompFormal.Framework.UniverseDecomposition

namespace MatDecompFormal.Framework

/-!
# Decomposition Driver

This file packages the reusable assembly pattern from:

* a universe-level target predicate `P`;
* a universe-level base-case proof;
* recursive step data on `PosSquareUniverse`;

to a concrete `SquareSubtypeInductionInstance`.
-/

open Matrix
open MatDecompFormal.Abstractions

universe u

variable {R : Type*}

/-- Structural slicing data for a square-universe driver. -/
structure SquareSliceData (R : Type*) where
  r_sub : PosSquareUniverse R → PosSquareUniverse R → Prop
  IsSliceable_sub : PosSquareUniverse R → Prop
  slice_sub :
    ∀ (x_sub : PosSquareUniverse R), IsSliceable_sub x_sub → SquareUniverse R

/-- Structural slicing data for a rectangular-universe driver. -/
structure RectSliceData (R : Type*) where
  r_sub : PosRectUniverse R → PosRectUniverse R → Prop
  IsSliceable_sub : PosRectUniverse R → Prop
  slice_sub :
    ∀ (x_sub : PosRectUniverse R), IsSliceable_sub x_sub → RectUniverse R

/-- The codomain of the reachability witness for a fixed slice-data package. -/
abbrev SquareReachType (sliceData : SquareSliceData R) (x_sub : PosSquareUniverse R) :=
  Σ' (y_sub : PosSquareUniverse R), Σ' (hy : sliceData.IsSliceable_sub y_sub),
    sliceData.r_sub y_sub x_sub ∧
      squareSubtypeμ (sliceData.slice_sub y_sub hy) <
        squareSubtypeμ (x_sub : SquareUniverse R)

/-- The codomain of the rectangular reachability witness for a fixed slice-data package. -/
abbrev RectReachType (sliceData : RectSliceData R) (x_sub : PosRectUniverse R) :=
  Σ' (y_sub : PosRectUniverse R), Σ' (hy : sliceData.IsSliceable_sub y_sub),
    sliceData.r_sub y_sub x_sub ∧
      rectSubtypeμ (sliceData.slice_sub y_sub hy) <
        rectSubtypeμ (x_sub : RectUniverse R)

/-- Type of a transport hook for a fixed target predicate and slice package. -/
abbrev SquareTransportType (P : SquareUniverse R → Prop)
    (sliceData : SquareSliceData R) :=
  ∀ {x_sub y_sub : PosSquareUniverse R},
    sliceData.r_sub y_sub x_sub →
      P (y_sub : SquareUniverse R) → P (x_sub : SquareUniverse R)

/-- Type of a lift hook from sliced subproblems for a fixed target predicate and slice package. -/
abbrev SquareLiftType (P : SquareUniverse R → Prop)
    (sliceData : SquareSliceData R) :=
  ∀ (x_sub : PosSquareUniverse R) (hx : sliceData.IsSliceable_sub x_sub),
    P (sliceData.slice_sub x_sub hx) → P (x_sub : SquareUniverse R)

/-- Proof-side hooks for a fixed target predicate and slice package. -/
structure SquareProofData (P : SquareUniverse R → Prop) (sliceData : SquareSliceData R) where
  transport_sub : SquareTransportType P sliceData
  lift_from_slice_sub : SquareLiftType P sliceData

/-- Type of a transport hook for a fixed rectangular target predicate and slice package. -/
abbrev RectTransportType (P : RectUniverse R → Prop)
    (sliceData : RectSliceData R) :=
  ∀ {x_sub y_sub : PosRectUniverse R},
    sliceData.r_sub y_sub x_sub →
      P (y_sub : RectUniverse R) → P (x_sub : RectUniverse R)

/-- Type of a lift hook from rectangular sliced subproblems. -/
abbrev RectLiftType (P : RectUniverse R → Prop)
    (sliceData : RectSliceData R) :=
  ∀ (x_sub : PosRectUniverse R) (hx : sliceData.IsSliceable_sub x_sub),
    P (sliceData.slice_sub x_sub hx) → P (x_sub : RectUniverse R)

/-- Proof-side hooks for a fixed rectangular target predicate and slice package. -/
structure RectProofData (P : RectUniverse R → Prop) (sliceData : RectSliceData R) where
  transport_sub : RectTransportType P sliceData
  lift_from_slice_sub : RectLiftType P sliceData

/-- Assemble a square-universe induction driver from target/base/step data. -/
noncomputable def mkSquareSubtypeInductionInstance
    (P : SquareUniverse R → Prop)
    (base_univ :
      ∀ (x : SquareUniverse R),
        (∀ (x_sub : PosSquareUniverse R), (x_sub : SquareUniverse R) ≠ x) ∨
          squareSubtypeμ x ≤ squareSubtypeμBase →
            P x)
    (sliceData : SquareSliceData R)
    (reach_sub :
      ∀ (x_sub : PosSquareUniverse R),
        squareSubtypeμ (x_sub : SquareUniverse R) > squareSubtypeμBase →
          SquareReachType sliceData x_sub)
    (proofData : SquareProofData P sliceData) :
    SquareSubtypeInductionInstance R where
  μ := squareSubtypeμ
  μ_base := squareSubtypeμBase
  P := P
  P_sub := fun x_sub => P (x_sub : SquareUniverse R)
  P_compat := by
    intro x_sub
    rfl
  r_sub := sliceData.r_sub
  IsSliceable_sub := sliceData.IsSliceable_sub
  slice_sub := sliceData.slice_sub
  transport_sub := by
    intro x_sub y_sub h_r hP
    exact proofData.transport_sub h_r hP
  lift_from_slice_sub := by
    intro x_sub hx hP
    exact proofData.lift_from_slice_sub x_sub hx hP
  reach_sub := by
    intro x_sub h_gt
    exact reach_sub x_sub h_gt
  base_univ := base_univ

/-- Assemble a rectangular-universe induction driver from target/base/step data. -/
noncomputable def mkRectSubtypeInductionInstance
    (P : RectUniverse R → Prop)
    (base_univ :
      ∀ (x : RectUniverse R),
        (∀ (x_sub : PosRectUniverse R), (x_sub : RectUniverse R) ≠ x) ∨
          rectSubtypeμ x ≤ rectSubtypeμBase →
            P x)
    (sliceData : RectSliceData R)
    (reach_sub :
      ∀ (x_sub : PosRectUniverse R),
        rectSubtypeμ (x_sub : RectUniverse R) > rectSubtypeμBase →
          RectReachType sliceData x_sub)
    (proofData : RectProofData P sliceData) :
    RectSubtypeInductionInstance R where
  μ := rectSubtypeμ
  μ_base := rectSubtypeμBase
  P := P
  P_sub := fun x_sub => P (x_sub : RectUniverse R)
  P_compat := by
    intro x_sub
    rfl
  r_sub := sliceData.r_sub
  IsSliceable_sub := sliceData.IsSliceable_sub
  slice_sub := sliceData.slice_sub
  transport_sub := by
    intro x_sub y_sub h_r hP
    exact proofData.transport_sub h_r hP
  lift_from_slice_sub := by
    intro x_sub hx hP
    exact proofData.lift_from_slice_sub x_sub hx hP
  reach_sub := by
    intro x_sub h_gt
    exact reach_sub x_sub h_gt
  base_univ := base_univ

section StrategyBridge

/-- Positive-dimensional square universe objects have nonempty index types. -/
lemma posSquareUniverse_nonempty {R : Type*}
    (x_sub : PosSquareUniverse R) : Nonempty x_sub.1.ι := by
  classical
  exact Fintype.card_pos_iff.mp x_sub.2

/-- Positive rectangular universe objects have nonempty row index types. -/
lemma posRectUniverse_row_nonempty {R : Type*} (x_sub : PosRectUniverse R) :
    Nonempty x_sub.1.ι := by
  classical
  exact Fintype.card_pos_iff.mp x_sub.2.1

/-- Positive rectangular universe objects have nonempty column index types. -/
lemma posRectUniverse_col_nonempty {R : Type*} (x_sub : PosRectUniverse R) :
    Nonempty x_sub.1.κ := by
  classical
  exact Fintype.card_pos_iff.mp x_sub.2.2

/--
`SquareStrategyCore` packages the purely strategy-side part of a family of
square-matrix elimination steps, indexed only by the ambient matrix type.
-/
structure SquareStrategyCore (R : Type*) where
  SliceIdx :
    ∀ {ι : Type u}, Fintype ι → DecidableEq ι → LinearOrder ι → Nonempty ι → Type u
  sliceFintype :
    ∀ {ι : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι),
      Fintype (SliceIdx fι dι oι nι)
  sliceDecEq :
    ∀ {ι : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι),
      DecidableEq (SliceIdx fι dι oι nι)
  sliceLinearOrder :
    ∀ {ι : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι),
      LinearOrder (SliceIdx fι dι oι nι)
  strategy :
    ∀ {ι : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι),
      ReductionStrategy ι ι (SliceIdx fι dι oι nι) (SliceIdx fι dι oι nι) R
  μ_eq :
    ∀ {ι : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι) (nι : Nonempty ι)
      (A : Matrix ι ι R),
      (strategy fι dι oι nι).μ A = Fintype.card ι
  μ_slice_eq :
    ∀ {ι : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι) (nι : Nonempty ι)
      (B : Matrix (SliceIdx fι dι oι nι) (SliceIdx fι dι oι nι) R),
      (strategy fι dι oι nι).μ_slice B =
        @Fintype.card (SliceIdx fι dι oι nι) (sliceFintype fι dι oι nι)

/-- Strategy-side transport hook type for a fixed target predicate. -/
abbrev SquareStrategyTransportType (P : SquareUniverse R → Prop)
    (C : SquareStrategyCore R) :=
  ∀ {ι : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι) (nι : Nonempty ι)
    {A B : Matrix ι ι R},
    (C.strategy fι dι oι nι).r B A →
      P (SquareUniverse.ofMatrix B) → P (SquareUniverse.ofMatrix A)

/-- Strategy-side lift hook type for a fixed target predicate. -/
abbrev SquareStrategyLiftType (P : SquareUniverse R → Prop)
    (C : SquareStrategyCore R) :=
  ∀ {ι : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι) (nι : Nonempty ι)
    (A : Matrix ι ι R)
    (hA : (C.strategy fι dι oι nι).reduction.IsSliceable A),
    P ({
      ι := C.SliceIdx fι dι oι nι
      fintype_ι := C.sliceFintype fι dι oι nι
      decEq_ι := C.sliceDecEq fι dι oι nι
      linOrder_ι := C.sliceLinearOrder fι dι oι nι
      A := (C.strategy fι dι oι nι).reduction.slice A hA
    } : SquareUniverse R) →
      P (SquareUniverse.ofMatrix A)

/-- Strategy-side proof hooks for a fixed target predicate. -/
structure SquareStrategyProofData (R : Type*) (P : SquareUniverse R → Prop)
    (C : SquareStrategyCore R) where
  transport :
    SquareStrategyTransportType P C
  lift :
    SquareStrategyLiftType P C

/--
`SquareStrategyData` packages a family of square-matrix reduction strategies,
indexed only by the ambient matrix type, together with the target-specific
proof hooks needed to turn the strategy family into a universe-level driver.
-/
structure SquareStrategyData (R : Type*) (P : SquareUniverse R → Prop) where
  core : SquareStrategyCore R
  proofData : SquareStrategyProofData R P core

namespace SquareStrategyData

variable {P : SquareUniverse R → Prop}

/-- Repackage a same-index transformed matrix as a positive square universe object. -/
@[simp] def posOfMatrix (_D : SquareStrategyData R P)
    (x_sub : PosSquareUniverse R)
    (B : Matrix x_sub.1.ι x_sub.1.ι R) : PosSquareUniverse R :=
  ⟨{ ι := x_sub.1.ι
     fintype_ι := x_sub.1.fintype_ι
     decEq_ι := x_sub.1.decEq_ι
     linOrder_ι := x_sub.1.linOrder_ι
     A := B }, by simpa [squareSubtypeμ] using x_sub.2⟩

/-- The universe-level relation induced by the local strategy on a positive object. -/
def rSub (D : SquareStrategyData R P) (y_sub x_sub : PosSquareUniverse R) : Prop :=
  letI : Nonempty x_sub.1.ι := posSquareUniverse_nonempty x_sub
  let fι : Fintype x_sub.1.ι := inferInstance
  let dι : DecidableEq x_sub.1.ι := inferInstance
  let oι : LinearOrder x_sub.1.ι := inferInstance
  let nι : Nonempty x_sub.1.ι := inferInstance
  ∃ (B : Matrix x_sub.1.ι x_sub.1.ι R),
    y_sub = D.posOfMatrix x_sub B ∧
      (D.core.strategy fι dι oι nι).r B x_sub.1.A

/-- The universe-level slicability predicate induced by the local strategy. -/
def isSliceableSub (D : SquareStrategyData R P) (x_sub : PosSquareUniverse R) : Prop :=
  letI : Nonempty x_sub.1.ι := posSquareUniverse_nonempty x_sub
  let fι : Fintype x_sub.1.ι := inferInstance
  let dι : DecidableEq x_sub.1.ι := inferInstance
  let oι : LinearOrder x_sub.1.ι := inferInstance
  let nι : Nonempty x_sub.1.ι := inferInstance
  (D.core.strategy fι dι oι nι).reduction.IsSliceable x_sub.1.A

/-- Slice a positive universe object using the local strategy. -/
noncomputable def sliceUniverse (D : SquareStrategyData R P)
    (x_sub : PosSquareUniverse R) (hx : D.isSliceableSub x_sub) : SquareUniverse R := by
  letI : Nonempty x_sub.1.ι := posSquareUniverse_nonempty x_sub
  let fι : Fintype x_sub.1.ι := inferInstance
  let dι : DecidableEq x_sub.1.ι := inferInstance
  let oι : LinearOrder x_sub.1.ι := inferInstance
  let nι : Nonempty x_sub.1.ι := inferInstance
  letI := D.core.sliceFintype fι dι oι nι
  letI := D.core.sliceDecEq fι dι oι nι
  letI := D.core.sliceLinearOrder fι dι oι nι
  exact SquareUniverse.ofMatrix ((D.core.strategy fι dι oι nι).reduction.slice x_sub.1.A hx)

/-- Convert strategy data to the structural slice package expected by the driver. -/
noncomputable def sliceData (D : SquareStrategyData R P) : SquareSliceData R where
  r_sub := D.rSub
  IsSliceable_sub := D.isSliceableSub
  slice_sub := D.sliceUniverse

/-- Convert strategy-side transport/lifting to the driver proof hooks. -/
noncomputable def driverProofData (D : SquareStrategyData R P) :
    SquareProofData P (D.sliceData) where
  transport_sub := by
    intro x_sub y_sub h_r hP
    letI : Nonempty x_sub.1.ι := posSquareUniverse_nonempty x_sub
    let fι : Fintype x_sub.1.ι := inferInstance
    let dι : DecidableEq x_sub.1.ι := inferInstance
    let oι : LinearOrder x_sub.1.ι := inferInstance
    let nι : Nonempty x_sub.1.ι := inferInstance
    rcases h_r with ⟨B, rfl, h_rel⟩
    simpa using D.proofData.transport fι dι oι nι (A := x_sub.1.A) (B := B) h_rel hP
  lift_from_slice_sub := by
    intro x_sub hx hP
    letI : Nonempty x_sub.1.ι := posSquareUniverse_nonempty x_sub
    let fι : Fintype x_sub.1.ι := inferInstance
    let dι : DecidableEq x_sub.1.ι := inferInstance
    let oι : LinearOrder x_sub.1.ι := inferInstance
    let nι : Nonempty x_sub.1.ι := inferInstance
    simpa [sliceData, sliceUniverse, isSliceableSub] using
      D.proofData.lift fι dι oι nι x_sub.1.A hx hP

/-- Convert strategy-side reachability to the universe-level reach witness. -/
noncomputable def reachSub (D : SquareStrategyData R P) :
    ∀ (x_sub : PosSquareUniverse R),
      squareSubtypeμ (x_sub : SquareUniverse R) > squareSubtypeμBase →
        SquareReachType (D.sliceData) x_sub := by
  intro x_sub h_gt
  letI : Nonempty x_sub.1.ι := posSquareUniverse_nonempty x_sub
  let fι : Fintype x_sub.1.ι := inferInstance
  let dι : DecidableEq x_sub.1.ι := inferInstance
  let oι : LinearOrder x_sub.1.ι := inferInstance
  let nι : Nonempty x_sub.1.ι := inferInstance
  let S := D.core.strategy fι dι oι nι
  have hμ_gt : S.μ x_sub.1.A > squareSubtypeμBase := by
    rw [D.core.μ_eq fι dι oι nι x_sub.1.A]
    simpa [squareSubtypeμ, squareSubtypeμBase] using h_gt
  rcases ReductionStrategy.mk_reach
      (S := S)
      (μ_base := squareSubtypeμBase)
      (A := x_sub.1.A)
      (by constructor <;> infer_instance)
      hμ_gt with ⟨B, hB, h_rel, h_prog⟩
  let y_sub := D.posOfMatrix x_sub B
  have hy : D.isSliceableSub y_sub := by
    simpa [isSliceableSub, posOfMatrix, y_sub] using hB
  refine ⟨y_sub, hy, ?_, ?_⟩
  · exact ⟨B, rfl, h_rel⟩
  · have h_slice_card :
      squareSubtypeμ (D.sliceUniverse y_sub hy) =
          S.μ_slice (S.reduction.slice B hB) := by
      letI := D.core.sliceFintype fι dι oι nι
      change Fintype.card (D.core.SliceIdx fι dι oι nι) =
        S.μ_slice (S.reduction.slice B hB)
      rw [D.core.μ_slice_eq fι dι oι nι (S.reduction.slice B hB)]
    change squareSubtypeμ (D.sliceUniverse y_sub hy) <
      squareSubtypeμ (x_sub : SquareUniverse R)
    rw [h_slice_card]
    rw [D.core.μ_eq fι dι oι nι x_sub.1.A] at h_prog
    simpa [squareSubtypeμ, squareSubtypeμBase] using h_prog

end SquareStrategyData

/-- Build target-specific strategy data from strategy core and proof hooks. -/
@[simps] def mkSquareStrategyData {P : SquareUniverse R → Prop}
    (C : SquareStrategyCore R)
    (proofData : SquareStrategyProofData R P C) :
    SquareStrategyData R P where
  core := C
  proofData := proofData

section RectStrategyBridge

/--
`RectStrategyCore` packages a rectangular matrix reduction family with separate
row and column slice index types.
-/
structure RectStrategyCore (R : Type*) where
  RowSliceIdx :
    ∀ {ι κ : Type u},
      Fintype ι → DecidableEq ι → LinearOrder ι → Nonempty ι →
      Fintype κ → DecidableEq κ → LinearOrder κ → Nonempty κ → Type u
  ColSliceIdx :
    ∀ {ι κ : Type u},
      Fintype ι → DecidableEq ι → LinearOrder ι → Nonempty ι →
      Fintype κ → DecidableEq κ → LinearOrder κ → Nonempty κ → Type u
  rowSliceFintype :
    ∀ {ι κ : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι) (fκ : Fintype κ) (dκ : DecidableEq κ) (oκ : LinearOrder κ)
      (nκ : Nonempty κ),
      Fintype (RowSliceIdx fι dι oι nι fκ dκ oκ nκ)
  rowSliceDecEq :
    ∀ {ι κ : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι) (fκ : Fintype κ) (dκ : DecidableEq κ) (oκ : LinearOrder κ)
      (nκ : Nonempty κ),
      DecidableEq (RowSliceIdx fι dι oι nι fκ dκ oκ nκ)
  rowSliceLinearOrder :
    ∀ {ι κ : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι) (fκ : Fintype κ) (dκ : DecidableEq κ) (oκ : LinearOrder κ)
      (nκ : Nonempty κ),
      LinearOrder (RowSliceIdx fι dι oι nι fκ dκ oκ nκ)
  colSliceFintype :
    ∀ {ι κ : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι) (fκ : Fintype κ) (dκ : DecidableEq κ) (oκ : LinearOrder κ)
      (nκ : Nonempty κ),
      Fintype (ColSliceIdx fι dι oι nι fκ dκ oκ nκ)
  colSliceDecEq :
    ∀ {ι κ : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι) (fκ : Fintype κ) (dκ : DecidableEq κ) (oκ : LinearOrder κ)
      (nκ : Nonempty κ),
      DecidableEq (ColSliceIdx fι dι oι nι fκ dκ oκ nκ)
  colSliceLinearOrder :
    ∀ {ι κ : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι) (fκ : Fintype κ) (dκ : DecidableEq κ) (oκ : LinearOrder κ)
      (nκ : Nonempty κ),
      LinearOrder (ColSliceIdx fι dι oι nι fκ dκ oκ nκ)
  strategy :
    ∀ {ι κ : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι) (fκ : Fintype κ) (dκ : DecidableEq κ) (oκ : LinearOrder κ)
      (nκ : Nonempty κ),
      ReductionStrategy ι κ
        (RowSliceIdx fι dι oι nι fκ dκ oκ nκ)
        (ColSliceIdx fι dι oι nι fκ dκ oκ nκ) R
  μ_eq :
    ∀ {ι κ : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι) (fκ : Fintype κ) (dκ : DecidableEq κ) (oκ : LinearOrder κ)
      (nκ : Nonempty κ) (A : Matrix ι κ R),
      (strategy fι dι oι nι fκ dκ oκ nκ).μ A =
        min (Fintype.card ι) (Fintype.card κ)
  μ_slice_eq :
    ∀ {ι κ : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
      (nι : Nonempty ι) (fκ : Fintype κ) (dκ : DecidableEq κ) (oκ : LinearOrder κ)
      (nκ : Nonempty κ)
      (B : Matrix
        (RowSliceIdx fι dι oι nι fκ dκ oκ nκ)
        (ColSliceIdx fι dι oι nι fκ dκ oκ nκ) R),
      (strategy fι dι oι nι fκ dκ oκ nκ).μ_slice B =
        min
          (@Fintype.card (RowSliceIdx fι dι oι nι fκ dκ oκ nκ)
            (rowSliceFintype fι dι oι nι fκ dκ oκ nκ))
          (@Fintype.card (ColSliceIdx fι dι oι nι fκ dκ oκ nκ)
            (colSliceFintype fι dι oι nι fκ dκ oκ nκ))

/-- Strategy-side transport hook type for a fixed rectangular target predicate. -/
abbrev RectStrategyTransportType (P : RectUniverse R → Prop)
    (C : RectStrategyCore R) :=
  ∀ {ι κ : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
    (nι : Nonempty ι) (fκ : Fintype κ) (dκ : DecidableEq κ) (oκ : LinearOrder κ)
    (nκ : Nonempty κ) {A B : Matrix ι κ R},
    (C.strategy fι dι oι nι fκ dκ oκ nκ).r B A →
      P (RectUniverse.ofMatrix B) → P (RectUniverse.ofMatrix A)

/-- Strategy-side lift hook type for a fixed rectangular target predicate. -/
abbrev RectStrategyLiftType (P : RectUniverse R → Prop)
    (C : RectStrategyCore R) :=
  ∀ {ι κ : Type u} (fι : Fintype ι) (dι : DecidableEq ι) (oι : LinearOrder ι)
    (nι : Nonempty ι) (fκ : Fintype κ) (dκ : DecidableEq κ) (oκ : LinearOrder κ)
    (nκ : Nonempty κ) (A : Matrix ι κ R)
    (hA : (C.strategy fι dι oι nι fκ dκ oκ nκ).reduction.IsSliceable A),
    P ({
      ι := C.RowSliceIdx fι dι oι nι fκ dκ oκ nκ
      fintype_ι := C.rowSliceFintype fι dι oι nι fκ dκ oκ nκ
      decEq_ι := C.rowSliceDecEq fι dι oι nι fκ dκ oκ nκ
      linOrder_ι := C.rowSliceLinearOrder fι dι oι nι fκ dκ oκ nκ
      κ := C.ColSliceIdx fι dι oι nι fκ dκ oκ nκ
      fintype_κ := C.colSliceFintype fι dι oι nι fκ dκ oκ nκ
      decEq_κ := C.colSliceDecEq fι dι oι nι fκ dκ oκ nκ
      linOrder_κ := C.colSliceLinearOrder fι dι oι nι fκ dκ oκ nκ
      A := (C.strategy fι dι oι nι fκ dκ oκ nκ).reduction.slice A hA
    } : RectUniverse R) →
      P (RectUniverse.ofMatrix A)

/-- Strategy-side proof hooks for a fixed rectangular target predicate. -/
structure RectStrategyProofData (R : Type*) (P : RectUniverse R → Prop)
    (C : RectStrategyCore R) where
  transport : RectStrategyTransportType P C
  lift : RectStrategyLiftType P C

/-- Rectangular strategy family plus target-specific proof hooks. -/
structure RectStrategyData (R : Type*) (P : RectUniverse R → Prop) where
  core : RectStrategyCore R
  proofData : RectStrategyProofData R P core

namespace RectStrategyData

variable {P : RectUniverse R → Prop}

@[simp] def posOfMatrix (_D : RectStrategyData R P)
    (x_sub : PosRectUniverse R)
    (B : Matrix x_sub.1.ι x_sub.1.κ R) : PosRectUniverse R :=
  ⟨{ ι := x_sub.1.ι
     fintype_ι := x_sub.1.fintype_ι
     decEq_ι := x_sub.1.decEq_ι
     linOrder_ι := x_sub.1.linOrder_ι
     κ := x_sub.1.κ
     fintype_κ := x_sub.1.fintype_κ
     decEq_κ := x_sub.1.decEq_κ
     linOrder_κ := x_sub.1.linOrder_κ
     A := B }, by simpa [rectSubtypeμ] using x_sub.2⟩

def rSub (D : RectStrategyData R P) (y_sub x_sub : PosRectUniverse R) : Prop :=
  letI : Nonempty x_sub.1.ι := posRectUniverse_row_nonempty x_sub
  letI : Nonempty x_sub.1.κ := posRectUniverse_col_nonempty x_sub
  let fι : Fintype x_sub.1.ι := inferInstance
  let dι : DecidableEq x_sub.1.ι := inferInstance
  let oι : LinearOrder x_sub.1.ι := inferInstance
  let nι : Nonempty x_sub.1.ι := inferInstance
  let fκ : Fintype x_sub.1.κ := inferInstance
  let dκ : DecidableEq x_sub.1.κ := inferInstance
  let oκ : LinearOrder x_sub.1.κ := inferInstance
  let nκ : Nonempty x_sub.1.κ := inferInstance
  ∃ (B : Matrix x_sub.1.ι x_sub.1.κ R),
    y_sub = D.posOfMatrix x_sub B ∧
      (D.core.strategy fι dι oι nι fκ dκ oκ nκ).r B x_sub.1.A

def isSliceableSub (D : RectStrategyData R P) (x_sub : PosRectUniverse R) : Prop :=
  letI : Nonempty x_sub.1.ι := posRectUniverse_row_nonempty x_sub
  letI : Nonempty x_sub.1.κ := posRectUniverse_col_nonempty x_sub
  let fι : Fintype x_sub.1.ι := inferInstance
  let dι : DecidableEq x_sub.1.ι := inferInstance
  let oι : LinearOrder x_sub.1.ι := inferInstance
  let nι : Nonempty x_sub.1.ι := inferInstance
  let fκ : Fintype x_sub.1.κ := inferInstance
  let dκ : DecidableEq x_sub.1.κ := inferInstance
  let oκ : LinearOrder x_sub.1.κ := inferInstance
  let nκ : Nonempty x_sub.1.κ := inferInstance
  (D.core.strategy fι dι oι nι fκ dκ oκ nκ).reduction.IsSliceable x_sub.1.A

noncomputable def sliceUniverse (D : RectStrategyData R P)
    (x_sub : PosRectUniverse R) (hx : D.isSliceableSub x_sub) : RectUniverse R := by
  letI : Nonempty x_sub.1.ι := posRectUniverse_row_nonempty x_sub
  letI : Nonempty x_sub.1.κ := posRectUniverse_col_nonempty x_sub
  let fι : Fintype x_sub.1.ι := inferInstance
  let dι : DecidableEq x_sub.1.ι := inferInstance
  let oι : LinearOrder x_sub.1.ι := inferInstance
  let nι : Nonempty x_sub.1.ι := inferInstance
  let fκ : Fintype x_sub.1.κ := inferInstance
  let dκ : DecidableEq x_sub.1.κ := inferInstance
  let oκ : LinearOrder x_sub.1.κ := inferInstance
  let nκ : Nonempty x_sub.1.κ := inferInstance
  letI := D.core.rowSliceFintype fι dι oι nι fκ dκ oκ nκ
  letI := D.core.rowSliceDecEq fι dι oι nι fκ dκ oκ nκ
  letI := D.core.rowSliceLinearOrder fι dι oι nι fκ dκ oκ nκ
  letI := D.core.colSliceFintype fι dι oι nι fκ dκ oκ nκ
  letI := D.core.colSliceDecEq fι dι oι nι fκ dκ oκ nκ
  letI := D.core.colSliceLinearOrder fι dι oι nι fκ dκ oκ nκ
  exact RectUniverse.ofMatrix
    ((D.core.strategy fι dι oι nι fκ dκ oκ nκ).reduction.slice x_sub.1.A hx)

noncomputable def sliceData (D : RectStrategyData R P) : RectSliceData R where
  r_sub := D.rSub
  IsSliceable_sub := D.isSliceableSub
  slice_sub := D.sliceUniverse

noncomputable def driverProofData (D : RectStrategyData R P) :
    RectProofData P (D.sliceData) where
  transport_sub := by
    intro x_sub y_sub h_r hP
    letI : Nonempty x_sub.1.ι := posRectUniverse_row_nonempty x_sub
    letI : Nonempty x_sub.1.κ := posRectUniverse_col_nonempty x_sub
    let fι : Fintype x_sub.1.ι := inferInstance
    let dι : DecidableEq x_sub.1.ι := inferInstance
    let oι : LinearOrder x_sub.1.ι := inferInstance
    let nι : Nonempty x_sub.1.ι := inferInstance
    let fκ : Fintype x_sub.1.κ := inferInstance
    let dκ : DecidableEq x_sub.1.κ := inferInstance
    let oκ : LinearOrder x_sub.1.κ := inferInstance
    let nκ : Nonempty x_sub.1.κ := inferInstance
    rcases h_r with ⟨B, rfl, h_rel⟩
    simpa using D.proofData.transport fι dι oι nι fκ dκ oκ nκ
      (A := x_sub.1.A) (B := B) h_rel hP
  lift_from_slice_sub := by
    intro x_sub hx hP
    letI : Nonempty x_sub.1.ι := posRectUniverse_row_nonempty x_sub
    letI : Nonempty x_sub.1.κ := posRectUniverse_col_nonempty x_sub
    let fι : Fintype x_sub.1.ι := inferInstance
    let dι : DecidableEq x_sub.1.ι := inferInstance
    let oι : LinearOrder x_sub.1.ι := inferInstance
    let nι : Nonempty x_sub.1.ι := inferInstance
    let fκ : Fintype x_sub.1.κ := inferInstance
    let dκ : DecidableEq x_sub.1.κ := inferInstance
    let oκ : LinearOrder x_sub.1.κ := inferInstance
    let nκ : Nonempty x_sub.1.κ := inferInstance
    simpa [sliceData, sliceUniverse, isSliceableSub] using
      D.proofData.lift fι dι oι nι fκ dκ oκ nκ x_sub.1.A hx hP

noncomputable def reachSub (D : RectStrategyData R P) :
    ∀ (x_sub : PosRectUniverse R),
      rectSubtypeμ (x_sub : RectUniverse R) > rectSubtypeμBase →
        RectReachType (D.sliceData) x_sub := by
  intro x_sub h_gt
  letI : Nonempty x_sub.1.ι := posRectUniverse_row_nonempty x_sub
  letI : Nonempty x_sub.1.κ := posRectUniverse_col_nonempty x_sub
  let fι : Fintype x_sub.1.ι := inferInstance
  let dι : DecidableEq x_sub.1.ι := inferInstance
  let oι : LinearOrder x_sub.1.ι := inferInstance
  let nι : Nonempty x_sub.1.ι := inferInstance
  let fκ : Fintype x_sub.1.κ := inferInstance
  let dκ : DecidableEq x_sub.1.κ := inferInstance
  let oκ : LinearOrder x_sub.1.κ := inferInstance
  let nκ : Nonempty x_sub.1.κ := inferInstance
  let S := D.core.strategy fι dι oι nι fκ dκ oκ nκ
  have hμ_gt : S.μ x_sub.1.A > rectSubtypeμBase := by
    rw [D.core.μ_eq fι dι oι nι fκ dκ oκ nκ x_sub.1.A]
    simpa [rectSubtypeμ, rectSubtypeμBase] using h_gt
  rcases ReductionStrategy.mk_reach
      (S := S)
      (μ_base := rectSubtypeμBase)
      (A := x_sub.1.A)
      (by constructor <;> infer_instance)
      hμ_gt with ⟨B, hB, h_rel, h_prog⟩
  let y_sub := D.posOfMatrix x_sub B
  have hy : D.isSliceableSub y_sub := by
    simpa [isSliceableSub, posOfMatrix, y_sub] using hB
  refine ⟨y_sub, hy, ?_, ?_⟩
  · exact ⟨B, rfl, h_rel⟩
  · have h_slice_card :
      rectSubtypeμ (D.sliceUniverse y_sub hy) =
          S.μ_slice (S.reduction.slice B hB) := by
      letI := D.core.rowSliceFintype fι dι oι nι fκ dκ oκ nκ
      letI := D.core.colSliceFintype fι dι oι nι fκ dκ oκ nκ
      change
        min
          (Fintype.card (D.core.RowSliceIdx fι dι oι nι fκ dκ oκ nκ))
          (Fintype.card (D.core.ColSliceIdx fι dι oι nι fκ dκ oκ nκ)) =
            S.μ_slice (S.reduction.slice B hB)
      rw [D.core.μ_slice_eq fι dι oι nι fκ dκ oκ nκ (S.reduction.slice B hB)]
    change rectSubtypeμ (D.sliceUniverse y_sub hy) <
      rectSubtypeμ (x_sub : RectUniverse R)
    rw [h_slice_card]
    rw [D.core.μ_eq fι dι oι nι fκ dκ oκ nκ x_sub.1.A] at h_prog
    simpa [rectSubtypeμ, rectSubtypeμBase] using h_prog

end RectStrategyData

@[simps] def mkRectStrategyData {P : RectUniverse R → Prop}
    (C : RectStrategyCore R)
    (proofData : RectStrategyProofData R P C) :
    RectStrategyData R P where
  core := C
  proofData := proofData

noncomputable def mkRectSubtypeInductionInstanceFromStrategy
    (P : RectUniverse R → Prop)
    (base_univ :
      ∀ (x : RectUniverse R),
        (∀ (x_sub : PosRectUniverse R), (x_sub : RectUniverse R) ≠ x) ∨
          rectSubtypeμ x ≤ rectSubtypeμBase →
            P x)
    (D : RectStrategyData R P) :
    RectSubtypeInductionInstance R :=
  mkRectSubtypeInductionInstance
    (base_univ := base_univ)
    (sliceData := D.sliceData)
    (reach_sub := D.reachSub)
    (proofData := D.driverProofData)

end RectStrategyBridge

/-- Identity transformation used by lightweight strategy cores. -/
noncomputable def trivialSquareTransform (X : Type*) : Transformation X where
  T := Unit
  Goal := fun _ => True
  apply _ x := x
  find _ _ := ()
  find_spec := by
    intro _ _
    trivial

/-- Assemble a square-universe induction driver directly from strategy-family data. -/
noncomputable def mkSquareSubtypeInductionInstanceFromStrategy
    (P : SquareUniverse R → Prop)
    (base_univ :
      ∀ (x : SquareUniverse R),
        (∀ (x_sub : PosSquareUniverse R), (x_sub : SquareUniverse R) ≠ x) ∨
          squareSubtypeμ x ≤ squareSubtypeμBase →
            P x)
    (D : SquareStrategyData R P) :
    SquareSubtypeInductionInstance R :=
  mkSquareSubtypeInductionInstance
    (base_univ := base_univ)
    (sliceData := D.sliceData)
    (reach_sub := D.reachSub)
    (proofData := D.driverProofData)

end StrategyBridge

end MatDecompFormal.Framework
