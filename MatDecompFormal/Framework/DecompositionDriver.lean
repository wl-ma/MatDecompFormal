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

/-- The codomain of the reachability witness for a fixed slice-data package. -/
abbrev SquareReachType (sliceData : SquareSliceData R) (x_sub : PosSquareUniverse R) :=
  Σ' (y_sub : PosSquareUniverse R), Σ' (hy : sliceData.IsSliceable_sub y_sub),
    sliceData.r_sub y_sub x_sub ∧
      squareSubtypeμ (sliceData.slice_sub y_sub hy) <
        squareSubtypeμ (x_sub : SquareUniverse R)

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

section StrategyBridge

/-- Positive-dimensional square universe objects have nonempty index types. -/
lemma posSquareUniverse_nonempty {R : Type*} (x_sub : PosSquareUniverse R) : Nonempty x_sub.1.ι := by
  classical
  exact Fintype.card_pos_iff.mp x_sub.2

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
