/-
Copyright (c) 2026 Wanli Ma, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanli Ma, Zichen Wang
-/
import MatDecompFormal.Framework.Induction
import MatDecompFormal.Framework.UniverseDecompositionSquareSubtype

namespace MatDecompFormal.Framework

open Matrix

/-!
# Universe Decomposition Instances

This file is the framework entry point for the universe decomposition drivers.
-/

section CoreDriverPackaging

/--
`SubtypeInductionInstance` packages exactly the data needed to run
`induction_on_subtype` on a universe `X` with a distinguished subtype `SubX`.
-/
structure SubtypeInductionInstance (X SubX : Type*) (toX : SubX → X) where
  μ : X → Nat
  μ_base : Nat
  P : X → Prop
  P_sub : SubX → Prop
  P_compat : ∀ (x_sub : SubX), P_sub x_sub ↔ P (toX x_sub)

  r_sub : SubX → SubX → Prop
  IsSliceable_sub : SubX → Prop
  slice_sub : ∀ (x_sub : SubX), IsSliceable_sub x_sub → X

  transport_sub :
    ∀ {x_sub y_sub}, r_sub y_sub x_sub → P_sub y_sub → P_sub x_sub

  lift_from_slice_sub :
    ∀ (x_sub : SubX) (hx : IsSliceable_sub x_sub),
      P (slice_sub x_sub hx) → P_sub x_sub

  /--
  Reachability packaged in the “metric > μ_base” style.
  -/
  reach_sub :
    ∀ (x_sub : SubX), μ (toX x_sub) > μ_base →
      Σ' (y_sub : SubX), Σ' (hy : IsSliceable_sub y_sub),
        r_sub y_sub x_sub ∧ μ (slice_sub y_sub hy) < μ (toX x_sub)

  /--
  Base case on the whole universe:
  either `x` is not in the subtype-image, or `μ x ≤ μ_base`.
  -/
  base_univ :
    ∀ (x : X), (∀ (x_sub : SubX), toX x_sub ≠ x) ∨ μ x ≤ μ_base → P x

namespace SubtypeInductionInstance

variable {X SubX : Type*} {toX : SubX → X}

/-- Main driver: directly calls `induction_on_subtype'`. -/
theorem prove (inst : SubtypeInductionInstance X SubX toX) :
    ∀ (x : X), inst.P x := by
  let BaseSet : X → Prop := fun x => inst.μ x ≤ inst.μ_base

  refine induction_on_subtype'
    (X := X)
    SubX toX
    inst.μ (· < ·) wellFounded_lt
    inst.P
    inst.P_sub
    inst.P_compat
    (r_sub := inst.r_sub)
    (IsSliceable_sub := inst.IsSliceable_sub)
    (slice_sub := inst.slice_sub)
    (transport_sub := inst.transport_sub)
    (lift_from_slice_sub := inst.lift_from_slice_sub)
    (BaseSet := BaseSet)
    (reach_sub := by
      intro x_sub h_not_base
      have h_gt : inst.μ (toX x_sub) > inst.μ_base :=
        Nat.lt_of_not_ge h_not_base
      rcases inst.reach_sub x_sub h_gt with ⟨y_sub, hy, h_r, h_prog⟩
      exact ⟨y_sub, hy, h_r, h_prog⟩)
    (base_univ := by
      intro x hx
      simpa [BaseSet] using inst.base_univ x hx)

end SubtypeInductionInstance

end CoreDriverPackaging

section Specializations

/-- Rectangular specialization: `X = RectUniverse R`, `SubX = PosRectUniverse R`. -/
abbrev RectSubtypeInductionInstance (R : Type*) :=
  SubtypeInductionInstance (X := RectUniverse R)
    (SubX := PosRectUniverse R) (toX := Subtype.val)

namespace RectSubtypeInductionInstance

variable {R : Type*} (inst : RectSubtypeInductionInstance R)

theorem prove_for_matrix :
    ∀ {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
      [Fintype κ] [DecidableEq κ] [LinearOrder κ],
      (A : Matrix ι κ R) → inst.P (RectUniverse.ofMatrix A) := by
  intro ι κ _ _ _ _ _ _ A
  exact (SubtypeInductionInstance.prove inst) (RectUniverse.ofMatrix A)

end RectSubtypeInductionInstance

/-- Square specialization: `X = SquareUniverse R`, `SubX = PosSquareUniverse R`. -/
abbrev SquareSubtypeInductionInstance (R : Type*) :=
  SubtypeInductionInstance (X := SquareUniverse R)
    (SubX := PosSquareUniverse R) (toX := Subtype.val)

namespace SquareSubtypeInductionInstance

variable {R : Type*} (inst : SquareSubtypeInductionInstance R)

theorem prove_for_matrix :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι],
      (A : Matrix ι ι R) → inst.P (SquareUniverse.ofMatrix A) := by
  intro ι _ _ _ A
  exact (SubtypeInductionInstance.prove (inst := inst)) (SquareUniverse.ofMatrix A)

end SquareSubtypeInductionInstance

end Specializations

end MatDecompFormal.Framework
