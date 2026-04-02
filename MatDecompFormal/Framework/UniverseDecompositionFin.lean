import MatDecompFormal.Framework.Induction
import MatDecompFormal.Framework.UniverseDecompositionFinSquareSubtype

namespace MatDecompFormal.Framework

open Matrix

/-!
# Universe Decomposition Instances (Fin)

This file is the framework entry point for `Fin`-indexed universe decomposition
drivers.

Layering:
1. square cast/subtype support lives in
   `Framework.UniverseDecompositionFinSquareSubtype`;
2. this file defines the core driver packaging;
3. this file also exposes the rectangular and square specializations.
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
    (SubX := SubX) (toX := toX)
    (μ := inst.μ) (relα := (· < ·)) (hwf := wellFounded_lt)
    (P := inst.P)
    (P_sub := inst.P_sub)
    (P_compat := inst.P_compat)
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

/-- Rectangular specialization: `X = FinRectUniverse R`, `SubX = PosFinRectUniverse R`. -/
abbrev RectSubtypeInductionInstance (R : Type*) :=
  SubtypeInductionInstance (X := FinRectUniverse R)
    (SubX := PosFinRectUniverse R) (toX := Subtype.val)

namespace RectSubtypeInductionInstance

variable {R : Type*} (inst : RectSubtypeInductionInstance R)

/-- Convenience API: prove `inst.P` for every `m × n` matrix. -/
theorem prove_for_fin :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) R),
      inst.P ⟨⟨m, n⟩, ⟨A⟩⟩ := by
  intro m n A
  exact (SubtypeInductionInstance.prove inst) ⟨⟨m, n⟩, ⟨A⟩⟩

end RectSubtypeInductionInstance

/-- Square specialization: `X = FinSqUniverse R`, `SubX = PosFinSqUniverse R`. -/
abbrev SquareSubtypeInductionInstance (R : Type*) :=
  SubtypeInductionInstance (X := FinSqUniverse R)
    (SubX := PosFinSqUniverse R) (toX := Subtype.val)

namespace SquareSubtypeInductionInstance

variable {R : Type*} (inst : SquareSubtypeInductionInstance R)

/-- Convenience API: prove `inst.P` for every `n × n` matrix. -/
theorem prove_for_fin :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R),
      inst.P ⟨n, ⟨A⟩⟩ := by
  intro n A
  exact (SubtypeInductionInstance.prove (inst := inst)) ⟨n, ⟨A⟩⟩

end SquareSubtypeInductionInstance

end Specializations

end MatDecompFormal.Framework
