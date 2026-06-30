/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Instances.PLU.Strategy
import MatDecompFormal.Instances.PLU.Direct
import MatDecompFormal.Instances.PLU.Details

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Components.Properties

/-!
# PLU Driver

This file assembles the active PLU framework driver from concrete target and
base-case data, while still isolating the hard recursive strategy core and its
proof hooks in the final direct lifting theorem.
-/

section GenericTarget

variable {R : Type*} [Semiring R]

/-- Universe-level PLU target predicate. -/
def PLU_P (x : SquareUniverse R) : Prop :=
  HasPLU x.A

/-- Positive-universe PLU target predicate. -/
def PLU_P_sub (x_sub : PosSquareUniverse R) : Prop :=
  HasPLU x_sub.1.A

@[simp] theorem plu_P_compat (x_sub : PosSquareUniverse R) :
    PLU_P_sub x_sub ↔ PLU_P (x_sub : SquareUniverse R) :=
  Iff.rfl

/-- Universe-level PLU base case used by the generic driver assembler. -/
theorem plu_base_univ (x : SquareUniverse R) :
    ((∀ (x_sub : PosSquareUniverse R), (x_sub : SquareUniverse R) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      PLU_P x := by
  intro hx
  exact base_plu_zero_dim_sq
    (squareSubtypeBaseDimEqZero x hx)

end GenericTarget

section Driver

variable {R : Type*} [DivisionRing R]

/-- Current PLU strategy core built from head-tail pivoting and reduction. -/
noncomputable def plu_strategy_core : SquareStrategyCore R :=
  pluHeadTailSubmatrixStrategyCore

end Driver

section TransportHelpers

variable {R : Type*} [Semiring R]

/-- Pull a PLU decomposition back across a single left row-swap. -/
theorem hasPLU_of_left_swap
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (i : ι) {A : Matrix ι ι R} :
    HasPLU ((Matrix.swap R (headElem (α := ι)) i) * A) → HasPLU A := by
  intro hB
  rcases hB with ⟨⟨P, L, U⟩, h_prop, h_eq⟩
  refine ⟨(P * Matrix.swap R (headElem (α := ι)) i, L, U), ?_, ?_⟩
  · rcases h_prop with ⟨hP, hL, hU⟩
    refine ⟨?_, hL, hU⟩
    exact isPermutation_mul hP (isPermutation_swap (headElem (α := ι)) i)
  · calc
      ((P * Matrix.swap R (headElem (α := ι)) i) * A)
          = P * ((Matrix.swap R (headElem (α := ι)) i) * A) := by
              rw [Matrix.mul_assoc]
      _ = L * U := h_eq

end TransportHelpers

section Driver

variable {R : Type*} [DivisionRing R]

/-- Proof-side PLU hooks for the current head-tail strategy core. -/
noncomputable def plu_strategy_proof :
    SquareStrategyProofData R PLU_P plu_strategy_core where
  transport := by
    intro ι fι dι oι nι A B hBA hP
    change HasPLU B at hP
    change HasPLU A
    change (B = A) ∨ ∃ t : ι, B = Matrix.swap R (headElem (α := ι)) t * A at hBA
    rcases hBA with rfl | ⟨t, rfl⟩
    · exact hP
    · exact hasPLU_of_left_swap (i := t) hP
  lift := by
    intro ι fι dι oι nι A hA hP
    exact pluHeadTailSubmatrixLift fι dι oι nι A hA hP

/-- Assembled PLU strategy data for the current head-tail core. -/
noncomputable def plu_strategy_data : SquareStrategyData R PLU_P :=
  mkSquareStrategyData
    plu_strategy_core
    plu_strategy_proof


end Driver

end MatDecompFormal.Instances
