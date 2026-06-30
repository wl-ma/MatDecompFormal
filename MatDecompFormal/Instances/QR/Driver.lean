/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Framework.DecompositionDriver
import MatDecompFormal.Instances.QR.Recursive
import MatDecompFormal.Instances.QR.Strategy
import MatDecompFormal.Instances.QR.Details

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# QR Driver

This file assembles the active QR framework driver from concrete target and
base-case data, using a QR-specific head-tail submatrix strategy core together
with QR-specific proof hooks.
-/

section GenericTarget

variable {R : Type*} [Semiring R]

def QR_P (x : SquareUniverse R) : Prop :=
  HasQR x.A

def QR_P_sub (x_sub : PosSquareUniverse R) : Prop :=
  HasQR x_sub.1.A

@[simp] theorem qr_P_compat (x_sub : PosSquareUniverse R) :
    QR_P_sub x_sub ↔ QR_P (x_sub : SquareUniverse R) :=
  Iff.rfl

/-- Universe-level QR base case used by the generic driver assembler. -/
theorem qr_base_univ (x : SquareUniverse R) :
    ((∀ (x_sub : PosSquareUniverse R), (x_sub : SquareUniverse R) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      QR_P x := by
  intro hx
  exact base_qr_zero_dim_sq
    (squareSubtypeBaseDimEqZero x hx)

end GenericTarget

noncomputable def qr_strategy_core : SquareStrategyCore ℝ :=
  qrHeadTailSubmatrixStrategyCore

noncomputable def qr_strategy_proof : SquareStrategyProofData ℝ QR_P qr_strategy_core where
  transport := by
    intro ι fι dι oι nι A B hBA hP
    rcases hBA with rfl | ⟨t, rfl⟩
    · exact hP
    · exact qr_transport_of_orthogonal_left_of_transpose t.1 A t.2.1 t.2.2 hP
  lift := by
    intro ι fι dι oι nι A hA hP
    exact qrReady_headTailSubmatrixLift A hA hP

noncomputable def qr_strategy_data : SquareStrategyData ℝ QR_P :=
  mkSquareStrategyData qr_strategy_core qr_strategy_proof

/-- Concrete QR framework driver with only the recursive lift step still delegated. -/
noncomputable def qr_framework_inst : SquareSubtypeInductionInstance ℝ :=
  mkSquareSubtypeInductionInstanceFromStrategy
    QR_P
    qr_base_univ
    qr_strategy_data

/-- Type-indexed QR existence theorem routed through the framework driver. -/
theorem exists_qr_decomposition
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) : HasQR A := by
  by_cases h_sub : Subsingleton ι
  · letI := h_sub
    exact base_qr_subsingleton A
  · letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp h_sub
    exact SquareSubtypeInductionInstance.prove_for_matrix
      (inst := qr_framework_inst) A

end MatDecompFormal.Instances
