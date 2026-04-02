import MatDecompFormal.Instances.QR.Core
import MatDecompFormal.Instances.QR.Driver
import MatDecompFormal.Instances.QR.Bridge

/-!
# QR decomposition

This file is the QR instance's readable main-line assembly.

Reading from top to bottom shows:

* the internal surface from `Instances.QR.Core`
  (`QR_Schema_fin`, `HasQR_fin`);
* key internal organization nodes (`QR_Strategy_step_then_reduce`,
  `QR_Strategy_close_step_fin`);
* the framework assembly point (`QR_Instance`);
* the internal `_fin` theorem exported through the framework;
* the external surface from `Instances.QR.Bridge` (`QR_Schema`, `HasQR`);
* the final external theorem obtained through the bridge.

The heavy technical proofs remain in the support modules:

* `Instances.QR.Core` for the internal mathematical machinery;
* `Instances.QR.Driver` for the driver support behind `QR_Instance`;
* `Instances.QR.Bridge` for the `FinEnum` bridge support.
-/

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework

section InternalSurface

/- `QR_Schema_fin` and `HasQR_fin` are provided by `Instances.QR.Core`. -/

end InternalSurface

section InternalOrganization

/--
Strategy-level formulation of the QR main chain:
if the matrix is not ready, the unique Householder transform makes it ready;
once ready, the reduction and lifting interfaces are already aligned.
-/
lemma QR_Strategy_step_then_reduce {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (h_not : ¬ (QR_Strategy_fin k).transform.Goal A) :
    let B := (QR_Strategy_fin k).transform.apply ((QR_Strategy_fin k).transform.find A h_not) A
    (QR_Strategy_fin k).reduction.IsSliceable B ∧
      (QR_Strategy_fin k).μ_slice
        ((QR_Strategy_fin k).reduction.slice B
          ((QR_Strategy_fin k).transform.find_spec A h_not)) <
        (QR_Strategy_fin k).μ A := by
  dsimp [QR_Strategy_fin, QR_Transform_fin]
  constructor
  · exact QR_HouseholderStep_sliceable_for_reduction (k := k) A
  · simp

/--
This is the complete QR strategy loop at the internal `Fin` layer:
transform to the ready-for-slice state, solve the transformed matrix by
reduction plus lifting, then transport that QR decomposition back.
-/
lemma QR_Strategy_close_step_fin {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (h_slice : HasQR_fin (QR_HouseholderStepSlice_fin (k := k) A)) :
    HasQR_fin A := by
  have h_step :
      HasQR_fin (QR_HouseholderStep_fin (k := k) A) := by
    exact lift_from_slice_qr_fin (k := k)
      (QR_HouseholderStep_fin (k := k) A)
      (QR_HouseholderStep_ready_for_slice (k := k) A) h_slice
  exact transport_qr_fin (k := k) A h_step

end InternalOrganization

section FrameworkAssembly

/- This is the point where the QR-specific organization is packaged for the
generic square subtype induction framework. -/

/--
QR packaged for the unified square subtype induction driver.
-/
noncomputable def QR_Instance : SquareSubtypeInductionInstance ℝ where
  μ := QR_μ
  μ_base := squareSubtypeμBase
  P := QR_P
  P_sub := QR_P_sub
  P_compat := QR_P_compat
  r_sub := QR_r_sub
  IsSliceable_sub := QR_IsSliceable_sub
  slice_sub := QR_slice_sub
  transport_sub := by
    intro x y h_r hPy
    exact QR_transport_sub h_r hPy
  lift_from_slice_sub := by
    intro x hx hSlice
    exact QR_lift_from_slice_sub x hx hSlice
  reach_sub := by
    intro x_sub hx_pos
    exact QR_reach_sub x_sub hx_pos
  base_univ := by
    intro x hx
    have hx0 : x.1 = 0 := squareSubtypeBaseDimEqZero (R := ℝ) x hx
    cases x with
    | mk n fam =>
        cases hx0
        simpa using base_qr_zero_dim fam.A

/--
Primary QR existence theorem on the internal `Fin` layer.

At the top level, the framework hand-off is explicit: `QR_Instance` packages the
QR strategy for the square subtype induction driver, and the driver exports the
resulting `_fin` theorem.
-/
theorem exists_qr_decomposition_fin {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : HasQR_fin A := by
  simpa using
    (SquareSubtypeInductionInstance.prove_for_fin
      (inst := QR_Instance) n A)

end FrameworkAssembly

section ExternalSurface

variable {ι : Type*} [FinEnum ι]

/- `QR_Schema` and `HasQR` are provided by `Instances.QR.Bridge`. -/

/--
External presentation theorem for QR.

The top-level assembly is explicit: bridge the external `FinEnum` statement to
the internal `Fin` theorem via `hasQR_reindex_iff`, then discharge the internal
goal with `exists_qr_decomposition_fin`.
-/
theorem exists_qr_decomposition (A : Matrix ι ι ℝ) : HasQR A := by
  let e := orderIsoOfFinEnum ι
  rw [hasQR_reindex_iff e]
  exact exists_qr_decomposition_fin (A.reindex e.toEquiv e.toEquiv)

end ExternalSurface

end MatDecompFormal.Instances
