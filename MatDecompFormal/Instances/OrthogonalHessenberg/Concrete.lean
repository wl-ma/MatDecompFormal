/-
Copyright (c) 2026 Zichen Wang, Wanli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma
-/
import MatDecompFormal.Instances.OrthogonalHessenberg.Existence
import MatDecompFormal.Instances.Normal.Strategy

universe u

namespace MatDecompFormal.Instances

open Matrix
open InnerProductSpace
open MatDecompFormal.Framework

/-!
# Concrete Unitary Hessenberg Step

This file discharges the unitary boundary-column step oracle nonconstructively:
extend the normalized active boundary column to an orthonormal basis and use the
associated unitary change-of-basis matrix.  This supplies the concrete oracle
needed by the descent theorem in `Existence.lean`.
-/

/-- Boundary column as a vector in complex Euclidean space. -/
noncomputable def boundaryColumnVec
    {ι : Type u} [Fintype ι] (c : Matrix ι Unit ℂ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => c i ())

lemma boundaryColumnVec_ne_zero
    {ι : Type u} [Fintype ι] {c : Matrix ι Unit ℂ} (hc : c ≠ 0) :
    boundaryColumnVec c ≠ 0 := by
  intro hvec
  apply hc
  have hfun : (fun i => c i ()) = 0 := (WithLp.toLp_eq_zero 2).mp hvec
  ext i j
  cases j
  exact congrFun hfun i

/-- Normalized nonzero boundary column. -/
noncomputable def normalizedBoundaryColumn
    {ι : Type u} [Fintype ι] (c : Matrix ι Unit ℂ) (_hc : c ≠ 0) :
    EuclideanSpace ℂ ι :=
  ((‖boundaryColumnVec c‖ : ℂ)⁻¹) • boundaryColumnVec c

lemma normalizedBoundaryColumn_norm
    {ι : Type u} [Fintype ι] (c : Matrix ι Unit ℂ) (hc : c ≠ 0) :
    ‖normalizedBoundaryColumn c hc‖ = 1 := by
  simpa [normalizedBoundaryColumn] using
    (norm_smul_inv_norm (boundaryColumnVec_ne_zero hc))

lemma orthonormal_singleton_head_const
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    Orthonormal ℂ
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
An orthonormal basis whose head vector is the normalized active boundary
column, with the standard basis used in the zero-column case.
-/
noncomputable def boundaryColumnBasis
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (c : Matrix ι Unit ℂ) :
    OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι) := by
  classical
  by_cases hc : c = 0
  · exact EuclideanSpace.basisFun ι ℂ
  · exact Classical.choose
      (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℂ) (E := EuclideanSpace ℂ ι) (ι := ι)
        (card_ι := by simp)
        (s := {headElem (α := ι)})
        (v := fun _ : ι => normalizedBoundaryColumn c hc)
        (orthonormal_singleton_head_const
          (normalizedBoundaryColumn c hc)
          (normalizedBoundaryColumn_norm c hc)))

lemma boundaryColumnBasis_head
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (c : Matrix ι Unit ℂ) (hc : c ≠ 0) :
    boundaryColumnBasis c (headElem (α := ι)) =
      normalizedBoundaryColumn c hc := by
  classical
  unfold boundaryColumnBasis
  simp [hc]
  simpa using
    Classical.choose_spec
      (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℂ) (E := EuclideanSpace ℂ ι) (ι := ι)
        (card_ι := by simp)
        (s := {headElem (α := ι)})
        (v := fun _ : ι => normalizedBoundaryColumn c hc)
        (orthonormal_singleton_head_const
          (normalizedBoundaryColumn c hc)
          (normalizedBoundaryColumn_norm c hc)))
      (headElem (α := ι)) (by simp)

/-- Concrete unitary factor that clears the active boundary column. -/
noncomputable def unitaryBoundaryStepQ
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    Matrix x_sub.1.ι x_sub.1.ι ℂ := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact matrixOfOrthonormalBasis (boundaryColumnBasis x_sub.1.c)

lemma unitaryBoundaryStepQ_unitary
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    IsUnitaryMatrix (unitaryBoundaryStepQ x_sub) := by
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  exact matrixOfOrthonormalBasis_unitary (boundaryColumnBasis x_sub.1.c)

lemma unitaryBoundaryStepQ_ready
    (x_sub : PosHessenbergBoundaryUniverse.{u} ℂ) :
    HessenbergBoundaryReady
      (unitaryHessenbergBoundarySimilarityObject
        (x_sub : HessenbergBoundaryUniverse.{u} ℂ)
        (unitaryBoundaryStepQ x_sub)) := by
  classical
  letI : Nonempty x_sub.1.ι := posHessenbergBoundaryUniverse_nonempty x_sub
  intro _hne i hi
  by_cases hc : x_sub.1.c = 0
  · simp [unitaryHessenbergBoundarySimilarityObject, hc]
  · let b : OrthonormalBasis x_sub.1.ι ℂ (EuclideanSpace ℂ x_sub.1.ι) :=
      boundaryColumnBasis x_sub.1.c
    let Q : Matrix x_sub.1.ι x_sub.1.ι ℂ := matrixOfOrthonormalBasis b
    let v : EuclideanSpace ℂ x_sub.1.ι := boundaryColumnVec x_sub.1.c
    have hbhead : b (headElem (α := x_sub.1.ι)) =
        normalizedBoundaryColumn x_sub.1.c hc := by
      simpa [b] using boundaryColumnBasis_head x_sub.1.c hc
    have hneNorm : ‖v‖ ≠ 0 := by
      simpa [v] using boundaryColumnVec_ne_zero hc
    have hvec : v = (‖v‖ : ℂ) • b (headElem (α := x_sub.1.ι)) := by
      calc
        v = (‖v‖ : ℂ) • (((‖v‖ : ℂ)⁻¹) • v) := by
          rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hneNorm), one_smul]
      _ = (‖v‖ : ℂ) • b (headElem (α := x_sub.1.ι)) := by
          rw [hbhead]
          simp [normalizedBoundaryColumn, v]
    have hvec_ofLp :
        v.ofLp = (‖v‖ : ℂ) • (b (headElem (α := x_sub.1.ι))).ofLp := by
      exact congrArg WithLp.ofLp hvec
    have hmul :
        Qᴴ *ᵥ v.ofLp =
          (‖v‖ : ℂ) •
            (Pi.single (headElem (α := x_sub.1.ι)) (1 : ℂ) :
              x_sub.1.ι → ℂ) := by
      calc
        Qᴴ *ᵥ v.ofLp =
            Qᴴ *ᵥ ((‖v‖ : ℂ) • (b (headElem (α := x_sub.1.ι))).ofLp) := by
              rw [hvec_ofLp]
        _ = (‖v‖ : ℂ) •
            (Qᴴ *ᵥ (b (headElem (α := x_sub.1.ι))).ofLp) := by
              rw [mulVec_smul]
        _ = (‖v‖ : ℂ) •
            (Pi.single (headElem (α := x_sub.1.ι)) (1 : ℂ) :
              x_sub.1.ι → ℂ) := by
              simpa [Q] using
                congrArg ((‖v‖ : ℂ) • ·)
                  (conjTranspose_matrixOfOrthonormalBasis_mulVec b
                    (headElem (α := x_sub.1.ι)))
    have hentry := congrFun hmul i
    have hzero :
        (Qᴴ *ᵥ v.ofLp) i = 0 := by
      simpa [hi] using hentry
    simpa [unitaryHessenbergBoundarySimilarityObject, unitaryBoundaryStepQ, Q, v,
      boundaryColumnVec, Matrix.mulVec, Matrix.mul_apply] using hzero

/-- Concrete nonconstructive unitary boundary oracle. -/
noncomputable def unitaryHessenbergBoundaryStepOracle :
    UnitaryHessenbergBoundaryStepOracle.{u} where
  Q := unitaryBoundaryStepQ
  unitary_Q := unitaryBoundaryStepQ_unitary
  ready := unitaryBoundaryStepQ_ready

/-- Unconditional unitary Hessenberg reduction over `ℂ`. -/
theorem exists_unitary_hessenberg_reduction_complex
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasUnitaryHessenberg A :=
  exists_unitary_hessenberg_reduction unitaryHessenbergBoundaryStepOracle A

/--
Complex unitary Hessenberg reduction with a route-tagged final witness trace.

This exposes the final Hessenberg witness and route tag, not a recursive
boundary-step execution trace.
-/
theorem exists_unitary_hessenberg_reduction_complex_with_witness_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    UnitaryHessenbergTrace "orthonormal-basis-boundary" A :=
  witnessData_of_hasUnitaryHessenberg
    "orthonormal-basis-boundary"
    (exists_unitary_hessenberg_reduction_complex A)

/--
Compatibility name for the route-tagged final witness trace.
Prefer `exists_unitary_hessenberg_reduction_complex_with_witness_trace`.
-/
theorem exists_unitary_hessenberg_reduction_complex_with_trace
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    UnitaryHessenbergTrace "orthonormal-basis-boundary" A :=
  exists_unitary_hessenberg_reduction_complex_with_witness_trace A

end MatDecompFormal.Instances
