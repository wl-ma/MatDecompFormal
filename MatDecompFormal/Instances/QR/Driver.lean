import MatDecompFormal.Framework.UniverseDecompositionFin
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Instances.QR.Core

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Components.Properties
open MatDecompFormal.Abstractions

/-!
# QR Driver

This file packages the internal QR core for the unified square subtype
induction driver. It contains cast-compatibility lemmas and subtype-facing
hooks used by the top-level `QR_Instance`.
-/

/-- Zero-dimensional square real matrices have a trivial internal QR decomposition. -/
lemma base_qr_zero_dim
    (A : Matrix (Fin 0) (Fin 0) ℝ) :
    HasQR_fin A := by
  refine ⟨⟨(1 : Matrix (Fin 0) (Fin 0) ℝ), A⟩, ?_, ?_⟩
  · constructor
    · simp [IsOrthogonalMatrix_fin]
    · simpa using
        (isUpperTriangular_of_subsingleton (ι := Fin 0) (R := ℝ) (A := A))
  · dsimp [QR_Schema_fin]
    ext i j
    exact Fin.elim0 i

section CastCompat

/-- `HasQR_fin` is invariant under square casts along a dimension equality. -/
@[simp] lemma HasQR_fin_castSq
    {n n' : ℕ} (h : n = n') (A : Matrix (Fin n) (Fin n) ℝ) :
    HasQR_fin (castSq (R := ℝ) h A) ↔ HasQR_fin A := by
  simpa using
    (squarePred_castSq_iff
      (R := ℝ)
      (Q := fun {n} A => HasQR_fin (n := n) A)
      h A)

/--
`HasQR_fin` is invariant under the `n -> (n - 1) + 1` cast used by the square
universe/subtype driver on positive dimensions.
-/
@[simp] lemma HasQR_fin_castToPredSucc
    {n : ℕ} (hn : n > 0) (A : Matrix (Fin n) (Fin n) ℝ) :
    HasQR_fin (castToPredSucc (R := ℝ) hn A) ↔ HasQR_fin A := by
  simpa using
    (squarePred_castToPredSucc_iff
      (R := ℝ)
      (Q := fun {n} A => HasQR_fin (n := n) A)
      hn A)

end CastCompat

section DriverHooks

/-- QR uses the standard square `Fin` universe when packaged for the driver. -/
abbrev QR_Univ := FinSqUniverse ℝ

/-- Positive-dimensional square QR objects, matching the driver's subtype layer. -/
abbrev QR_PosUniv := PosFinSqUniverse ℝ

/-- Universe-level QR predicate for the square subtype driver. -/
abbrev QR_P (x : QR_Univ) : Prop :=
  squareSubtypeP (R := ℝ) (Q := fun {n} A => HasQR_fin (n := n) A) x

/-- Subtype-level QR predicate for the square subtype driver. -/
abbrev QR_P_sub (x : QR_PosUniv) : Prop :=
  squareSubtypePSub (R := ℝ) (Q := fun {n} A => HasQR_fin (n := n) A) x

/-- The measure used by the QR subtype driver is the matrix dimension. -/
abbrev QR_μ (x : QR_Univ) : Nat :=
  squareSubtypeμ (R := ℝ) x

/-- The universe/subtype QR predicates are definitionally aligned. -/
lemma QR_P_compat (x_sub : QR_PosUniv) :
    QR_P_sub x_sub ↔ QR_P x_sub.val := by
  simp [QR_P, QR_P_sub]

/--
Subtype-level strategy relation for QR.
-/
noncomputable def QR_r_sub : QR_PosUniv → QR_PosUniv → Prop :=
  fun y x =>
    let k : ℕ := x.val.1 - 1
    ∃ hny : y.val.1 = x.val.1,
      let A_y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
        castToPredSucc (R := ℝ) x.property (castSq (R := ℝ) hny y.val.2.A)
      let A_x : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
        castToPredSucc (R := ℝ) x.property x.val.2.A
      A_y = A_x ∨ A_y = QR_HouseholderStep_fin (k := k) A_x

/--
Subtype-level sliceability predicate for QR, obtained by viewing a positive
square matrix in the `(n - 1) + 1` world used by the strategy.
-/
abbrev QR_IsSliceable_sub (x : QR_PosUniv) : Prop :=
  squareSubtypeIsSliceable
    (R := ℝ)
    (Pred := fun k A => (QR_Reduction_fin k).IsSliceable A)
    x

/--
Subtype-level slice operator for QR, returning the recursive `k × k` subproblem
as an object in the square universe.
-/
noncomputable def QR_slice_sub (x : QR_PosUniv) (hx : QR_IsSliceable_sub x) : QR_Univ :=
  squareSubtypeSlice
    (R := ℝ)
    (Pred := fun k A => (QR_Reduction_fin k).IsSliceable A)
    (slice := fun k A hA => (QR_Reduction_fin k).slice A hA)
    x hx

/--
Subtype-friendly QR transport hook.
-/
lemma QR_transport_sub
    {x y : QR_PosUniv}
    (h_r : QR_r_sub y x) (hPy : QR_P_sub y) :
    QR_P_sub x := by
  change HasQR_fin y.val.2.A at hPy
  change HasQR_fin x.val.2.A
  rcases h_r with ⟨hny, h_r'⟩
  rw [← HasQR_fin_castSq hny, ← HasQR_fin_castToPredSucc x.property] at hPy
  by_cases h_id :
      castToPredSucc (R := ℝ) x.property (castSq (R := ℝ) hny y.val.2.A) =
        castToPredSucc (R := ℝ) x.property x.val.2.A
  · simpa [h_id] using hPy
  · have h_step :
        castToPredSucc (R := ℝ) x.property (castSq (R := ℝ) hny y.val.2.A) =
          QR_HouseholderStep_fin (k := x.val.1 - 1)
            (castToPredSucc (R := ℝ) x.property x.val.2.A) := by
      cases h_r' with
      | inl h_eq =>
          contradiction
      | inr h_eq =>
          exact h_eq
    have hPx_cast :=
      transport_qr_fin (k := x.val.1 - 1)
        (castToPredSucc (R := ℝ) x.property x.val.2.A) (by simpa [h_step] using hPy)
    exact (HasQR_fin_castToPredSucc x.property _).1 hPx_cast

/--
Subtype-friendly QR lifting hook.
-/
lemma QR_lift_from_slice_sub
    (x : QR_PosUniv) (hx : QR_IsSliceable_sub x)
    (hSlice : QR_P (QR_slice_sub x hx)) :
    QR_P_sub x := by
  dsimp [QR_P, QR_P_sub, QR_slice_sub] at hSlice ⊢
  exact squareSubtypeLiftFromSlice
    (R := ℝ)
    (Pred := fun k A => (QR_Reduction_fin k).IsSliceable A)
    (slice := fun k A hA => (QR_Reduction_fin k).slice A hA)
    (Q := fun {n} A => HasQR_fin (n := n) A)
    (lift := fun k A hA hSlice => QR_Strategy_lift_from_slice_fin (k := k) (A := A) hA hSlice)
    (cast_iff := fun hn A => HasQR_fin_castToPredSucc hn A)
    x hx hSlice

/--
Subtype-friendly QR reach hook.
-/
noncomputable def QR_reach_sub
    (x_sub : QR_PosUniv) (_hx_pos : QR_μ x_sub.val > 0) :
    Σ' (y_sub : QR_PosUniv), Σ' (hy : QR_IsSliceable_sub y_sub),
      QR_r_sub y_sub x_sub ∧ QR_μ (QR_slice_sub y_sub hy) < QR_μ x_sub.val := by
  let n : ℕ := x_sub.val.1
  let k : ℕ := n - 1
  let A_cast : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := by
    simpa [n, k] using
      (castToPredSucc (R := ℝ) x_sub.property (by simpa [n] using x_sub.val.2.A))

  have hk : (k + 1) = n := by
    simpa [n, k] using (Nat.succ_pred_eq_of_pos x_sub.property)

  by_cases h_ready : QR_ReadyForSlice_fin (k := k) A_cast
  · refine ⟨x_sub, ?_, ?_, ?_⟩
    · dsimp [QR_IsSliceable_sub]
      simpa [n, k, A_cast] using h_ready
    · dsimp [QR_r_sub]
      refine ⟨rfl, ?_⟩
      left
      simp
    · dsimp [QR_μ, QR_slice_sub]
      apply Nat.pred_lt
      simpa [pos_iff_ne_zero] using x_sub.property
  · let B_cast : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
        QR_HouseholderStep_fin (k := k) A_cast
    have hB : (QR_Reduction_fin k).IsSliceable B_cast := by
      simpa [B_cast] using QR_HouseholderStep_sliceable_for_reduction (k := k) A_cast
    let y_mat : Matrix (Fin n) (Fin n) ℝ := castSq (R := ℝ) hk B_cast
    let y_sub : QR_PosUniv := ⟨⟨n, ⟨y_mat⟩⟩, x_sub.property⟩
    refine ⟨y_sub, ?_, ?_, ?_⟩
    · dsimp [QR_IsSliceable_sub]
      convert hB
      dsimp [y_sub, y_mat]
      subst k
      simp
    · dsimp [QR_r_sub]
      refine ⟨rfl, ?_⟩
      right
      subst k
      subst n
      simp [y_sub, y_mat, A_cast, B_cast]
    · dsimp [QR_μ, QR_slice_sub]
      apply Nat.pred_lt
      simpa [pos_iff_ne_zero] using x_sub.property

end DriverHooks

end MatDecompFormal.Instances
