import MatDecompFormal.Instances.PLU.Details

/-!
# PLU decomposition

This file is the PLU instance's main-line assembly file.

Reading from top to bottom shows:

* the internal surface from `Instances.PLU.Details`
  (`PLU_Schema_fin`, `HasPLU_fin`);
* the internal organization from `Instances.PLU.Details`
  (`PLU_Reduction_fin`, `PLU_Transform_fin`, `PLU_Strategy_fin`);
* the framework assembly point (`PLU_Instance`);
* the internal `_fin` theorem exported through the framework;
* the external surface from `Instances.PLU.Details` (`PLU_Schema`, `HasPLU`);
* the final external theorem obtained through the bridge support.

The heavier strategy, lifting, driver-support, and bridge-support details remain
in `Instances.PLU.Details`.
-/

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework

section InternalSurface

/- `PLU_Schema_fin` and `HasPLU_fin` are provided by `Instances.PLU.Details`. -/

end InternalSurface

section InternalOrganization

/- `PLU_Reduction_fin`, `PLU_Transform_fin`, and `PLU_Strategy_fin` are the
key internal organization nodes provided by `Instances.PLU.Details`. -/

end InternalOrganization

section FrameworkAssembly

/- This is the point where the PLU-specific organization is packaged for the
generic square subtype induction framework. -/

/--
PLU packaged for the unified square subtype induction driver on the square
universe.
-/
noncomputable def PLU_Instance (R : Type*) [Field R] [DecidableEq R] :
    SubtypeInductionInstance
      (X := FinSqUniverse R)
      (SubX := PosFinSqUniverse R)
      (toX := Subtype.val) where
  μ := squareSubtypeμ (R := R)
  μ_base := squareSubtypeμBase

  P := squareSubtypeP (R := R) (Q := fun {n} A => HasPLU_fin (R := R) (n := n) A)
  P_sub := squareSubtypePSub (R := R) (Q := fun {n} A => HasPLU_fin (R := R) (n := n) A)
  P_compat := squareSubtypePCompat
    (R := R) (Q := fun {n} A => HasPLU_fin (R := R) (n := n) A)

  r_sub := fun y x =>
    ∃ hny : y.val.1 = x.val.1,
      (PLU_Strategy_fin (R := R) (x.val.1 - 1)).r
        (castToPredSucc (R := R) x.property
          (castSq (R := R) hny (y.val.2.A)))
        (castToPredSucc (R := R) x.property x.val.2.A)

  IsSliceable_sub := squareSubtypeIsSliceable
    (R := R)
    (Pred := fun k A => (PLU_Reduction_fin (R := R) k).IsSliceable A)

  slice_sub := squareSubtypeSlice
    (R := R)
    (Pred := fun k A => (PLU_Reduction_fin (R := R) k).IsSliceable A)
    (slice := fun k A hA => (PLU_Reduction_fin (R := R) k).slice A hA)

  transport_sub := by
    intro x y h_r hPy
    classical
    rcases h_r with ⟨hny, h_r'⟩
    dsimp [squareSubtypePSub] at hPy ⊢
    rw [← HasPLU_fin_castSq hny, ← HasPLU_fin_castToPredSucc x.property] at hPy
    have hPx_cast := transport_plu_fin (k := x.val.1 - 1) h_r' hPy
    exact (HasPLU_fin_castToPredSucc (R := R) x.property _).1 hPx_cast

  lift_from_slice_sub := by
    intro x hx hSlice
    exact squareSubtypeLiftFromSlice
      (R := R)
      (Pred := fun k A => (PLU_Reduction_fin (R := R) k).IsSliceable A)
      (slice := fun k A hA => (PLU_Reduction_fin (R := R) k).slice A hA)
      (Q := fun {n} A => HasPLU_fin (n := n) A)
      (lift := fun k A hA hSlice =>
        lift_from_slice_plu_fin (R := R) (k := k) (A := A) hA hSlice)
      (cast_iff := fun hn A => HasPLU_fin_castToPredSucc (R := R) hn A)
      x hx hSlice

  reach_sub := by
    intro x_sub hx_pos
    classical
    let n : ℕ := x_sub.val.1
    let k : ℕ := n - 1
    let S := PLU_Strategy_fin (R := R) k
    let A_cast : Matrix (Fin (k + 1)) (Fin (k + 1)) R := by
      simpa [n, k] using
        (castToPredSucc (R := R) x_sub.property (by simpa [n] using x_sub.val.2.A))

    by_cases h_goal : S.transform.Goal A_cast
    · refine ⟨x_sub, ?_, ?_, ?_⟩
      · dsimp [ReductionMethod.IsSliceable, n, k]
        have hA_slice : S.reduction.IsSliceable A_cast := by
          simpa [S.goal_is_sliceable] using h_goal
        simpa [A_cast, S, PLU_Strategy_fin] using hA_slice
      · refine ⟨rfl, ?_⟩
        refine Or.inl ?_
        simp
      · dsimp
        apply Nat.pred_lt
        simp [pos_iff_ne_zero] at hx_pos
        simpa using hx_pos

    · let t := S.transform.find A_cast h_goal
      let B_cast := S.transform.apply t A_cast
      have hB_goal : S.transform.Goal B_cast := S.transform.find_spec A_cast h_goal
      have hB_slice : (PLU_Reduction_fin (R := R) k).IsSliceable B_cast := by
        have : S.reduction.IsSliceable B_cast := by
          simpa [S.goal_is_sliceable] using hB_goal
        simpa [S, PLU_Strategy_fin] using this

      have hk : (k + 1) = n := by
        simpa [n, k] using (Nat.succ_pred_eq_of_pos x_sub.property)

      let y_mat : Matrix (Fin n) (Fin n) R := castSq (R := R) hk B_cast
      let y_sub : PosFinSqUniverse R := ⟨⟨n, ⟨y_mat⟩⟩, x_sub.property⟩

      refine ⟨y_sub, ?_, ?_, ?_⟩
      · dsimp
        convert hB_slice
        dsimp [y_sub, y_mat]
        subst k
        simp
      · dsimp
        have hny : y_sub.val.1 = x_sub.val.1 := rfl
        refine ⟨hny, ?_⟩
        refine Or.inr ?_
        use t
        subst k
        subst n
        simp [y_sub, y_mat, B_cast, A_cast, S]
      · dsimp
        apply Nat.pred_lt
        simp [pos_iff_ne_zero] at hx_pos
        simpa using hx_pos

  base_univ := by
    intro x hx
    have hx0 : x.1 = 0 := squareSubtypeBaseDimEqZero (R := R) x hx
    exact base_plu_zero_dim_sq (R := R) (x := x) hx0

/--
Primary PLU existence theorem on the internal `Fin` layer.

At the top level, the framework hand-off is explicit: `PLU_Instance` packages
the PLU strategy for the square subtype induction driver, and the driver
exports the resulting internal `_fin` theorem.
-/
theorem exists_plu_decomposition_fin {n : ℕ} {R : Type*} [Field R] [DecidableEq R]
    (A : Matrix (Fin n) (Fin n) R) : HasPLU_fin A := by
  simpa using
    (SquareSubtypeInductionInstance.prove_for_fin
      (inst := PLU_Instance (R := R)) n A)

end FrameworkAssembly

section ExternalSurface

variable {ι R : Type*} [FinEnum ι] [Field R]

/- `PLU_Schema` and `HasPLU` are provided by `Instances.PLU.Details`. -/

/--
External presentation theorem for PLU.

The top-level assembly is explicit: bridge the external `FinEnum` statement to
the internal `Fin` theorem via `hasPLU_reindex_iff`, then discharge the
internal goal with `exists_plu_decomposition_fin`.
-/
theorem exists_plu_decomposition [DecidableEq R] (A : Matrix ι ι R) : HasPLU A := by
  let e := orderIsoOfFinEnum ι
  rw [hasPLU_reindex_iff e]
  exact exists_plu_decomposition_fin (A.reindex e.toEquiv e.toEquiv)

end ExternalSurface

end MatDecompFormal.Instances
