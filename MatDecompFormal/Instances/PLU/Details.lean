import MatDecompFormal.Framework.UniverseDecompositionFin
import Mathlib.Data.Sum.Order
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Abstractions.Strategy
import MatDecompFormal.Abstractions.ReductionCombinators
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Components.Properties.Reindex
import MatDecompFormal.Components.Reductions.Schur
import MatDecompFormal.Components.Reductions.ZeroColumn
import MatDecompFormal.Components.Transformations.Elementary.Pivot
import MatDecompFormal.Components.BlockLifting

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Components.Transformations.Elementary
open MatDecompFormal.Components

/-!
# PLU Details

This file contains the non-assembly PLU implementation details used by the
top-level `Instances.PLU` main-line file:

* the internal `Fin` schema and existence wrapper;
* the reduction / transform / strategy support;
* lifting, transport, cast, and reach glue for the square subtype driver;
* the external `FinEnum` bridge support.
-/

section Schema

variable {n : ℕ} {R : Type*} [Field R] [DecidableEq R]

/-- Internal canonical PLU schema on square `Fin n` matrices. -/
def PLU_Schema_fin (n : ℕ) : DecompositionSchema n n R where
  Factors := Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R
  property := fun (P, L, U) =>
    IsPermutation P ∧ IsUnitLowerTriangular L ∧ IsUpperTriangular U
  equation := fun A (P, L, U) => P * A = L * U

/-- Internal canonical PLU existence proposition. -/
def HasPLU_fin (A : Matrix (Fin n) (Fin n) R) : Prop :=
  HasDecomposition (PLU_Schema_fin n) A

end Schema

/-- Helper to cast a rectangular matrix to a square one when dimensions are equal. -/
private def castSquare {m n : ℕ} {R : Type*} (A : Matrix (Fin m) (Fin n) R)
    (h : m = n) : Matrix (Fin n) (Fin n) R := by
  cases h
  simpa using A

noncomputable section FinImpl

variable {R : Type*} [Field R]

/-- Combined reduction method used by the strategy: Schur with a zero-column fallback. -/
noncomputable def PLU_Reduction_fin (k : ℕ) : ReductionMethod (k + 1) (k + 1) k k R :=
  ReductionMethod.try_else (SchurMethod k R) (ZeroColumnMethod k k R)

/-- A transformation tailored to the above reduction method. -/
noncomputable def PLU_Transform_fin (k : ℕ) :
    Transformation (Matrix (Fin (k + 1)) (Fin (k + 1)) R) :=
  let reduc := PLU_Reduction_fin (R := R) k
  {
    T := Fin (k + 1)
    Goal := reduc.IsSliceable
    decGoal := by
      classical
      exact Classical.decPred _
    apply := fun i A => (swap R 0 i) * A
    find := fun A h_not =>
      by
        classical
        dsimp [reduc, PLU_Reduction_fin, ReductionMethod.try_else] at h_not
        have h_not_zeroCol : ¬ (ZeroColumnMethod k k R).IsSliceable A :=
          (not_or.mp h_not).2
        dsimp [ZeroColumnMethod] at h_not_zeroCol
        let h_exists : ∃ i, A i 0 ≠ 0 := not_forall.mp h_not_zeroCol
        exact Classical.choose h_exists
    find_spec := by
      intro A h_not
      classical
      dsimp [reduc, PLU_Reduction_fin, ReductionMethod.try_else] at h_not
      have h_not_schur : ¬ (SchurMethod k R).IsSliceable A :=
        (not_or.mp h_not).1
      have h_not_zeroCol : ¬ (ZeroColumnMethod k k R).IsSliceable A :=
        (not_or.mp h_not).2
      dsimp [ZeroColumnMethod] at h_not_zeroCol
      let h_exists : ∃ i, A i 0 ≠ 0 := not_forall.mp h_not_zeroCol
      let i := Classical.choose h_exists
      have hi : A i 0 ≠ 0 := Classical.choose_spec h_exists
      dsimp [reduc, PLU_Reduction_fin, ReductionMethod.try_else, SchurMethod, ZeroColumnMethod]
      refine Or.inl ?_
      have : (swap R 0 i * A) 0 0 = A i 0 := by
        simp [swap_mul_apply_left]
      have h_unit : IsUnit (A i 0) := isUnit_iff_ne_zero.mpr hi
      simpa [this] using h_unit
  }

/-- Complete reduction strategy on `(k+1)×(k+1)` matrices. -/
noncomputable def PLU_Strategy_fin (k : ℕ) :
    ReductionStrategy (k + 1) (k + 1) k k R where
  transform := (PLU_Transform_fin (R := R) k)
  reduction := (PLU_Reduction_fin (R := R) k)
  goal_is_sliceable := rfl
  μ := fun _A => k + 1
  μ_slice := fun _A => k
  μ_mono := by intro A t; simp
  slice_progress := by intro A hA; simp

/-- Transport lemma: the PLU property is invariant under the strategy relation. -/
lemma transport_plu_fin {k : ℕ}
    {A B : Matrix (Fin (k + 1)) (Fin (k + 1)) R}
    (hr : (PLU_Strategy_fin (R := R) k).r B A) (hB : HasPLU_fin B) :
    HasPLU_fin A := by
  classical
  rcases hr with rfl | ⟨t, rfl⟩
  · exact hB
  · rcases hB with ⟨⟨P, L, U⟩, ⟨hP, hL, hU⟩, hEq⟩
    let t' : Fin (k + 1) := t
    have hP' : IsPermutation (P * swap R 0 t') :=
      isPermutation_mul hP (isPermutation_swap 0 t')
    refine ⟨⟨P * swap R 0 t', L, U⟩, ⟨hP', hL, hU⟩, ?_⟩
    dsimp [PLU_Schema_fin]
    simpa [mul_assoc] using hEq

private lemma lift_from_slice_schur_case {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (h_pivot_unit : IsUnit (A 0 0))
    (h_slice : HasPLU_fin ((SchurMethod k R).slice A h_pivot_unit)) :
    HasPLU_fin A := by
  classical
  rcases h_slice with ⟨⟨P', L', U'⟩, ⟨hP', hL', hU'⟩, h_slice_eq⟩
  rcases
      lift_permutation_unitLower_upper_schur
        (R := R) (k := k)
        (A := A) (h_pivot_unit := h_pivot_unit)
        (subP := P') (subL := L') (subU := U')
        hP' hL' hU' h_slice_eq with
    ⟨⟨P, L, U⟩, ⟨hP, hL, hU, h_eq⟩⟩
  exact
    ⟨⟨P, L, U⟩,
      ⟨hP, hL, hU⟩,
      by simpa [PLU_Schema_fin] using h_eq⟩

private lemma lift_from_slice_zero_col_case {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (h_zero_col : ∀ i, A i 0 = 0)
    (h_slice : HasPLU_fin ((ZeroColumnMethod k k R).slice A h_zero_col)) :
    HasPLU_fin A := by
  classical
  rcases h_slice with ⟨⟨P', L', U'⟩, ⟨hP', hL', hU'⟩, h_slice_eq⟩
  rcases
      lift_permutation_unitLower_upper_zero_col
        (R := R) (k := k)
        (A := A) (h_zero_col := h_zero_col)
        (subP := P') (subL := L') (subU := U')
        hP' hL' hU' h_slice_eq with
    ⟨⟨P, L, U⟩, ⟨hP, hL, hU, h_eq⟩⟩
  exact
    ⟨⟨P, L, U⟩,
      ⟨hP, hL, hU⟩,
      by simpa [PLU_Schema_fin] using h_eq⟩

/-- Lifting lemma: build a PLU decomposition of `A` from a slice. -/
lemma lift_from_slice_plu_fin {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (hA : (PLU_Reduction_fin (R := R) k).IsSliceable A)
    (h_slice : HasPLU_fin ((PLU_Reduction_fin (R := R) k).slice A hA)) :
    HasPLU_fin A := by
  by_cases h_schur : IsUnit (A 0 0)
  · cases hA with
    | inl hA_schur =>
        have h_slice' : HasPLU_fin ((SchurMethod k R).slice A hA_schur) := by
          simpa [PLU_Reduction_fin, ReductionMethod.try_else, hA_schur] using h_slice
        have h_eq : hA_schur = h_schur := Subsingleton.elim _ _
        have h_slice'' : HasPLU_fin ((SchurMethod k R).slice A h_schur) := by
          simpa [h_eq] using h_slice'
        exact lift_from_slice_schur_case A h_schur h_slice''
    | inr h_zero_col =>
        have : False := (isUnit_iff_ne_zero.mp h_schur) (h_zero_col 0)
        contradiction
  · cases hA with
    | inl h_unit =>
        have : False := h_schur h_unit
        contradiction
    | inr h_zero_col =>
        have h_slice' : HasPLU_fin ((ZeroColumnMethod k k R).slice A h_zero_col) := by
          simp [PLU_Reduction_fin, ReductionMethod.try_else] at h_slice
          split_ifs at h_slice with h_case
          · contradiction
          · exact h_slice
        exact lift_from_slice_zero_col_case A h_zero_col h_slice'

/-- Reach witness for PLU on `(k+1)×(k+1)` (NOT a Prop, so it is a `def`). -/
noncomputable def reach_plu_fin {k : ℕ} (μ_base : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (hμ : (PLU_Strategy_fin (R := R) k).μ A > μ_base) :
    Σ' (B : Matrix (Fin (k + 1)) (Fin (k + 1)) R),
      Σ' (hB : (PLU_Reduction_fin (R := R) k).IsSliceable B),
        (PLU_Strategy_fin (R := R) k).r B A ∧
          (PLU_Strategy_fin (R := R) k).μ_slice
            ((PLU_Reduction_fin (R := R) k).slice B hB) <
              (PLU_Strategy_fin (R := R) k).μ A := by
  simpa using
    (ReductionStrategy.mk_reach
      (S := (PLU_Strategy_fin (R := R) k))
      (μ_base := μ_base)
      (A := A)
      (by exact ⟨Nat.succ_pos _, Nat.succ_pos _⟩)
      hμ)

/-- Base case (Square universe): zero-dimensional square matrices admit a trivial PLU. -/
lemma base_plu_zero_dim_sq {R : Type*} [Field R] [DecidableEq R]
    {x : FinSqUniverse R} (h_zero : x.1 = 0) :
    HasPLU_fin (R := R) x.2.A := by
  classical
  rcases x with ⟨n, A⟩
  cases h_zero
  have h_triv : HasPLU_fin (R := R) A.A := by
    refine ⟨⟨(1 : Matrix (Fin 0) (Fin 0) R),
              (1 : Matrix (Fin 0) (Fin 0) R),
              (A.A : Matrix (Fin 0) (Fin 0) R)⟩, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · dsimp [IsPermutation]
        refine ⟨Equiv.refl (Fin 0), ?_⟩
        ext i j
        exact (Fin.elim0 i)
      · simpa using (isUnitLowerTriangular_one (ι := Fin 0) (R := R))
      · simpa using
          (isUpperTriangular_of_subsingleton (ι := Fin 0) (R := R)
            (A := (A.A : Matrix (Fin 0) (Fin 0) R)))
    · dsimp [PLU_Schema_fin]
  simpa using h_triv

end FinImpl

@[simp] lemma HasPLU_fin_castSq {R : Type*} [Field R] [DecidableEq R]
    {n n' : ℕ} (h : n = n') (A : Matrix (Fin n) (Fin n) R) :
    HasPLU_fin (castSq (R := R) h A) ↔ HasPLU_fin A := by
  simpa using
    (squarePred_castSq_iff
      (R := R)
      (Q := fun {n} A => HasPLU_fin (n := n) A)
      h A)

@[simp] lemma HasPLU_fin_castToPredSucc {R : Type*} [Field R] [DecidableEq R]
    {n : ℕ} (hn : n > 0) (A : Matrix (Fin n) (Fin n) R) :
    HasPLU_fin (castToPredSucc (R := R) hn A) ↔ HasPLU_fin A := by
  simpa using
    (squarePred_castToPredSucc_iff
      (R := R)
      (Q := fun {n} A => HasPLU_fin (n := n) A)
      hn A)

section FinEnum

variable {ι R : Type*} [FinEnum ι] [Field R]

/-- External presentation schema for PLU on `FinEnum`-indexed square matrices. -/
def PLU_Schema : DecompositionSchema' ι ι R where
  Factors := Matrix ι ι R × Matrix ι ι R × Matrix ι ι R
  property := fun (P, L, U) =>
    IsPermutation P ∧ IsUnitLowerTriangular L ∧ IsUpperTriangular U
  equation := fun A (P, L, U) => P * A = L * U

/-- External semantic wrapper for PLU existence. -/
def HasPLU (A : Matrix ι ι R) : Prop :=
  HasDecomposition' (PLU_Schema (R := R)) A

/--
Bridge lemma: `HasPLU` is invariant under reindexing by an order-preserving
equivalence `e : ι ≃o Fin n`.
-/
lemma hasPLU_reindex_iff (e : ι ≃o Fin (FinEnum.card ι)) (A : Matrix ι ι R) :
    HasPLU A ↔ HasPLU_fin (A.reindex e.toEquiv e.toEquiv) := by
  constructor
  · rintro ⟨⟨P, L, U⟩, ⟨hP, hL, hU⟩, hEq⟩
    let P' := P.reindex e.toEquiv e.toEquiv
    let L' := L.reindex e.toEquiv e.toEquiv
    let U' := U.reindex e.toEquiv e.toEquiv
    refine ⟨⟨P', L', U'⟩, ?_, ?_⟩
    · refine ⟨(isPermutation_reindex e.toEquiv P).1 hP, ?_, ?_⟩
      · have h_mono : StrictMono e.toEquiv := e.strictMono
        exact (isUnitLowerTriangular_reindex e.toEquiv h_mono L).1 hL
      · have h_mono : StrictMono e.toEquiv := e.strictMono
        exact (isUpperTriangular_reindex e.toEquiv h_mono U).1 hU
    · dsimp [PLU_Schema]
      have h := congrArg (Matrix.reindex e.toEquiv e.toEquiv) hEq
      simp [PLU_Schema_fin, P', L', U']
      rw [← submatrix_mul, ← submatrix_mul]
      · simpa [submatrix_mul_equiv] using h
      all_goals exact e.toEquiv.symm.bijective
  · rintro ⟨⟨P', L', U'⟩, ⟨hP', hL', hU'⟩, hEq⟩
    let P := P'.reindex e.symm.toEquiv e.symm.toEquiv
    let L := L'.reindex e.symm.toEquiv e.symm.toEquiv
    let U := U'.reindex e.symm.toEquiv e.symm.toEquiv
    refine ⟨⟨P, L, U⟩, ?_, ?_⟩
    · refine ⟨(isPermutation_reindex e.symm.toEquiv P').1 hP', ?_, ?_⟩
      · have h_mono : StrictMono e.symm.toEquiv := e.symm.strictMono
        exact (isUnitLowerTriangular_reindex e.symm.toEquiv h_mono L').1 hL'
      · have h_mono : StrictMono e.symm.toEquiv := e.symm.strictMono
        exact (isUpperTriangular_reindex e.symm.toEquiv h_mono U').1 hU'
    · dsimp [PLU_Schema]
      simp [P, L, U]
      dsimp [PLU_Schema_fin] at hEq
      ext i j
      have hentry := congrArg (fun M => M (e i) (e j)) hEq
      have hleft :
          (P'.submatrix (fun x : ι => e x) (fun x : ι => e x) * A) i j
            =
          (P' * A.submatrix (fun x : Fin (FinEnum.card ι) => e.symm x)
                            (fun x : Fin (FinEnum.card ι) => e.symm x)) (e i) (e j) := by
        classical
        simp [Matrix.mul_apply, Matrix.submatrix]
        refine (Fintype.sum_equiv (e.toEquiv)
          (fun k : ι => P' (e i) (e k) * A k j)
          (g := fun x : Fin (FinEnum.card ι) => P' (e i) x * A (e.symm x) j) ?_)
        intro x
        simp
      have hright :
          (L'.submatrix (fun x : ι => e x) (fun x : ι => e x) *
              U'.submatrix (fun x : ι => e x) (fun x : ι => e x)) i j
            =
          (L' * U') (e i) (e j) := by
        classical
        simp [Matrix.mul_apply, Matrix.submatrix]
        refine (Fintype.sum_equiv (e.toEquiv)
          (fun k : ι => L' (e i) (e k) * U' (e k) (e j))
          (g := fun x : Fin (FinEnum.card ι) => L' (e i) x * U' x (e j)) ?_)
        intro x
        rfl
      calc
        (P'.submatrix (fun x : ι => e x) (fun x : ι => e x) * A) i j
            =
          (P' * A.submatrix (fun x : Fin (FinEnum.card ι) => e.symm x)
                            (fun x : Fin (FinEnum.card ι) => e.symm x)) (e i) (e j) := hleft
        _ = (L' * U') (e i) (e j) := by simpa using hentry
        _ =
          (L'.submatrix (fun x : ι => e x) (fun x : ι => e x) *
              U'.submatrix (fun x : ι => e x) (fun x : ι => e x)) i j := by
            simpa using hright.symm

end FinEnum

end MatDecompFormal.Instances
