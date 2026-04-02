import MatDecompFormal.Components.Lifting.LowLevel
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Reindex
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Components.Reductions.Schur
import MatDecompFormal.Components.Reductions.ZeroColumn

namespace MatDecompFormal.Components

open Matrix
open MatDecompFormal.Framework
open MatDecompFormal.Components.Properties

/-!
# Generic Lifting Core

This file contains the reusable middle-layer lifting cores. It depends on the
block algebra and low-level transport tools, but does not package any
instance-oriented wrapper.
-/

section GenericLifting

variable {k : ℕ} {R : Type*} [Field R]

/--
Bundle the lifted factors together with the proofs that they satisfy their
respective predicates.
-/
structure LiftedThreeFactors
    (PropF₁ : ∀ {ι : Type}, Matrix ι ι R → Prop)
    (PropF₂ PropF₃ : ∀ {ι : Type} [LinearOrder ι], Matrix ι ι R → Prop) where
  (F₁ F₂ F₃ : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
  (hF₁ : PropF₁ F₁)
  (hF₂ : PropF₂ F₂)
  (hF₃ : PropF₃ F₃)

/-- `IsPermutation` does not depend on the chosen `DecidableEq` instance. -/
lemma isPermutation_decEq_irrel {ι : Type*}
    (d₁ d₂ : DecidableEq ι) (A : Matrix ι ι R) :
    @IsPermutation ι R _ d₁ A ↔ @IsPermutation ι R _ d₂ A := by
  unfold IsPermutation
  constructor <;> rintro ⟨σ, hσ⟩ <;> refine ⟨σ, ?_⟩
  · ext i j
    have hentry := congrArg (fun M => M i j) hσ
    simpa [PEquiv.toMatrix_apply] using hentry
  · ext i j
    have hentry := congrArg (fun M => M i j) hσ
    simpa [PEquiv.toMatrix_apply] using hentry

/--
Generic Schur-pattern lifting for three-factor decompositions.
-/
noncomputable def lift_schur_pattern
    {PropF₁ : ∀ {ι : Type}, Matrix ι ι R → Prop}
    {PropF₂ PropF₃ : ∀ {ι : Type} [LinearOrder ι], Matrix ι ι R → Prop}
    (h_reindexF₁ :
      ∀ {ι ι'} (e : ι ≃ ι') (A : Matrix ι ι R),
        PropF₁ A ↔ PropF₁ (A.reindex e e))
    (h_reindexF₂ :
      ∀ {ι ι'} [LinearOrder ι] [LinearOrder ι'] (e : ι ≃ ι') (_h_mono : StrictMono e)
        (A : Matrix ι ι R),
        PropF₂ A ↔ PropF₂ (A.reindex e e))
    (h_reindexF₃ :
      ∀ {ι ι'} [LinearOrder ι] [LinearOrder ι'] (e : ι ≃ ι') (_h_mono : StrictMono e)
        (A : Matrix ι ι R),
        PropF₃ A ↔ PropF₃ (A.reindex e e))
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (h_pivot_unit : IsUnit (A 0 0))
    (subF₁ subF₂ subF₃ : Matrix (Fin k) (Fin k) R)
    (h_subF₁_prop : PropF₁
      ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subF₁ :
        Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex))
    (h_subF₂_prop : PropF₂
      ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0
        (subF₁ *
          (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₂₁ *
            !![(IsUnit.unit h_pivot_unit).inv])
        subF₂ :
        Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex))
    (h_subF₃_prop : PropF₃
      ((fromBlocks
        (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₁
        (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₂
        0 subF₃ :
        Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex))
    (h_slice_eq : subF₁ * ((Reductions.SchurMethod k R).slice A h_pivot_unit) = subF₂ * subF₃)
    : { res : LiftedThreeFactors PropF₁ PropF₂ PropF₃ // res.F₁ * A = res.F₂ * res.F₃ } :=

  let e : Fin (k + 1) ≃ (Fin 1) ⊕ₗ (Fin k) := finSuccEquivSumLex k
  have h_mono : StrictMono e := by simpa [e] using (finSuccEquivSumLex_strictMono k)

  let A' := Matrix.reindex e e A
  let A₁₁ := A'.toBlocks₁₁
  let A₁₂ := A'.toBlocks₁₂
  let A₂₁ := A'.toBlocks₂₁
  let A₂₂ := A'.toBlocks₂₂
  let inv₁₁ : Matrix (Fin 1) (Fin 1) R := !![(IsUnit.unit h_pivot_unit).inv]

  let F₁_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subF₁
  let F₂_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 (subF₁ * A₂₁ * inv₁₁) subF₂
  let F₃_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks A₁₁ A₁₂ 0 subF₃

  let F₁ := Matrix.reindex e.symm e.symm F₁_blk
  let F₂ := Matrix.reindex e.symm e.symm F₂_blk
  let F₃ := Matrix.reindex e.symm e.symm F₃_blk

  { val := { F₁ := F₁, F₂ := F₂, F₃ := F₃,
             hF₁ := (h_reindexF₁ e F₁).2 (by simpa [F₁, F₁_blk] using h_subF₁_prop),
             hF₂ := (h_reindexF₂ e h_mono F₂).2 (by
               simpa [F₂, F₂_blk, A', A₂₁, inv₁₁] using h_subF₂_prop),
             hF₃ := (h_reindexF₃ e h_mono F₃).2 (by
               simpa [F₃, F₃_blk, A', A₁₁, A₁₂] using h_subF₃_prop)
           },
    property := by
      let Aℓ : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R := Matrix.reindex e e A
      have h_blk : F₁_blk * Aℓ = F₂_blk * F₃_blk := by
        change
          (F₁_blk : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R) *
              (Aℓ : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R) =
            (F₂_blk : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R) *
              (F₃_blk : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R)
        let F₁_blk_sum : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R := F₁_blk
        let F₂_blk_sum : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R := F₂_blk
        let F₃_blk_sum : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R := F₃_blk
        let F₁_blk_sum : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R := F₁_blk
        let F₂_blk_sum : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R := F₂_blk
        let F₃_blk_sum : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R := F₃_blk
        have h_lhs :
            F₁_blk * Aℓ =
              (fromBlocks A₁₁ A₁₂ (subF₁ * A₂₁) (subF₁ * A₂₂) :
                Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
          rw [show Aℓ =
              (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ :
                Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) by
              exact (fromBlocks_toBlocks Aℓ).symm]
          exact block_P_mul_A A₁₁ A₁₂ A₂₁ A₂₂ subF₁
        have h_rhs :
            F₂_blk * F₃_blk =
              (fromBlocks A₁₁ A₁₂ (subF₁ * A₂₁ * inv₁₁ * A₁₁)
                (subF₁ * A₂₁ * inv₁₁ * A₁₂ + subF₂ * subF₃) :
                Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R) := by
          exact block_L_mul_U (subF₁ * A₂₁ * inv₁₁) subF₂ A₁₁ A₁₂ subF₃
        have h_slice_def :
            (Reductions.SchurMethod k R).slice A h_pivot_unit =
              A₂₂ - A₂₁ * inv₁₁ * A₁₂ := by
          rfl
        rw [h_lhs, h_rhs, ← h_slice_eq, h_slice_def]
        ext i j
        cases i <;> cases j
        · simp [fromBlocks_apply₁₁]
        · simp [fromBlocks_apply₁₂]
        · have h_inv_mul : inv₁₁ * A₁₁ = (1 : Matrix (Fin 1) (Fin 1) R) := by
            ext i j
            fin_cases i
            fin_cases j
            simpa [inv₁₁, A₁₁, A', e, finSuccEquivSumLex, Matrix.toBlocks₁₁,
              Matrix.reindex_apply] using
              (inv_mul_cancel₀ (IsUnit.ne_zero h_pivot_unit))
          simp [fromBlocks_apply₂₁, Matrix.mul_assoc, h_inv_mul]
        · have h22 :
              subF₁ * A₂₂ =
                subF₁ * A₂₁ * inv₁₁ * A₁₂ + subF₁ * (A₂₂ - A₂₁ * inv₁₁ * A₁₂) := by
            have h_assoc :
                subF₁ * (A₂₁ * inv₁₁ * A₁₂) = subF₁ * A₂₁ * inv₁₁ * A₁₂ := by
              simp [Matrix.mul_assoc]
            have h' :
                subF₁ * A₂₁ * inv₁₁ * A₁₂ + subF₁ * (A₂₂ - A₂₁ * inv₁₁ * A₁₂) =
                  subF₁ * A₂₂ := by
              calc
                subF₁ * A₂₁ * inv₁₁ * A₁₂ + subF₁ * (A₂₂ - A₂₁ * inv₁₁ * A₁₂)
                    = subF₁ * A₂₁ * inv₁₁ * A₁₂ +
                        (subF₁ * A₂₂ - subF₁ * A₂₁ * inv₁₁ * A₁₂) := by
                        simp [mul_sub, Matrix.mul_assoc]
                _ = subF₁ * A₂₂ := by
                        simp [sub_eq_add_neg, add_left_comm, add_comm]
            simpa using h'.symm
          simp [fromBlocks_apply₂₂, h22]
      exact schur_case_transport_back (R := R) (A := A) (e := e)
        (P_blk := F₁_blk) (L_blk := F₂_blk) (U_blk := F₃_blk) h_blk
  }

/--
Generic zero-column-pattern lifting for three-factor decompositions.
-/
noncomputable def lift_zero_col_pattern
    {PropF₁ : ∀ {ι : Type}, Matrix ι ι R → Prop}
    {PropF₂ PropF₃ : ∀ {ι : Type} [LinearOrder ι], Matrix ι ι R → Prop}
    (h_reindexF₁ :
      ∀ {ι ι'} (e : ι ≃ ι') (A : Matrix ι ι R),
        PropF₁ A ↔ PropF₁ (A.reindex e e))
    (h_reindexF₂ :
      ∀ {ι ι'} [LinearOrder ι] [LinearOrder ι'] (e : ι ≃ ι') (_h_mono : StrictMono e)
        (A : Matrix ι ι R),
        PropF₂ A ↔ PropF₂ (A.reindex e e))
    (h_reindexF₃ :
      ∀ {ι ι'} [LinearOrder ι] [LinearOrder ι'] (e : ι ≃ ι') (_h_mono : StrictMono e)
        (A : Matrix ι ι R),
        PropF₃ A ↔ PropF₃ (A.reindex e e))
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (h_zero_col : ∀ i, A i 0 = 0)
    (subF₁ subF₂ subF₃ : Matrix (Fin k) (Fin k) R)
    (h_subF₁_prop : PropF₁
      ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subF₁ :
        Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex))
    (h_subF₂_prop : PropF₂
      ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subF₂ :
        Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex))
    (h_subF₃_prop : PropF₃
      ((fromBlocks 0
        (Matrix.reindex (finSuccEquivSumLex k) (finSuccEquivSumLex k) A).toBlocks₁₂
        0 subF₃ :
        Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R).reindex toLex toLex))
    (h_slice_eq : subF₁ * ((Reductions.ZeroColumnMethod k k R).slice A h_zero_col) = subF₂ * subF₃)
    : { res : LiftedThreeFactors PropF₁ PropF₂ PropF₃ // res.F₁ * A = res.F₂ * res.F₃ } :=

  let e : Fin (k + 1) ≃ (Fin 1) ⊕ₗ (Fin k) := finSuccEquivSumLex k
  have h_mono : StrictMono e := by simpa [e] using (finSuccEquivSumLex_strictMono k)

  let A' := Matrix.reindex e e A
  let A₁₁ := A'.toBlocks₁₁
  let A₁₂ := A'.toBlocks₁₂
  let A₂₁ := A'.toBlocks₂₁
  let A₂₂ := A'.toBlocks₂₂

  let F₁_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subF₁
  let F₂_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 subF₂
  let F₃_blk : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R :=
    fromBlocks (0 : Matrix (Fin 1) (Fin 1) R) A₁₂ 0 subF₃

  let F₁ := Matrix.reindex e.symm e.symm F₁_blk
  let F₂ := Matrix.reindex e.symm e.symm F₂_blk
  let F₃ := Matrix.reindex e.symm e.symm F₃_blk

  { val := { F₁ := F₁, F₂ := F₂, F₃ := F₃,
             hF₁ := (h_reindexF₁ e F₁).2 (by simpa [F₁, F₁_blk] using h_subF₁_prop),
             hF₂ := (h_reindexF₂ e h_mono F₂).2 (by simpa [F₂, F₂_blk] using h_subF₂_prop),
             hF₃ := (h_reindexF₃ e h_mono F₃).2 (by
               simpa [F₃, F₃_blk, A', A₁₂] using h_subF₃_prop)
           },
    property := by
      let Aℓ : Matrix (Fin 1 ⊕ₗ Fin k) (Fin 1 ⊕ₗ Fin k) R := Matrix.reindex e e A
      have h_blk : F₁_blk * Aℓ = F₂_blk * F₃_blk := by
        change
          (F₁_blk : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R) *
              (Aℓ : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R) =
            (F₂_blk : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R) *
              (F₃_blk : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R)
        let F₁_blk_sum : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R := F₁_blk
        let F₂_blk_sum : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R := F₂_blk
        let F₃_blk_sum : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) R := F₃_blk
        have h_A_left_zeros : A'.toBlocks₁₁ = 0 ∧ A'.toBlocks₂₁ = 0 := by
          constructor
          · ext i j
            fin_cases i
            fin_cases j
            simpa [A', Aℓ, e, finSuccEquivSumLex, Matrix.toBlocks₁₁, Matrix.reindex_apply] using
              (h_zero_col 0)
          · ext i j
            fin_cases j
            simpa [A', Aℓ, e, finSuccEquivSumLex, Matrix.toBlocks₂₁, Matrix.reindex_apply] using
              (h_zero_col i.succ)
        have hAℓ_blocks :
            Aℓ = fromBlocks (0 : Matrix (Fin 1) (Fin 1) R) A₁₂
              (0 : Matrix (Fin k) (Fin 1) R) A₂₂ := by
          have h_blocks : Aℓ = fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ :=
            (fromBlocks_toBlocks Aℓ).symm
          simpa [A₁₁, A₂₁, h_A_left_zeros.1, h_A_left_zeros.2] using h_blocks
        rw [hAℓ_blocks]
        have h_lhs :
            F₁_blk_sum * (fromBlocks (0 : Matrix (Fin 1) (Fin 1) R) A₁₂
                (0 : Matrix (Fin k) (Fin 1) R) A₂₂) =
              fromBlocks (0 : Matrix (Fin 1) (Fin 1) R) A₁₂
                (0 : Matrix (Fin k) (Fin 1) R) (subF₁ * A₂₂) := by
          simpa [F₁_blk_sum] using block_P_mul_A (0 : Matrix (Fin 1) (Fin 1) R) A₁₂
            (0 : Matrix (Fin k) (Fin 1) R) A₂₂ subF₁
        have h_rhs :
            F₂_blk_sum * F₃_blk_sum =
              fromBlocks (0 : Matrix (Fin 1) (Fin 1) R) A₁₂
                (0 : Matrix (Fin k) (Fin 1) R) (subF₂ * subF₃) := by
          simpa [F₂_blk_sum, F₃_blk_sum] using
            block_P_mul_A (0 : Matrix (Fin 1) (Fin 1) R) A₁₂
              (0 : Matrix (Fin k) (Fin 1) R) subF₃ subF₂
        have h_slice_def :
            (Reductions.ZeroColumnMethod k k R).slice A h_zero_col = A₂₂ := by
          simpa [A', A₂₂, finSuccEquivSumLex, finSuccEquivSum] using
            (submatrix_succ_eq_toBlocks₂₂ (A := A) (n := k) (m := k))
        rw [h_lhs, h_rhs, ← h_slice_eq, h_slice_def]
      exact schur_case_transport_back (R := R) (A := A) (e := e)
        (P_blk := F₁_blk) (L_blk := F₂_blk) (U_blk := F₃_blk) h_blk
  }

end GenericLifting

end MatDecompFormal.Components
