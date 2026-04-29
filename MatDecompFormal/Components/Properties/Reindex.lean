import MatDecompFormal.Framework.FinEnum
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Diagonal

namespace MatDecompFormal.Components.Properties

open Matrix FinEnum

/-!
# Reindex and Matrix Properties

This file collects preservation lemmas for `Matrix.reindex`, including:

* permutation matrices (`IsPermutation`)
* diagonals (`diag`)
* upper triangular / lower triangular / unit lower triangular matrices
  (`IsUpperTriangular`, `IsLowerTriangular`, `IsUnitLowerTriangular`)

In the `FinEnum` setting, it also relates `IsUpperTriangular` to the equivalent
`BlockTriangular A (@equiv ι _)` formulation.
-/


-- We split the lemmas into two parts: one only needs Equiv,
-- and the other needs the stronger OrderIso

section EquivBased

variable {ι ι' R : Type*} [CommRing R] [DecidableEq ι] [DecidableEq ι']

/--
Reindexing the permutation matrix `(Equiv.toPEquiv σ).toMatrix` by `e e`
is equivalent to applying `permCongr` to the permutation and then taking its matrix.
-/
lemma toMatrix_reindex_permCongr (e : ι ≃ ι') (σ : Equiv.Perm ι) :
    ((Equiv.toPEquiv σ).toMatrix : Matrix ι ι R).reindex e e =
      (Equiv.toPEquiv (e.permCongr σ)).toMatrix := by
  classical
  ext i j
  simp [Matrix.reindex_apply, PEquiv.toMatrix_apply,
    Equiv.permCongr_apply, Equiv.eq_symm_apply]

/--
`IsPermutation` is preserved under `reindex e e`.
-/
lemma isPermutation_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
    IsPermutation A ↔ IsPermutation (A.reindex e e) := by
  classical
  constructor
  · -- (→)
    intro hA; rcases hA with ⟨σ, rfl⟩
    dsimp [IsPermutation]
    refine ⟨e.permCongr σ, ?_⟩
    simpa using
      toMatrix_reindex_permCongr (e := e) (σ := σ)
  · -- (←)
    intro hA_reindexed
    rcases hA_reindexed with ⟨σ, hσ⟩
    refine ⟨e.symm.permCongr σ, ?_⟩
    -- Reindex both sides of the equality back again
    have h := congrArg (Matrix.reindex e.symm e.symm) hσ
    -- The left side contracts to A; use the permutation congruence lemma,
    -- now with equivalence e.symm `Matrix.reindex_apply` + `Equiv.symm_apply_apply`
    -- ensure that reindexing and then reindexing back recovers the original matrix.
    simpa [Matrix.reindex_apply,
      toMatrix_reindex_permCongr (e := e.symm) (σ := σ)] using h

end EquivBased



/-!
## Diagonals and reindex
-/

section

variable {ι ι' R : Type*}

/--
The diagonal after `reindex` is the original diagonal composed with `e.symm`.
-/
lemma diag_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
    (A.reindex e e).diag = A.diag ∘ e.symm := by
  funext i'
  -- Unfold diag and reindex
  simp [Matrix.diag, Matrix.reindex_apply, Function.comp]

end



/-!
## Upper/lower triangularity and reindex under OrderIso
-/

section OrderPropertyBased

-- For order-dependent properties, separate the Equiv from the order-preservation assumption
variable {ι ι' R : Type*} [LinearOrder ι] [Preorder ι'] [Zero R]

/--
Upper triangularity is preserved under the basis change induced by a strictly monotone `Equiv`.
-/
lemma isUpperTriangular_reindex (e : ι ≃ ι') (h_mono : StrictMono e) (A : Matrix ι ι R) :
    IsUpperTriangular A ↔ IsUpperTriangular (A.reindex e e) := by
  dsimp [IsUpperTriangular, BlockTriangular]
  constructor
  · intro h i' j' h_lt
    -- `StrictMono` implies `Monotone`; use it to reflect the order through `e.symm`.
    have h_preimage_lt : e.symm j' < e.symm i' := by
      -- `StrictMono.lt_iff_lt` lets us pull back `<` along `e`.
      have h_lt' : e (e.symm j') < e (e.symm i') := by
        simpa using h_lt
      exact (h_mono.lt_iff_lt).1 h_lt'
    simpa [Matrix.reindex_apply] using h h_preimage_lt
  · intro h i j h_lt
    have h_image_lt : e j < e i := h_mono h_lt
    simpa [Matrix.reindex_apply] using h h_image_lt

/--
Lower triangularity is preserved under the basis change induced by a strictly monotone `Equiv`.
-/
lemma isLowerTriangular_reindex (e : ι ≃ ι') (h_mono : StrictMono e) (A : Matrix ι ι R) :
    IsLowerTriangular A ↔ IsLowerTriangular (A.reindex e e) := by
  dsimp [IsLowerTriangular]
  have h := isUpperTriangular_reindex (e := e) (h_mono := h_mono) (A := Aᵀ)
  simpa [IsLowerTriangular, Matrix.transpose_reindex] using h

/--
Unit lower triangularity is preserved under the basis change induced by a strictly monotone `Equiv`.
-/
lemma isUnitLowerTriangular_reindex (e : ι ≃ ι') (h_mono : StrictMono e)
    (A : Matrix ι ι R) [One R] : --[DecidableEq ι] [DecidableEq ι'] :
    IsUnitLowerTriangular A ↔ IsUnitLowerTriangular (A.reindex e e) := by
  dsimp [IsUnitLowerTriangular]
  -- We need to prove `IsLowerTriangular` and `diag` properties are preserved.
  constructor
  · rintro ⟨hLT, hdiag⟩
    refine ⟨(isLowerTriangular_reindex (e := e) (h_mono := h_mono) (A := A)).1 hLT, ?_⟩
    -- diagonal entries remain `1` after reindexing
    funext i
    have hdiag_eval : A.diag (e.symm i) = 1 := by
      have := congrArg (fun f => f (e.symm i)) hdiag
      simpa using this
    simpa [diag_reindex, Function.comp] using hdiag_eval
  · rintro ⟨hLT, hdiag⟩
    refine ⟨(isLowerTriangular_reindex (e := e) (h_mono := h_mono) (A := A)).2 hLT, ?_⟩
    funext i
    have h := congrArg (fun f => f (e i)) hdiag
    -- unfold the diagonal of the reindexed matrix
    simpa [diag_reindex, Function.comp] using h

end OrderPropertyBased



/-!
## Upper-triangular compatibility in the FinEnum setting

For a `FinEnum` index type, upper triangularity can be expressed either through
the canonical enumeration `equiv : ι ≃ Fin (card ι)` or through the
`LinearOrder` on the index type itself.

The lemma below states that the two are equivalent in the `FinEnum` setting.
-/

section FinEnumCompat

variable {ι R : Type*} [FinEnum ι] [Zero R]

/--
In the `FinEnum` setting, `IsUpperTriangular` is equivalent to
`BlockTriangular A (@equiv ι _)`, using `FinEnum.equiv` as the blocking function.
-/
lemma isUpperTriangular_iff_blockTriangular_equiv (A : Matrix ι ι R) :
    IsUpperTriangular A ↔ BlockTriangular A (@equiv ι _) := by
  classical
  -- e : ι ≃o Fin (card ι)
  let e := MatDecompFormal.Framework.orderIsoOfFinEnum ι
  -- IsUpperTriangular A = BlockTriangular A (fun i => i)
  dsimp [IsUpperTriangular]
  -- First prove that using id and using e give equivalent results
  have h :
      BlockTriangular A (fun i : ι => i) ↔
        BlockTriangular A (fun i : ι => e i) := by
    constructor
    · intro hBT i j hlt
      -- e.lt_iff_lt turns e j < e i into j < i
      have hlt' : j < i := (e.lt_iff_lt).mp hlt
      exact hBT hlt'
    · intro hBT i j hlt
      -- The reverse direction is analogous
      have hlt' : e j < e i := (e.lt_iff_lt).mpr hlt
      exact hBT hlt'
  -- Then note that e.toEquiv = equiv, by the definition in Framework.FinEnum
  have heq : (fun i : ι => e i) = (fun i : ι => (@equiv ι _) i) := by
    funext i; rfl
  -- Use heq to rewrite the BlockTriangular blocking function as (@equiv ι _)
  simpa [heq] using h

end FinEnumCompat


end MatDecompFormal.Components.Properties
