import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Order.Basic
import MatDecompFormal.Framework.FinEnum

namespace MatDecompFormal.Components.Properties

open FinEnum Matrix MatDecompFormal.Framework

/-!
# Row Echelon Form Property

This file defines helper objects for matrix row echelon form. The file is not yet
finalized, so it remains an internal module and is not part of the public export surface.
-/

section NonZeroIndex

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Zero R] [DecidableEq R]

/--
`NonZeroIndex A i` computes the column index of the first nonzero entry in row `i` of matrix `A`.

To implement lookup over a general `FinEnum` type `κ`, we use the equivalence between
`κ` and `Fin (card κ)`, run `Fin.find` on the `Fin` type, and then map the result
back to `κ`.

*   `A`: the input matrix.
*   `i`: the row index.
*   **Returns**: a value of type `WithTop κ`. If a pivot is found, it is `some j`;
    if the row is all zero, it is `⊤`, i.e. `none`.
-/
noncomputable def NonZeroIndex (A : Matrix ι κ R) (i : ι) : WithTop κ :=
  let finEnum_κ : FinEnum κ := inferInstance
  let eκ : κ ≃ Fin (FinEnum.card κ) := finEnum_κ.equiv
  let row_vec : Fin (card κ) → R := fun j ↦ A i (eκ.symm j)
  let find_result : WithTop (Fin (card κ)) := Fin.find (fun j ↦ row_vec j ≠ 0)
  find_result.map eκ.symm

namespace NonZeroIndex

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Zero R] [DecidableEq R] (A : Matrix ι κ R)

lemma eq_top_iff {i} : NonZeroIndex A i = ⊤ ↔ ∀ j, A i j = 0 := by
  dsimp [NonZeroIndex]
  rw [WithTop.map_eq_top_iff]
  sorry

lemma ne_top_iff {i} : NonZeroIndex A i ≠ ⊤ ↔ ∃ j, NonZeroIndex A i = some j := sorry

lemma eq_some_iff {i} {j₀} :
    NonZeroIndex A i = some j₀ ↔
      (∀ j, (@equiv κ) j < (@equiv κ) j₀ → A i j = 0) ∧ A i j₀ ≠ 0 := by
  dsimp [NonZeroIndex]
  sorry

end NonZeroIndex

end NonZeroIndex

section IsRowEchelon

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Zero R] [DecidableEq R]

noncomputable local instance : LinearOrder ι := LinearOrder.ofFinEnum ι
noncomputable local instance : LinearOrder κ := LinearOrder.ofFinEnum κ

end IsRowEchelon

end MatDecompFormal.Components.Properties
