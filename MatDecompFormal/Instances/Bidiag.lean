import MatDecompFormal.Instances.Bidiag.Core
import MatDecompFormal.Instances.Bidiag.Bridge
import Mathlib.Data.Real.Basic

/-!
# Bidiagonalization

This file is the local main-line assembly file for a new bidiagonalization
instance draft.

Reading from top to bottom shows:

* the internal `Fin`-level surface from `Instances.Bidiag.Core`
  (`IsUpperBidiagonal_fin`, `Bidiag_Schema_fin`, `HasBidiag_fin`);
* the local constructor theorems available without changing the current global
  framework;
* the external `FinEnum` presentation surface from `Instances.Bidiag.Bridge`
  (`IsUpperBidiagonal`, `Bidiag_Schema`, `HasBidiag`);
* the corresponding external constructor theorem.

What is intentionally missing is also part of the experiment: unlike PLU/QR,
this draft does not package a full driver-backed existence theorem for all
matrices. That gap is exactly where the current framework shows its one-sided,
square-oriented bias.
-/

namespace MatDecompFormal.Instances

open Matrix

section InternalSurface

/- `IsUpperBidiagonal_fin`, `Bidiag_Schema_fin`, and `HasBidiag_fin` are
provided by `Instances.Bidiag.Core`. -/

end InternalSurface

section InternalConstructors

/--
Internal main theorem for the current bidiagonal draft.

The theorem is intentionally constructor-shaped: bidiagonalization here is
packaged from genuine two-sided orthogonal/bidiagonal data, without pretending
that the existing one-sided square driver already supports this instance.
-/
theorem exists_bidiagonalization_fin_of_orthogonal_bidiagonal_data
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ)
    (hU : IsOrthogonalMatrix_fin (m := m) U)
  (hB : IsUpperBidiagonal_fin (m := m) (n := n) B)
  (hV : IsOrthogonalMatrix_fin (m := n) V)
  (hEq : A = U * B * Vᵀ) :
    HasBidiag_fin (m := m) (n := n) A := by
  exact mk_hasBidiag_fin_of_data A U B V hU hB hV hEq

/--
Internal ready theorem: an already upper-bidiagonal rectangular matrix admits
the trivial bidiagonalization.
-/
theorem exists_bidiagonalization_fin_of_upperBidiagonal
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : IsUpperBidiagonal_fin (m := m) (n := n) A) :
    HasBidiag_fin (m := m) (n := n) A := by
  exact mk_hasBidiag_fin_of_upperBidiagonal A hA

end InternalConstructors

section ExternalSurface

/- `IsUpperBidiagonal`, `Bidiag_Schema`, and `HasBidiag` are provided by
`Instances.Bidiag.Bridge`. -/

end ExternalSurface

section ExternalConstructors

/--
External main theorem for the local bidiagonal draft.
-/
theorem exists_bidiagonalization_of_orthogonal_bidiagonal_data
    {ι κ : Type*} [FinEnum ι] [FinEnum κ]
    (A : Matrix ι κ ℝ)
    (U : Matrix ι ι ℝ)
    (B : Matrix ι κ ℝ)
    (V : Matrix κ κ ℝ)
    (hU : IsOrthogonalMatrix U)
    (hB : IsUpperBidiagonal (ι := ι) (κ := κ) B)
    (hV : IsOrthogonalMatrix V)
    (hEq : A = U * B * Vᵀ) :
    HasBidiag (ι := ι) (κ := κ) A := by
  exact mk_hasBidiag_of_data A U B V hU hB hV hEq

/--
External ready theorem: an already upper-bidiagonal matrix admits the trivial
two-sided bidiagonalization.
-/
theorem exists_bidiagonalization_of_upperBidiagonal
    {ι κ : Type*} [FinEnum ι] [FinEnum κ]
    (A : Matrix ι κ ℝ)
    (hA : IsUpperBidiagonal (ι := ι) (κ := κ) A) :
    HasBidiag (ι := ι) (κ := κ) A := by
  exact mk_hasBidiag_of_upperBidiagonal A hA

end ExternalConstructors

end MatDecompFormal.Instances
