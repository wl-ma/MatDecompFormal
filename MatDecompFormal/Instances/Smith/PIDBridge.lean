import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import MatDecompFormal.Instances.Smith.Existence

universe u v w

namespace MatDecompFormal.Instances

open Matrix

/-!
# Smith PID Bridge

Mathlib's PID Smith normal form is currently stated for submodules of finite
free modules.  The matrix-level theorem in this project needs an additional
bridge: translate a rectangular matrix into a linear map/submodule statement,
extract the Smith bases, and repackage the basis changes as the explicit
matrices required by `HasSmithNormalForm`.

This file exposes the mathlib SNF data under the Smith namespace and keeps the
remaining matrix bridge as an explicit obligation.
-/

/--
The available PID Smith normal-form data from mathlib for a submodule of a
finite free module.

This is not yet the project's matrix theorem; it is the authoritative PID
source that the future matrix bridge should consume.
-/
noncomputable def pidSubmoduleSmithNormalForm
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (ι : Type w) [Finite ι]
    (b : Module.Basis ι R M) (N : Submodule R M) :
    Σ n : ℕ, Module.Basis.SmithNormalForm N ι n :=
  N.smithNormalForm b

/-- Existential wrapper around `pidSubmoduleSmithNormalForm`. -/
theorem exists_pid_submodule_smith_normal_form
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (ι : Type w) [Finite ι]
    (b : Module.Basis ι R M) (N : Submodule R M) :
    ∃ n : ℕ, Nonempty (Module.Basis.SmithNormalForm N ι n) := by
  let snf := pidSubmoduleSmithNormalForm R M ι b N
  exact ⟨snf.1, ⟨snf.2⟩⟩

section ChangeOfBasis

variable {R : Type u} [CommRing R]

/--
Mathlib's basis-change matrices carry an `Invertible` instance. This repackages
that instance into the explicit inverse witness used by this project.
-/
lemma gaussInvertibleMatrix_basis_toMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module R M]
    (b b' : Module.Basis ι R M) :
    GaussInvertibleMatrix (b.toMatrix b') := by
  classical
  letI : Invertible (b.toMatrix b') := Module.Basis.invertibleToMatrix b b'
  refine ⟨⅟(b.toMatrix b'), ?_, ?_⟩
  · exact invOf_mul_self (b.toMatrix b')
  · exact mul_invOf_self (b.toMatrix b')

/--
Changing both domain and codomain bases is represented by multiplication by
explicit basis-change matrices around the original matrix.

This is the core mechanical bridge needed after obtaining Smith bases from
mathlib's PID submodule normal form.
-/
theorem basis_change_toMatrix_eq_mul
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (bm bm' : Module.Basis m R M) (bn bn' : Module.Basis n R N)
    (f : M →ₗ[R] N) :
    LinearMap.toMatrix bm' bn' f =
      bn'.toMatrix bn * LinearMap.toMatrix bm bn f * bm.toMatrix bm' := by
  classical
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    bm' bm bn' bn f).symm

/--
Specialized basis-change formula for a concrete matrix over the standard
function-module bases.
-/
theorem basis_change_toMatrix_eq_mul_standard
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (bm' : Module.Basis m R (m → R)) (bn' : Module.Basis n R (n → R))
    (A : Matrix m n R) :
    LinearMap.toMatrix bn' bm' (Matrix.toLin' A) =
      bm'.toMatrix (Pi.basisFun R m) * A * (Pi.basisFun R n).toMatrix bn' := by
  classical
  have h :=
    basis_change_toMatrix_eq_mul
      (R := R) (Pi.basisFun R n) bn' (Pi.basisFun R m) bm' (Matrix.toLin' A)
  rw [h]
  rw [← Matrix.toLin_eq_toLin']
  rw [LinearMap.toMatrix_toLin]

end ChangeOfBasis

section RangeFactorization

variable {R : Type u} [CommRing R]

/-- A linear map factors through the inclusion of its range. -/
theorem linearMap_eq_range_subtype_comp_rangeRestrict
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    f = (LinearMap.range f).subtype.comp f.rangeRestrict :=
  rfl

/--
Matrix form of the range factorization `f = range(f).subtype ∘ f.rangeRestrict`.

The left factor is an inclusion matrix for the range submodule; the right
factor is the matrix of the surjection onto that range.
-/
theorem linearMap_toMatrix_eq_range_subtype_mul_rangeRestrict
    {m n r : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (bm : Module.Basis m R M) (bn : Module.Basis n R N)
    (f : M →ₗ[R] N)
    (br : Module.Basis r R (LinearMap.range f)) :
    LinearMap.toMatrix bm bn f =
      LinearMap.toMatrix br bn (LinearMap.range f).subtype *
        LinearMap.toMatrix bm br f.rangeRestrict := by
  classical
  have h :=
    LinearMap.toMatrix_comp bm br bn (LinearMap.range f).subtype f.rangeRestrict
  simpa [← linearMap_eq_range_subtype_comp_rangeRestrict f] using h

/--
Standard-basis matrix form of the range factorization of a concrete matrix.
-/
theorem matrix_eq_range_subtype_mul_rangeRestrict
    {m n r : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A))) :
    A =
      LinearMap.toMatrix br (Pi.basisFun R m) (LinearMap.range (Matrix.toLin' A)).subtype *
        LinearMap.toMatrix (Pi.basisFun R n) br (Matrix.toLin' A).rangeRestrict := by
  classical
  have h :=
    linearMap_toMatrix_eq_range_subtype_mul_rangeRestrict
      (R := R) (bm := Pi.basisFun R n) (bn := Pi.basisFun R m)
      (f := Matrix.toLin' A) (br := br)
  have hstd :
      LinearMap.toMatrix (Pi.basisFun R n) (Pi.basisFun R m) (Matrix.toLin' A) = A := by
    rw [← Matrix.toLin_eq_toLin']
    exact LinearMap.toMatrix_toLin (Pi.basisFun R n) (Pi.basisFun R m) A
  rwa [hstd] at h

end RangeFactorization

section SubmoduleMatrix

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {N : Submodule R M} {rank : ℕ}

/-- Lift finite Smith-rank indices into the same universe as the ambient basis index. -/
abbrev PIDSmithRankIdx (rank : ℕ) : Type u :=
  ULift.{u, 0} (Fin rank)

/-- Equivalence between mathlib's `Fin rank` Smith index and the local lifted index. -/
def pidSmithRankEquiv (rank : ℕ) : Fin rank ≃ ULift.{u, 0} (Fin rank) :=
  Equiv.ulift.symm

/--
Mathlib's submodule Smith normal form gives a rectangular diagonal matrix for
the inclusion map `N.subtype`, when written in the Smith bases.
-/
noncomputable def smithNormalFormData_of_basisSmithNormalForm
    (snf : Module.Basis.SmithNormalForm N ι rank) :
    SmithNormalFormData (R := R) (m := ι) (n := PIDSmithRankIdx rank)
      (fun i (j : PIDSmithRankIdx rank) =>
        LinearMap.toMatrix snf.bN snf.bM N.subtype i j.down) where
  r := PIDSmithRankIdx rank
  fintype_r := inferInstance
  row := fun k => snf.f k.down
  col := id
  diag := fun k => snf.a k.down
  row_injective := by
    intro a b h
    cases a
    cases b
    have hdown := snf.f.injective h
    cases hdown
    rfl
  col_injective := Function.injective_id
  successor := fun _ _ => False
  entry_diag := by
    intro k
    rw [LinearMap.toMatrix_apply]
    have hrepr :
        (snf.bM.repr ((snf.bN k.down : N) : M)) (snf.f k.down) =
          snf.a k.down := by
      simpa using
        congrArg (fun x : M => snf.bM.repr x (snf.f k.down)) (snf.snf k.down)
    exact hrepr
  entry_zero := by
    intro i j h
    have hne : snf.f j.down ≠ i := by
      specialize h j
      simpa using h
    rw [LinearMap.toMatrix_apply]
    change (snf.bM.repr ((snf.bN j.down : N) : M)) i = 0
    rw [snf.snf j.down]
    simp [hne]
  divides_next := by
    intro k l h
    cases h

/--
The matrix of the inclusion map in mathlib Smith bases satisfies this project's
local Smith normal-form predicate.
-/
theorem isSmithNormalForm_of_basisSmithNormalForm
    (snf : Module.Basis.SmithNormalForm N ι rank) :
    IsSmithNormalForm (R := R) (m := ι) (n := PIDSmithRankIdx rank)
      (fun i (j : PIDSmithRankIdx rank) =>
        LinearMap.toMatrix snf.bN snf.bM N.subtype i j.down) :=
  ⟨smithNormalFormData_of_basisSmithNormalForm snf⟩

/--
Reindexed version of `isSmithNormalForm_of_basisSmithNormalForm`, using an
actual basis indexed by `PIDSmithRankIdx rank`.
-/
theorem isSmithNormalForm_of_basisSmithNormalForm_reindex
    (snf : Module.Basis.SmithNormalForm N ι rank) :
    IsSmithNormalForm
      (LinearMap.toMatrix
        (snf.bN.reindex (pidSmithRankEquiv rank)) snf.bM N.subtype) := by
  classical
  have hmat :
      LinearMap.toMatrix
          (snf.bN.reindex (pidSmithRankEquiv rank)) snf.bM N.subtype =
        (fun i (j : PIDSmithRankIdx rank) =>
          LinearMap.toMatrix snf.bN snf.bM N.subtype i j.down) := by
    ext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.reindex_apply, pidSmithRankEquiv]
  rw [hmat]
  exact isSmithNormalForm_of_basisSmithNormalForm snf

/--
Mathlib's submodule Smith normal form gives a full project-level Smith witness
for the inclusion matrix `N.subtype`, written with an arbitrary ambient basis
on rows and the Smith basis of `N` on columns.

This is the verified range-inclusion half of the PID matrix bridge. The
remaining bridge from an arbitrary matrix `A` to this inclusion matrix still
has to account for the map onto its range and the original column type.
-/
theorem hasSmithNormalForm_subtype_matrix_of_basisSmithNormalForm
    (b : Module.Basis ι R M)
    (snf : Module.Basis.SmithNormalForm N ι rank) :
  HasSmithNormalForm
      (LinearMap.toMatrix
        (snf.bN.reindex (pidSmithRankEquiv rank)) b N.subtype) := by
  classical
  let bN := snf.bN.reindex (pidSmithRankEquiv rank)
  let A := LinearMap.toMatrix bN b N.subtype
  let D := LinearMap.toMatrix bN snf.bM N.subtype
  refine ⟨snf.bM.toMatrix b, 1, D,
    gaussInvertibleMatrix_basis_toMatrix snf.bM b,
    gaussInvertibleMatrix_one,
    ?_, ?_⟩
  · exact isSmithNormalForm_of_basisSmithNormalForm_reindex snf
  · have hchange :
        D = snf.bM.toMatrix b * A * bN.toMatrix bN := by
      exact basis_change_toMatrix_eq_mul bN bN b snf.bM N.subtype
    simpa [A, D, bN] using hchange

end SubmoduleMatrix

/--
Matrix-level PID Smith bridge obligation.

A proof of this structure is the missing conversion from mathlib's
submodule/basis Smith normal form to the project's explicit two-sided matrix
equivalence. Keeping it named prevents the public PID theorem from hiding this
dependency.
-/
structure PIDMatrixSmithBridge
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    Prop where
  hasSmith :
    ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
      [Fintype n] [DecidableEq n] [LinearOrder n],
      (A : Matrix m n R) → HasSmithNormalForm A

/--
PID-scope matrix Smith theorem conditional on the explicit matrix bridge from
mathlib's submodule SNF data.
-/
theorem exists_smith_normal_form_pid_bridge
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (bridge : PIDMatrixSmithBridge R)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A :=
  bridge.hasSmith A

end MatDecompFormal.Instances
