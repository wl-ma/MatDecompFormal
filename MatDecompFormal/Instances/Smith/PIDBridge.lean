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

/--
Writing a concrete matrix map in a reindexed standard column basis reindexes the
columns of the original matrix.
-/
theorem toMatrix_reindex_standard_domain_eq_reindex
    {m n n' : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (A : Matrix m n R) (e : n ≃ n') :
    LinearMap.toMatrix ((Pi.basisFun R n).reindex e) (Pi.basisFun R m)
        (Matrix.toLin' A) =
      Matrix.reindex (Equiv.refl m) e A := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply]
  rw [Matrix.toLin'_apply]
  rw [Module.Basis.reindex_apply]
  rw [Pi.basisFun_repr]
  rw [Matrix.reindex_apply]
  rw [Pi.basisFun_apply]
  rw [Matrix.mulVec_single_one]
  rfl

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
Column basis data for a map already written as a projection on basis vectors.

This is the controlled local form of the next kernel-complement step: once PID
module theory supplies a basis of the original column module whose first block
maps to the range basis and whose second block lies in the kernel, the matrix is
definitionally the left projection `[I 0]`.
-/
structure ProjectionBasisData
    (R : Type u) [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r k : Type u} [Fintype r] [DecidableEq r] [Fintype k] [DecidableEq k]
    (f : M →ₗ[R] P) (br : Module.Basis r R P) : Type (u + 1) where
  basis : Module.Basis (r ⊕ k) R M
  map_inl : ∀ i : r, f (basis (Sum.inl i)) = br i
  map_inr : ∀ i : k, f (basis (Sum.inr i)) = 0

/--
A projection-compatible basis writes a linear map as the explicit left
projection matrix `[I 0]`.
-/
theorem toMatrix_projectionBasisData_eq_leftProjection
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r k : Type u} [Fintype r] [DecidableEq r] [Fintype k] [DecidableEq k]
    (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (data : ProjectionBasisData R f br) :
    LinearMap.toMatrix data.basis br f =
      smithLeftProjection (R := R) (n := r) (κ := k) := by
  classical
  ext i j
  cases j with
  | inl j =>
      rw [LinearMap.toMatrix_apply]
      rw [data.map_inl]
      rw [Module.Basis.repr_self_apply]
      by_cases h : i = j
      · simp [smithLeftProjection, h]
      · have hji : j ≠ i := fun hji => h hji.symm
        simp [smithLeftProjection, h, hji]
  | inr j =>
      rw [LinearMap.toMatrix_apply]
      rw [data.map_inr]
      simp [smithLeftProjection]

/--
Split-product data for constructing a projection-compatible basis.

The missing PID module-theory step can target this structure: provide an
equivalence between the original column module and `P × K` such that the map
to `P` is the first projection on the basis vectors.
-/
structure ProjectionSplitEquivData
    (R : Type u) [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r : Type u} [Fintype r] [DecidableEq r]
    (f : M →ₗ[R] P) (br : Module.Basis r R P) : Type (u + 1) where
  kerIdx : Type u
  fintype_kerIdx : Fintype kerIdx
  decidableEq_kerIdx : DecidableEq kerIdx
  K : Type u
  addCommGroup_K : AddCommGroup K
  module_K : Module R K
  basis_K : Module.Basis kerIdx R K
  splitEquiv : M ≃ₗ[R] P × K
  map_inl : ∀ i : r,
    f (splitEquiv.symm (LinearMap.inl R P K (br i))) = br i
  map_inr : ∀ i : kerIdx,
    f (splitEquiv.symm (LinearMap.inr R P K (basis_K i))) = 0

attribute [instance] ProjectionSplitEquivData.fintype_kerIdx
attribute [instance] ProjectionSplitEquivData.decidableEq_kerIdx
attribute [instance] ProjectionSplitEquivData.addCommGroup_K
attribute [instance] ProjectionSplitEquivData.module_K

/--
The kernel-valued complement map associated to a right inverse `s` of `f`.

It sends `x` to `x - s (f x)`, which lies in `ker f`. Keeping this as a
separate linear map avoids unfolding the full split equivalence in later
proofs.
-/
noncomputable def kernelComplementMapOfRightInverse
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : f.comp s = LinearMap.id) :
    M →ₗ[R] LinearMap.ker f where
  toFun x := by
    refine ⟨x - s (f x), ?_⟩
    have hfs : f (s (f x)) = f x := by
      have hpoint := congrArg (fun g : P →ₗ[R] P => g (f x)) hs
      simpa using hpoint
    simp [hfs]
  map_add' x y := by
    ext
    simp [map_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  map_smul' a x := by
    ext
    simp [map_smul, smul_sub]

/--
A right inverse of `f` splits the domain as `P × ker f`.

The first projection of this equivalence is definitionally controlled by
`linearEquivProdKerOfRightInverse_fst_comp`, which is the shape needed by the
projection-split bridge.
-/
noncomputable def linearEquivProdKerOfRightInverse
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : f.comp s = LinearMap.id) :
    M ≃ₗ[R] P × LinearMap.ker f where
  toLinearMap := LinearMap.prod f (kernelComplementMapOfRightInverse f s hs)
  invFun y := s y.1 + y.2.1
  left_inv x := by
    simp [kernelComplementMapOfRightInverse]
  right_inv y := by
    ext
    · have hfs : f (s y.1) = y.1 := by
        have hpoint := congrArg (fun g : P →ₗ[R] P => g y.1) hs
        simpa using hpoint
      simp [hfs]
    · have hfs : f (s y.1) = y.1 := by
        have hpoint := congrArg (fun g : P →ₗ[R] P => g y.1) hs
        simpa using hpoint
      have hfy : f (s y.1 + y.2.1) = y.1 := by
        simp [map_add, hfs]
      simp [kernelComplementMapOfRightInverse, hfy, add_sub_cancel_left]

/-- The split equivalence from a right inverse has first projection `f`. -/
theorem linearEquivProdKerOfRightInverse_fst_comp
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : f.comp s = LinearMap.id) :
    (LinearMap.fst R P (LinearMap.ker f)).comp
        (linearEquivProdKerOfRightInverse f s hs).toLinearMap = f := by
  ext x
  rfl

/--
A split equivalence whose first projection is the original map supplies the
projection equations required by `ProjectionSplitEquivData`.

This is the preferred target for the remaining PID module-theory step: construct
`e : M ≃ₗ[R] P × K` and prove `fst ∘ e = f`, instead of proving the two
basis-vector equations directly.
-/
noncomputable def projectionSplitEquivData_of_fst_comp
    {R : Type u} [CommRing R]
    {M P K : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] [AddCommGroup K] [Module R K]
    {r k : Type u} [Fintype r] [DecidableEq r] [Fintype k] [DecidableEq k]
    (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (bk : Module.Basis k R K)
    (e : M ≃ₗ[R] P × K)
    (he : (LinearMap.fst R P K).comp e.toLinearMap = f) :
    ProjectionSplitEquivData R f br where
  kerIdx := k
  fintype_kerIdx := inferInstance
  decidableEq_kerIdx := inferInstance
  K := K
  addCommGroup_K := inferInstance
  module_K := inferInstance
  basis_K := bk
  splitEquiv := e
  map_inl := by
    intro i
    have hpoint :=
      congrArg (fun g : M →ₗ[R] P =>
        g (e.symm (LinearMap.inl R P K (br i)))) he
    simpa using hpoint.symm
  map_inr := by
    intro i
    have hpoint :=
      congrArg (fun g : M →ₗ[R] P =>
        g (e.symm (LinearMap.inr R P K (bk i)))) he
    simpa using hpoint.symm

/--
A right inverse of `f` plus a basis of `ker f` supplies
`ProjectionSplitEquivData`.

For the PID bridge, the planned source of the right inverse is projectivity of
the range of `Matrix.toLin' A`, and the planned source of the kernel basis is
finite-free PID module theory.
-/
noncomputable def projectionSplitEquivData_of_rightInverse
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r k : Type u} [Fintype r] [DecidableEq r] [Fintype k] [DecidableEq k]
    (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (s : P →ₗ[R] M) (hs : f.comp s = LinearMap.id)
    (bk : Module.Basis k R (LinearMap.ker f)) :
    ProjectionSplitEquivData R f br :=
  projectionSplitEquivData_of_fst_comp
    (f := f) (br := br) (bk := bk)
    (linearEquivProdKerOfRightInverse f s hs)
    (linearEquivProdKerOfRightInverse_fst_comp f s hs)

/--
A surjective map onto a module with a basis has a linear right inverse.

This packages the projectivity argument used for range restrictions: a module
with a basis is projective, so any surjection onto it splits.
-/
noncomputable def rightInverseOfSurjectiveOfBasis
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r : Type u} (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (hf : LinearMap.range f = ⊤) :
    {s : P →ₗ[R] M // f.comp s = LinearMap.id} := by
  classical
  haveI : Module.Projective R P := Module.Projective.of_basis br
  let h := f.exists_rightInverse_of_surjective hf
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/--
The range restriction of any map has a linear right inverse after choosing a
basis of the range.
-/
noncomputable def rightInverseOfRangeRestrictOfBasis
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r : Type u}
    (f : M →ₗ[R] P) (br : Module.Basis r R (LinearMap.range f)) :
    {s : LinearMap.range f →ₗ[R] M // f.rangeRestrict.comp s = LinearMap.id} :=
  rightInverseOfSurjectiveOfBasis f.rangeRestrict br (LinearMap.range_rangeRestrict f)

/--
Given a basis of `ker f`, projectivity of a basis on the target supplies the
section needed to build `ProjectionSplitEquivData`.
-/
noncomputable def projectionSplitEquivData_of_kernelBasis
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r k : Type u} [Fintype r] [DecidableEq r] [Fintype k] [DecidableEq k]
    (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (hf : LinearMap.range f = ⊤)
    (bk : Module.Basis k R (LinearMap.ker f)) :
    ProjectionSplitEquivData R f br := by
  classical
  let sec := rightInverseOfSurjectiveOfBasis f br hf
  exact projectionSplitEquivData_of_rightInverse
    (f := f) (br := br) sec.val sec.property bk

/--
PID basis for the kernel of the range restriction of a finite matrix.

This is the kernel-basis input required by
`projectionSplitEquivData_of_kernelBasis`.
-/
noncomputable def kernelBasisOfRangeRestrictPid
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix m n R) :
    Σ k : ℕ, Module.Basis (Fin k) R
      (LinearMap.ker (Matrix.toLin' A).rangeRestrict) :=
  Submodule.basisOfPid (Pi.basisFun R n)
    (LinearMap.ker (Matrix.toLin' A).rangeRestrict)

/--
Construct the projection-split data for a range restriction, assuming only the
range basis from the Smith normal-form data. The remaining global bridge still
has to identify the original finite column index with the product of range and
kernel indices.
-/
noncomputable def projectionSplitEquivDataOfRangeRestrictPid
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m n r : Type u} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A))) :
    ProjectionSplitEquivData R (Matrix.toLin' A).rangeRestrict br := by
  classical
  let kb := kernelBasisOfRangeRestrictPid (R := R) A
  exact projectionSplitEquivData_of_kernelBasis
    (R := R)
    (M := n → R)
    (P := LinearMap.range (Matrix.toLin' A))
    (r := r)
    (k := PIDSmithRankIdx kb.1)
    (f := (Matrix.toLin' A).rangeRestrict)
    (br := br)
    (hf := LinearMap.range_rangeRestrict (Matrix.toLin' A))
    (bk := kb.2.reindex (pidSmithRankEquiv kb.1))

/--
The basis carried by split-product data determines the finite column-index
equivalence required by the matrix bridge.
-/
noncomputable def indexEquivOfProjectionSplitEquivData
    {R : Type u} [CommRing R] [InvariantBasisNumber R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {n r : Type u} [Fintype r] [DecidableEq r]
    (bn : Module.Basis n R M) (br : Module.Basis r R P)
    {f : M →ₗ[R] P}
    (data : ProjectionSplitEquivData R f br) :
    n ≃ r ⊕ data.kerIdx :=
  bn.indexEquiv ((br.prod data.basis_K).map data.splitEquiv.symm)

/--
Column-index equivalence for a matrix range restriction after constructing the
PID projection-split data.
-/
noncomputable def colEquivOfProjectionSplitEquivData
    {R : Type u} [CommRing R] [InvariantBasisNumber R]
    {m n r : Type u} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A)))
    (data : ProjectionSplitEquivData R (Matrix.toLin' A).rangeRestrict br) :
    n ≃ r ⊕ data.kerIdx :=
  indexEquivOfProjectionSplitEquivData
    (R := R) (M := n → R) (P := LinearMap.range (Matrix.toLin' A))
    (bn := Pi.basisFun R n) (br := br) data

/-- A split-product equivalence supplies a projection-compatible basis. -/
noncomputable def projectionBasisData_of_splitEquivData
    {R : Type u} [CommRing R]
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    {r : Type u} [Fintype r] [DecidableEq r]
    (f : M →ₗ[R] P) (br : Module.Basis r R P)
    (data : ProjectionSplitEquivData R f br) :
    ProjectionBasisData (k := data.kerIdx) R f br where
  basis := (br.prod data.basis_K).map data.splitEquiv.symm
  map_inl := by
    intro i
    rw [Module.Basis.map_apply]
    rw [Module.Basis.prod_apply]
    exact data.map_inl i
  map_inr := by
    intro i
    rw [Module.Basis.map_apply]
    rw [Module.Basis.prod_apply]
    exact data.map_inr i

/--
Column-side data saying that the surjection from the original column module
onto the range is in split form `[I 0]` after a column basis change.

This is the remaining kernel-complement/basis-extension content needed to turn
the range-inclusion Smith witness into a Smith witness for the original matrix.
-/
structure SmithRangeSplitBasisData
    (R : Type u) [CommRing R]
    {m n r : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A))) :
    Type (u + 1) where
  kerIdx : Type u
  fintype_kerIdx : Fintype kerIdx
  decidableEq_kerIdx : DecidableEq kerIdx
  colEquiv : n ≃ r ⊕ kerIdx
  colBasis : Module.Basis (r ⊕ kerIdx) R (n → R)
  rangeRestrict_matrix :
    LinearMap.toMatrix colBasis br (Matrix.toLin' A).rangeRestrict =
      smithLeftProjection (R := R) (n := r) (κ := kerIdx)

attribute [instance] SmithRangeSplitBasisData.fintype_kerIdx
attribute [instance] SmithRangeSplitBasisData.decidableEq_kerIdx

/--
Projection-compatible basis data for the range restriction supplies the
column-side split data needed by the matrix bridge.
-/
noncomputable def smithRangeSplitBasisData_of_projectionBasisData
    {R : Type u} [CommRing R]
    {m n r k : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    [Fintype k] [DecidableEq k]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A)))
    (colEquiv : n ≃ r ⊕ k)
    (data :
      ProjectionBasisData (k := k) R (Matrix.toLin' A).rangeRestrict br) :
    SmithRangeSplitBasisData R A br where
  kerIdx := k
  fintype_kerIdx := inferInstance
  decidableEq_kerIdx := inferInstance
  colEquiv := colEquiv
  colBasis := data.basis
  rangeRestrict_matrix :=
    toMatrix_projectionBasisData_eq_leftProjection (Matrix.toLin' A).rangeRestrict br data

/--
Split-product data for the range restriction supplies the column-side split
data needed by the matrix bridge.
-/
noncomputable def smithRangeSplitBasisData_of_projectionSplitEquivData
    {R : Type u} [CommRing R]
    {m n r : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A)))
    (data :
      ProjectionSplitEquivData R (Matrix.toLin' A).rangeRestrict br)
    (colEquiv : n ≃ r ⊕ ProjectionSplitEquivData.kerIdx data) :
    SmithRangeSplitBasisData R A br :=
  smithRangeSplitBasisData_of_projectionBasisData
    (A := A) (br := br) (colEquiv := colEquiv)
    (projectionBasisData_of_splitEquivData
      (Matrix.toLin' A).rangeRestrict br data)

/--
If the column-side range restriction is split as `[I 0]`, then the original
matrix inherits the Smith witness for its range inclusion.
-/
theorem hasSmithNormalForm_of_range_snf_and_splitBasis
    {R : Type u} [CommRing R]
    {m n r : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Fintype r] [DecidableEq r]
    (A : Matrix m n R)
    (br : Module.Basis r R (LinearMap.range (Matrix.toLin' A)))
    (hIncl :
      HasSmithNormalForm
        (LinearMap.toMatrix br (Pi.basisFun R m)
          (LinearMap.range (Matrix.toLin' A)).subtype))
    (split : SmithRangeSplitBasisData R A br) :
    HasSmithNormalForm A := by
  classical
  let Acol : Matrix m (r ⊕ split.kerIdx) R :=
    LinearMap.toMatrix br (Pi.basisFun R m)
        (LinearMap.range (Matrix.toLin' A)).subtype *
      LinearMap.toMatrix split.colBasis br (Matrix.toLin' A).rangeRestrict
  have hAcol_append :
      Acol =
        smithAppendZeroCols (κ := split.kerIdx)
          (LinearMap.toMatrix br (Pi.basisFun R m)
            (LinearMap.range (Matrix.toLin' A)).subtype) := by
    simp [Acol, split.rangeRestrict_matrix, matrix_mul_smithLeftProjection]
  have hAcol_smith : HasSmithNormalForm Acol := by
    rw [hAcol_append]
    exact hasSmithNormalForm_appendZeroCols (κ := split.kerIdx) hIncl
  let bStdCol := (Pi.basisFun R n).reindex split.colEquiv
  have hAcol_factor :
      LinearMap.toMatrix split.colBasis (Pi.basisFun R m) (Matrix.toLin' A) = Acol := by
    have hfactor :=
      linearMap_toMatrix_eq_range_subtype_mul_rangeRestrict
        (R := R) (bm := split.colBasis) (bn := Pi.basisFun R m)
        (f := Matrix.toLin' A) (br := br)
    exact hfactor
  have hAcol_basis :
      Acol =
        Matrix.reindex (Equiv.refl m) split.colEquiv A *
          bStdCol.toMatrix split.colBasis := by
    have hchange :
        LinearMap.toMatrix split.colBasis (Pi.basisFun R m) (Matrix.toLin' A) =
          LinearMap.toMatrix bStdCol (Pi.basisFun R m) (Matrix.toLin' A) *
            bStdCol.toMatrix split.colBasis := by
      simpa [bStdCol] using
        basis_change_toMatrix_eq_mul
          (R := R) bStdCol split.colBasis
          (Pi.basisFun R m) (Pi.basisFun R m) (Matrix.toLin' A)
    have hstd :
        LinearMap.toMatrix bStdCol (Pi.basisFun R m) (Matrix.toLin' A) =
          Matrix.reindex (Equiv.refl m) split.colEquiv A := by
      simpa [bStdCol] using
        toMatrix_reindex_standard_domain_eq_reindex A split.colEquiv
    rw [← hAcol_factor, hchange, hstd]
  have hReindexed :
      HasSmithNormalForm (Matrix.reindex (Equiv.refl m) split.colEquiv A) := by
    have hAcol_transport :
        Acol =
          (1 : Matrix m m R) * Matrix.reindex (Equiv.refl m) split.colEquiv A *
            bStdCol.toMatrix split.colBasis := by
      simpa [Matrix.mul_assoc] using hAcol_basis
    exact smith_transport_twoSidedUnits
      (1 : Matrix m m R) (bStdCol.toMatrix split.colBasis)
      (Matrix.reindex (Equiv.refl m) split.colEquiv A) Acol
      gaussInvertibleMatrix_one (gaussInvertibleMatrix_basis_toMatrix bStdCol split.colBasis)
      hAcol_transport hAcol_smith
  have hBack := smith_reindex (R := R) (m := m) (n := r ⊕ split.kerIdx)
    (m' := m) (n' := n) (Equiv.refl m) split.colEquiv.symm hReindexed
  simpa [Matrix.reindex_apply] using hBack

/--
Combine mathlib's Smith normal form for the range inclusion with split-product
column data for the range restriction.

This packages all already-verified matrix bridge pieces. The remaining PID
module-theory obligation is to construct the supplied `ProjectionSplitEquivData`
and the finite index equivalence for the original column module.
-/
theorem hasSmithNormalForm_of_basisSmithNormalForm_and_projectionSplit
    {R : Type u} [CommRing R]
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R)
    {rank : ℕ}
    (snf :
      Module.Basis.SmithNormalForm
        (LinearMap.range (Matrix.toLin' A)) m rank)
    (split :
      ProjectionSplitEquivData R (Matrix.toLin' A).rangeRestrict
        (snf.bN.reindex (pidSmithRankEquiv rank)))
    (colEquiv : n ≃ ULift.{u, 0} (Fin rank) ⊕ split.kerIdx) :
    HasSmithNormalForm A := by
  classical
  let br := snf.bN.reindex (pidSmithRankEquiv rank)
  have hIncl :
      HasSmithNormalForm
        (LinearMap.toMatrix br (Pi.basisFun R m)
          (LinearMap.range (Matrix.toLin' A)).subtype) := by
    simpa [br] using
      hasSmithNormalForm_subtype_matrix_of_basisSmithNormalForm
        (R := R) (M := (m → R)) (ι := m)
        (N := LinearMap.range (Matrix.toLin' A))
        (b := Pi.basisFun R m) (snf := snf)
  let splitData :=
    smithRangeSplitBasisData_of_projectionSplitEquivData
      (A := A) (br := br) split colEquiv
  exact hasSmithNormalForm_of_range_snf_and_splitBasis
    (A := A) (br := br) hIncl splitData

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
Higher-level PID bridge obligation reduced to the remaining column-side split
data for mathlib's range Smith normal form.
-/
structure PIDProjectionSplitBridge
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    Type (u + 1) where
  projectionSplit :
    ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
      [Fintype n] [DecidableEq n] [LinearOrder n],
      (A : Matrix m n R) →
        let snf :=
          pidSubmoduleSmithNormalForm R (m → R) m (Pi.basisFun R m)
            (LinearMap.range (Matrix.toLin' A))
        Σ split :
          ProjectionSplitEquivData R (Matrix.toLin' A).rangeRestrict
            (snf.2.bN.reindex (pidSmithRankEquiv snf.1)),
          n ≃ ULift.{u, 0} (Fin snf.1) ⊕ split.kerIdx

/--
A projection-split bridge discharges the matrix-level PID Smith bridge.
-/
theorem pidMatrixSmithBridge_of_projectionSplitBridge
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (bridge : PIDProjectionSplitBridge R) :
    PIDMatrixSmithBridge R where
  hasSmith := by
    intro m n _ _ _ _ _ _ A
    classical
    let snf :=
      pidSubmoduleSmithNormalForm R (m → R) m (Pi.basisFun R m)
        (LinearMap.range (Matrix.toLin' A))
    obtain ⟨split, colEquiv⟩ := bridge.projectionSplit A
    exact hasSmithNormalForm_of_basisSmithNormalForm_and_projectionSplit
      (A := A) (snf := snf.2) split colEquiv

/--
Construct the refined projection-split bridge over a PID.

This discharges the remaining column-side split and finite-index equivalence
using projectivity of the range basis, the PID basis theorem for the kernel,
and `Basis.indexEquiv` for the split product basis.
-/
noncomputable def pidProjectionSplitBridge
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    PIDProjectionSplitBridge R where
  projectionSplit := by
    intro m n _ _ _ _ _ _ A
    classical
    let snf :=
      pidSubmoduleSmithNormalForm R (m → R) m (Pi.basisFun R m)
        (LinearMap.range (Matrix.toLin' A))
    let br := snf.2.bN.reindex (pidSmithRankEquiv snf.1)
    let split := projectionSplitEquivDataOfRangeRestrictPid (A := A) br
    refine ⟨split, ?_⟩
    exact colEquivOfProjectionSplitEquivData (A := A) br split

/-- Matrix-level PID Smith bridge constructed from the verified projection-split bridge. -/
noncomputable def pidMatrixSmithBridge
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    PIDMatrixSmithBridge R :=
  pidMatrixSmithBridge_of_projectionSplitBridge (pidProjectionSplitBridge R)

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

/--
PID-scope matrix Smith theorem conditional on the refined projection-split
bridge obligation.
-/
theorem exists_smith_normal_form_projection_split_bridge
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (bridge : PIDProjectionSplitBridge R)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A :=
  exists_smith_normal_form_pid_bridge
    (pidMatrixSmithBridge_of_projectionSplitBridge bridge) A

/--
Public PID-scope Smith normal form theorem.

This theorem is unconditional over a PID. The field-only theorem remains under
the explicit field-specific names in `Smith.Existence`.
-/
theorem exists_smith_normal_form
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasSmithNormalForm A :=
  exists_smith_normal_form_pid_bridge (pidMatrixSmithBridge R) A

end MatDecompFormal.Instances
