import Mathlib.RingTheory.Ideal.Quotient.Basic
import MatDecompFormal.Instances.Smith.Details

universe u v

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# PID Module Structure Details

The first formal target is the finite-presentation route from the plan.  A
presentation matrix has PID module structure when it is equivalent, by
two-sided invertible row/column transformations, to a Smith normal-form matrix.
This is the matrix-level content needed before adding a quotient-module API for
abstract finitely generated modules.
-/

variable {R : Type v} {rel gen : Type u}

/--
Matrix-level finite-presentation module-structure payload.

`rel` indexes relations and `gen` indexes generators.  The matrix presents the
cokernel of the relation map; Smith normal form records the free and cyclic
summand data.
-/
structure PIDModuleStructureData
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    (A : Matrix rel gen R) where
  P : Matrix rel rel R
  Q : Matrix gen gen R
  D : Matrix rel gen R
  invertible_P : GaussInvertibleMatrix P
  invertible_Q : GaussInvertibleMatrix Q
  smith_D : IsSmithNormalForm D
  equation : D = P * A * Q

/--
Preferred name for the presentation-level normal-form data carried by a
presentation matrix.

This is not the abstract PID module classification theorem; it only records
two-sided equivalence of a presentation matrix to strengthened Smith normal
form.
-/
abbrev PresentedPIDModuleStructureData
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    (A : Matrix rel gen R) :=
  PIDModuleStructureData A

/--
Finite-presentation module-structure predicate for the module presented by
`A`.  The current formal model keeps the presentation as its matrix; this alias
is the public API corresponding to the plan's `PresentedModule A` route.
-/
def HasPresentedPIDModuleStructure
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    (A : Matrix rel gen R) : Prop :=
  Nonempty (PresentedPIDModuleStructureData A)

/--
Compatibility name for older descent code.

Despite its historical name, this is still presentation-level data: a matrix is
equivalent to a Smith normal-form presentation.  Use
`HasPresentedPIDModuleStructure` in new public statements, and use
`PIDModuleDecomposition` for the full abstract module decomposition target.
-/
def HasPIDModuleStructure
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    (A : Matrix rel gen R) : Prop :=
  HasPresentedPIDModuleStructure A

@[simp] theorem hasPIDModuleStructure_iff
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {A : Matrix rel gen R} :
    HasPIDModuleStructure A ↔ HasPresentedPIDModuleStructure A :=
  Iff.rfl

theorem hasPresentedPIDModuleStructure_iff
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {A : Matrix rel gen R} :
    HasPresentedPIDModuleStructure A ↔ HasPIDModuleStructure A :=
  Iff.rfl

/--
Finite ordered invariant factors for a PID module decomposition.

The `order` field gives the linear order used by the divisibility chain.  This
mirrors the strengthened `SmithNormalFormData.divides_chain` payload instead of
the older unordered diagonal predicate.
-/
structure PIDInvariantFactorData (R : Type v) [Semiring R] where
  ι : Type u
  fintype_ι : Fintype ι
  order : Fin (Fintype.card ι) ≃ ι
  invariantFactor : ι → R
  divisibility_chain : ∀ k : Fin (Fintype.card ι),
    (hnext : (k : Nat) + 1 < Fintype.card ι) →
      invariantFactor (order k) ∣
        invariantFactor (order ⟨(k : Nat) + 1, hnext⟩)

attribute [instance] PIDInvariantFactorData.fintype_ι

namespace PIDInvariantFactorData

/-- Number of cyclic torsion summands encoded by the invariant-factor data. -/
def length [Semiring R] (torsionData : PIDInvariantFactorData.{u, v} R) : Nat :=
  Fintype.card torsionData.ι

/-- The invariant factor at an ordered position. -/
def orderedInvariantFactor [Semiring R]
    (torsionData : PIDInvariantFactorData.{u, v} R)
    (k : Fin torsionData.length) : R :=
  torsionData.invariantFactor (torsionData.order k)

/-- Forgetful accessor for the divisibility chain. -/
theorem orderedInvariantFactor_divides_next [Semiring R]
    (torsionData : PIDInvariantFactorData.{u, v} R)
    (k : Fin torsionData.length)
    (hnext : (k : Nat) + 1 < torsionData.length) :
    torsionData.orderedInvariantFactor k ∣
      torsionData.orderedInvariantFactor ⟨(k : Nat) + 1, hnext⟩ :=
  torsionData.divisibility_chain k hnext

/--
Extract invariant factors from the strengthened Smith normal-form data.  This
is the intended source of `torsionData` for presentation-level decompositions.
-/
noncomputable def ofSmithNormalFormData
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) :
    PIDInvariantFactorData R where
  ι := data.r
  fintype_ι := data.fintype_r
  order := data.order
  invariantFactor := data.diag
  divisibility_chain := data.divides_chain

/--
Extract invariant factors from the strengthened Smith predicate.  This uses
classical choice because `IsSmithNormalForm` is a proposition.
-/
noncomputable def ofSmithNormalForm
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (hD : IsSmithNormalForm D) :
    PIDInvariantFactorData R :=
  ofSmithNormalFormData (Classical.choice hD)

/--
Extend the ordered Smith invariant factors by a tail of zero factors.

A zero cyclic summand is `R/(0)`, hence represents one free coordinate while
keeping the target in the uniform product-of-cyclic-quotients shape.  This is
the quotient-model shape used for cokernels of rectangular Smith matrices:
diagonal invariant factors come first, followed by zero factors for generator
coordinates not hit by a Smith pivot.
-/
noncomputable def ofSmithNormalFormDataWithZeroTail
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) (zeroTail : Nat) :
    PIDInvariantFactorData R where
  ι := Fin (Fintype.card data.r + zeroTail)
  fintype_ι := inferInstance
  order := finCongr (Fintype.card_fin (Fintype.card data.r + zeroTail))
  invariantFactor := fun i =>
    if h : (i : Nat) < Fintype.card data.r then
      data.diag (data.order ⟨i, h⟩)
    else 0
  divisibility_chain := by
    intro k hnext
    by_cases hknext : (k : Nat) + 1 < Fintype.card data.r
    · have hk : (k : Nat) < Fintype.card data.r := Nat.lt_of_succ_lt hknext
      simpa [finCongr, hk, hknext] using
        data.divides_chain ⟨(k : Nat), hk⟩ hknext
    · by_cases hk : (k : Nat) < Fintype.card data.r
      · simp [finCongr, hk, hknext]
      · simp [finCongr, hk, hknext]

/--
Choice-based version of `ofSmithNormalFormDataWithZeroTail` from the Smith
normal-form predicate.
-/
noncomputable def ofSmithNormalFormWithZeroTail
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (hD : IsSmithNormalForm D) (zeroTail : Nat) :
    PIDInvariantFactorData R :=
  ofSmithNormalFormDataWithZeroTail (Classical.choice hD) zeroTail

end PIDInvariantFactorData

namespace SmithNormalFormData

/--
The coordinate submodule generated by the Smith diagonal factor in a generator
column.  Non-pivot generator columns get `⊥`, corresponding to a free
`R/(0)` quotient coordinate.
-/
noncomputable def columnSubmodule
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) (j : gen) :
    Submodule R R :=
  if h : ∃ k : data.r, data.col k = j then
    Ideal.span ({data.diag (Classical.choose h)} : Set R)
  else ⊥

@[simp] theorem columnSubmodule_col
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) (k : data.r) :
    data.columnSubmodule (data.col k) =
      Ideal.span ({data.diag k} : Set R) := by
  classical
  rw [columnSubmodule]
  have hExists : ∃ k' : data.r, data.col k' = data.col k := ⟨k, rfl⟩
  simp only [hExists, ↓reduceDIte]
  have hChoose :
      Classical.choose hExists = k :=
    data.col_injective (Classical.choose_spec hExists)
  rw [hChoose]

theorem columnSubmodule_eq_bot_of_not_col
    [CommRing R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {D : Matrix rel gen R} (data : SmithNormalFormData D) {j : gen}
    (hj : ∀ k : data.r, data.col k ≠ j) :
    data.columnSubmodule j = ⊥ := by
  classical
  rw [columnSubmodule]
  have hnot : ¬∃ k : data.r, data.col k = j := by
    rintro ⟨k, hk⟩
    exact hj k hk
  simp [hnot]

end SmithNormalFormData

/-- The cyclic summand `R / (d)` used in the PID module decomposition. -/
abbrev PIDCyclicSummand (R : Type v) [CommRing R] (d : R) :=
  R ⧸ Ideal.span ({d} : Set R)

/-- Free part of rank `freeRank` in the decomposition model. -/
abbrev PIDModuleFreePart (R : Type v) [CommRing R] (freeRank : Nat) :=
  Fin freeRank → R

/-- Finite product of cyclic torsion summands. -/
abbrev PIDModuleTorsionPart (R : Type v) [CommRing R]
    (torsionData : PIDInvariantFactorData.{u, v} R) :=
  ∀ i : torsionData.ι, PIDCyclicSummand R (torsionData.invariantFactor i)

/--
The explicit module on the right-hand side of the PID structure theorem:
`R^freeRank` times the finite torsion product `∏ᵢ R/(dᵢ)`.
-/
abbrev PIDModuleDecompositionModel (R : Type v) [CommRing R]
    (freeRank : Nat) (torsionData : PIDInvariantFactorData.{u, v} R) :=
  PIDModuleFreePart R freeRank × PIDModuleTorsionPart R torsionData

/--
Actual PID module decomposition witness data for an abstract module.

This is the full module-level target: an isomorphism from `M` to a free part
plus cyclic torsion summands whose invariant factors satisfy the strengthened
Smith divisibility chain.
-/
structure PIDModuleDecompositionData (R : Type v) (M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M]
    (freeRank : Nat) (torsionData : PIDInvariantFactorData.{u, v} R) where
  decompositionIso :
    M ≃ₗ[R] PIDModuleDecompositionModel R freeRank torsionData

/--
Actual PID module decomposition proposition for an abstract module.

The proposition is intentionally a `Nonempty` wrapper around
`PIDModuleDecompositionData`, so theorem statements can use the usual
`∃ freeRank torsionData, PIDModuleDecomposition R M freeRank torsionData`
shape while still carrying an isomorphism witness internally.
-/
def PIDModuleDecomposition (R : Type v) (M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M]
    (freeRank : Nat) (torsionData : PIDInvariantFactorData.{u, v} R) : Prop :=
  Nonempty (PIDModuleDecompositionData R M freeRank torsionData)

namespace PIDModuleDecomposition

variable [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
variable {freeRank : Nat} {torsionData : PIDInvariantFactorData.{u, v} R}

/-- Extract witness data from the decomposition proposition. -/
noncomputable def data
    (decomp : PIDModuleDecomposition R M freeRank torsionData) :
    PIDModuleDecompositionData R M freeRank torsionData :=
  Classical.choice decomp

/-- Extract the linear equivalence carried by a decomposition proposition. -/
noncomputable def decompositionIso
    (decomp : PIDModuleDecomposition R M freeRank torsionData) :
    M ≃ₗ[R] PIDModuleDecompositionModel R freeRank torsionData :=
  decomp.data.decompositionIso

/-- Forget the decomposition to its free rank. -/
def freeRankOf
    (_decomp : PIDModuleDecomposition R M freeRank torsionData) : Nat :=
  freeRank

/-- Forget the decomposition to its ordered invariant-factor data. -/
def torsionDataOf
    (_decomp : PIDModuleDecomposition R M freeRank torsionData) :
    PIDInvariantFactorData R :=
  torsionData

/-- The invariant factor indexed by a torsion summand. -/
def invariantFactor
    (_decomp : PIDModuleDecomposition R M freeRank torsionData)
    (i : torsionData.ι) : R :=
  torsionData.invariantFactor i

/-- The cyclic summand indexed by `i`. -/
abbrev cyclicSummand
    (_decomp : PIDModuleDecomposition R M freeRank torsionData)
    (i : torsionData.ι) :=
  PIDCyclicSummand R (torsionData.invariantFactor i)

/-- The ordered invariant-factor divisibility chain carried by the decomposition. -/
theorem invariantFactor_divides_next
    (_decomp : PIDModuleDecomposition R M freeRank torsionData)
    (k : Fin torsionData.length)
    (hnext : (k : Nat) + 1 < torsionData.length) :
    torsionData.orderedInvariantFactor k ∣
      torsionData.orderedInvariantFactor ⟨(k : Nat) + 1, hnext⟩ :=
  torsionData.orderedInvariantFactor_divides_next k hnext

end PIDModuleDecomposition

/--
Bridge/oracle for the abstract finitely generated PID module theorem.

The current project has the Smith normal-form side and presentation-level
payload, but not yet the finite-presentation/cokernel bridge for arbitrary
modules.  This structure isolates exactly that missing input.
-/
structure PIDModuleDecompositionBridge (R : Type v) (M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M] where
  freeRank : Nat
  torsionData : PIDInvariantFactorData.{u, v} R
  decomposition : PIDModuleDecomposition R M freeRank torsionData

namespace PIDModuleDecompositionBridge

variable [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- A bridge immediately supplies the sigma-form existence statement. -/
theorem exists_decomposition (bridge : PIDModuleDecompositionBridge R M) :
    ∃ freeRank torsionData,
      PIDModuleDecomposition R M freeRank torsionData :=
  ⟨bridge.freeRank, bridge.torsionData, bridge.decomposition⟩

end PIDModuleDecompositionBridge

/-- Universe-level predicate used by the rectangular descent driver. -/
def ModuleStructure_P [Semiring R] (x : RectUniverse R) : Prop :=
  HasPIDModuleStructure x.A

def ModuleStructure_P_sub [Semiring R] (x_sub : PosRectUniverse R) : Prop :=
  ModuleStructure_P (x_sub : RectUniverse R)

@[simp] theorem moduleStructure_P_compat [Semiring R] (x_sub : PosRectUniverse R) :
    ModuleStructure_P_sub x_sub ↔ ModuleStructure_P (x_sub : RectUniverse R) :=
  Iff.rfl

/-- Smith normal form immediately gives the presentation-level structure data. -/
theorem hasPIDModuleStructure_of_smith
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {A : Matrix rel gen R} (hA : HasSmithNormalForm A) :
    HasPIDModuleStructure A := by
  rcases hA with ⟨P, Q, D, hP, hQ, hD, hEq⟩
  exact ⟨{
    P := P
    Q := Q
    D := D
    invertible_P := hP
    invertible_Q := hQ
    smith_D := hD
    equation := hEq
  }⟩

/-- Module-structure data forgets back to Smith normal-form equivalence. -/
theorem smith_of_hasPIDModuleStructure
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {A : Matrix rel gen R} (hA : HasPIDModuleStructure A) :
    HasSmithNormalForm A := by
  rcases hA with ⟨data⟩
  exact ⟨data.P, data.Q, data.D, data.invertible_P, data.invertible_Q,
    data.smith_D, data.equation⟩

/-- Presentation-level data exposes the invariant factors from its Smith payload. -/
noncomputable def PIDModuleStructureData.torsionData
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {A : Matrix rel gen R} (data : PIDModuleStructureData A) :
    PIDInvariantFactorData R :=
  PIDInvariantFactorData.ofSmithNormalForm data.smith_D

/--
Presentation-level invariant factors extended with zero factors for generator
coordinates not represented by Smith diagonal pivots.

The zero tail is the ingredient needed to model the full cokernel of a
rectangular presentation matrix as a product of cyclic quotients.
-/
noncomputable def PIDModuleStructureData.torsionDataWithGeneratorZeroTail
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {A : Matrix rel gen R} (data : PIDModuleStructureData A) :
    PIDInvariantFactorData R :=
  let smithData := Classical.choice data.smith_D
  PIDInvariantFactorData.ofSmithNormalFormDataWithZeroTail smithData
    (Fintype.card gen - Fintype.card smithData.r)

/-- Zero presentation matrices have module-structure data. -/
theorem hasPIDModuleStructure_zero
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen] :
    HasPIDModuleStructure (0 : Matrix rel gen R) :=
  hasPIDModuleStructure_of_smith hasSmithNormalForm_zero

/-- Base witness for presentation matrices with empty relation index type. -/
theorem base_moduleStructure_empty_rows
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    [IsEmpty rel] (A : Matrix rel gen R) :
    HasPIDModuleStructure A :=
  hasPIDModuleStructure_of_smith (base_smith_empty_rows A)

/-- Base witness for presentation matrices with empty generator index type. -/
theorem base_moduleStructure_empty_cols
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    [IsEmpty gen] (A : Matrix rel gen R) :
    HasPIDModuleStructure A :=
  hasPIDModuleStructure_of_smith (base_smith_empty_cols A)

/-- Transport module-structure data across a two-sided invertible equivalence. -/
theorem moduleStructure_transport_twoSidedUnits
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    (P₀ : Matrix rel rel R) (Q₀ : Matrix gen gen R)
    (A B : Matrix rel gen R)
    (hP₀ : GaussInvertibleMatrix P₀) (hQ₀ : GaussInvertibleMatrix Q₀)
    (hB : B = P₀ * A * Q₀)
    (hNF : HasPIDModuleStructure B) :
    HasPIDModuleStructure A := by
  subst B
  rcases hNF with ⟨data⟩
  exact ⟨{
    P := data.P * P₀
    Q := Q₀ * data.Q
    D := data.D
    invertible_P := data.invertible_P.mul hP₀
    invertible_Q := hQ₀.mul data.invertible_Q
    smith_D := data.smith_D
    equation := by
      calc
        data.D = data.P * (P₀ * A * Q₀) * data.Q := data.equation
        _ = (data.P * P₀) * A * (Q₀ * data.Q) := by simp [Matrix.mul_assoc]
  }⟩

/-- Reindexing preserves presentation-level module-structure data. -/
theorem hasPIDModuleStructure_reindex
    [Semiring R] {rel' gen' : Type u}
    [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    [Fintype rel'] [DecidableEq rel'] [Fintype gen'] [DecidableEq gen']
    (er : rel ≃ rel') (eg : gen ≃ gen') {A : Matrix rel gen R}
    (hA : HasPIDModuleStructure A) :
    HasPIDModuleStructure (Matrix.reindex er eg A) := by
  rcases hA with ⟨data⟩
  exact ⟨{
    P := Matrix.reindex er er data.P
    Q := Matrix.reindex eg eg data.Q
    D := Matrix.reindex er eg data.D
    invertible_P := gaussInvertibleMatrix_reindex er data.invertible_P
    invertible_Q := gaussInvertibleMatrix_reindex eg data.invertible_Q
    smith_D := isSmithNormalForm_reindex er eg data.smith_D
    equation := by
      have hEq := congrArg (Matrix.reindex er eg) data.equation
      simpa [Matrix.submatrix_mul_equiv, Matrix.mul_assoc] using hEq
  }⟩

theorem moduleStructure_reindex
    [Semiring R] {rel' gen' : Type u}
    [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    [Fintype rel'] [DecidableEq rel'] [Fintype gen'] [DecidableEq gen']
    (er : rel ≃ rel') (eg : gen ≃ gen') {A : Matrix rel gen R}
    (hA : HasPIDModuleStructure A) :
    HasPIDModuleStructure (Matrix.reindex er eg A) :=
  hasPIDModuleStructure_reindex er eg hA

end MatDecompFormal.Instances
