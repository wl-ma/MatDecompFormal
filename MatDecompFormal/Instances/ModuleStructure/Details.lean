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

/-- Predicate for the finite-presentation module-structure theorem. -/
def HasPIDModuleStructure
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    (A : Matrix rel gen R) : Prop :=
  Nonempty (PIDModuleStructureData A)

/--
Finite-presentation module-structure predicate for the module presented by
`A`.  The current formal model keeps the presentation as its matrix; this alias
is the public API corresponding to the plan's `PresentedModule A` route.
-/
def HasPresentedPIDModuleStructure
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    (A : Matrix rel gen R) : Prop :=
  HasPIDModuleStructure A

@[simp] theorem hasPresentedPIDModuleStructure_iff
    [Semiring R] [Fintype rel] [DecidableEq rel] [Fintype gen] [DecidableEq gen]
    {A : Matrix rel gen R} :
    HasPresentedPIDModuleStructure A ↔ HasPIDModuleStructure A :=
  Iff.rfl

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
