# PID Module Structure Theorem via the Descent Framework

This plan describes how to formalize the structure theorem for finitely
generated modules over a PID using the project descent-template style.

The theorem is algebraic, not analytic. It should not depend on `ℝ` or `ℂ`.

## 1. Target Theorems

The current formal target is the finite-presentation route. It connects directly
to the rectangular descent driver and Smith normal form. The final theorem must
not be stated as a field theorem when the intended algebra is PID structure.

Internal descent-level PID bridge:

```lean
structure PIDModuleStructureStepBridge
    (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] where
  stepOracle : ∀ {rel gen}, ..., ModuleStructureStepOracle R rel gen
```

This bridge is retained only for the recursive descent-template entry point:

```lean
theorem exists_presented_pid_module_structure_step_bridge
    {R rel gen : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (bridge : PIDModuleStructureStepBridge R)
    [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPresentedPIDModuleStructure A
```

Public presentation theorem:

```lean
theorem exists_presented_pid_module_structure
    {R rel gen : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPresentedPIDModuleStructure A
```

Underlying matrix theorem:

```lean
theorem exists_structure_of_presentation
    {R rel gen : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPIDModuleStructure A
```

In code this matrix-level theorem is named `exists_structure_of_presentation_pid`.
It is unconditional at the ModuleStructure layer because it routes through the
public PID Smith normal-form theorem.  The module-structure theorem itself no
longer exposes the low-level one-step descent oracle as its public dependency.
Currently this public theorem follows the Smith theorem's same-universe shape
for `R`, `rel`, and `gen`; the separate `*_step_bridge` theorem keeps the
rectangular descent framework available for mixed-universe internal use.

The concrete field specialization, where the bridge/oracle is discharged through
Gauss rank normal form, is named:

```lean
theorem exists_presented_module_structure_field
    {R rel gen : Type*} [Field R]
    [Fintype rel] [DecidableEq rel] [LinearOrder rel]
    [Fintype gen] [DecidableEq gen] [LinearOrder gen]
    (A : Matrix rel gen R) :
    HasPresentedPIDModuleStructure A
```

The abstract finitely generated module theorem remains the intended corollary
after adding a quotient/free-presentation API:

```lean
theorem exists_pid_module_structure
    {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ F T, ModuleStructureDecomposition R M F T
```

There is also a framework theorem conditional on a Smith one-step oracle and
without PID assumptions:

```lean
theorem exists_structure_of_presentation_oracle
    (oracle : ∀ ..., ModuleStructureStepOracle R rel gen)
    (A : Matrix rel gen R) :
    HasPIDModuleStructure A
```

The desired abstract finitely generated module theorem would then add a
quotient/free-presentation API and apply the finite-presentation theorem above:

```lean
theorem exists_pid_module_structure
    {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ F T, ModuleStructureDecomposition R M F T
```

## 2. Algebraic Assumptions

Keep assumptions layered:

- definitions over `[CommRing R]` where possible;
- decomposition theorem over PID or Euclidean domain first;
- no `ℝ`/`ℂ` specialization unless stated as an example.

## 3. Descent Template Instantiation

### Universe

Use one of these universes:

1. finite presentation matrices `Matrix r g R`;
2. finitely generated modules with a chosen finite generating set;
3. finitely generated torsion modules plus free rank data.

The first is recommended because Smith normal form gives a concrete descent
engine. This is the implemented universe.

### Measure

For presentation matrices:

```lean
μ A = min (Fintype.card r) (Fintype.card g)
```

For abstract modules, use number of generators plus torsion complexity. Keep the
abstract theorem as a corollary of the presentation route.

### Predicate

`P A` means the presented module decomposes as a direct sum of a free part and
cyclic torsion factors with divisibility chain. In the current matrix-level API:

```lean
def HasPIDModuleStructure (A : Matrix rel gen R) : Prop :=
  Nonempty (PIDModuleStructureData A)
```

where `PIDModuleStructureData A` records invertible presentation changes and a
Smith normal-form matrix `D = P * A * Q`.

`HasPresentedPIDModuleStructure A` is the public alias for this matrix-backed
finite-presentation predicate. It corresponds to the `PresentedModule A` route
without committing to a quotient-module API in this file.

### Base

Empty relation or generator side gives a free/zero module with immediate
structure decomposition.

### Transform

Allowed transforms are invertible row and column operations on presentation
matrices:

```lean
B = P * A * Q
```

where `P`, `Q` are invertible over `R`.

### Readiness

Smith-ready presentation matrix:

1. head pivot isolated;
2. head row and column zero away from pivot;
3. pivot divides all entries in the tail block.

### Slice

Lower-right presentation matrix.

### Reach

Use a `SmithStepOracle` initially, then discharge via Euclidean/PID Smith
reduction. The current concrete field theorem discharges this oracle through
the Gauss rank-normal-form oracle and `smithStepOracleOfGauss`.

### Transport

Invertible row/column operations preserve the presented module up to isomorphism,
so the structure predicate transports backward. Implemented as
`moduleStructure_transport_twoSidedUnits`.

### Lift

A Smith-ready pivot gives one cyclic/free summand, and the recursive tail
structure supplies the rest. Pivot divisibility preserves the invariant-factor
chain. Implemented by converting the recursive tail module-structure witness to
a Smith witness, applying `smith_of_blockReady_reindex`, and converting back.

### Driver

Use the rectangular matrix driver if the universe is presentations. If using
abstract modules, introduce an `AlgebraicDescentInstance` with the same fields as
this contract.

## 4. Relation to Smith Normal Form

The module structure theorem should depend on Smith normal form or share its
step oracle. Prefer this dependency direction:

```text
Smith normal form -> PID module structure theorem
```

Do not duplicate the PID pivot-reduction proof in both instances.

The implementation follows this: `ModuleStructureStepOracle` is an alias of
`SmithStepOracle`, and the field-level concrete theorem uses
`smithStepOracleOfGauss`.

## 5. File Layout

```text
MatDecompFormal/Instances/ModuleStructure/PLAN.md
MatDecompFormal/Instances/ModuleStructure.lean
MatDecompFormal/Instances/ModuleStructure/Details.lean
MatDecompFormal/Instances/ModuleStructure/Strategy.lean
MatDecompFormal/Instances/ModuleStructure/Direct.lean
MatDecompFormal/Instances/ModuleStructure/Existence.lean
```

## 6. Verification

```bash
lake build MatDecompFormal.Instances.ModuleStructure
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/ModuleStructure -S
```
