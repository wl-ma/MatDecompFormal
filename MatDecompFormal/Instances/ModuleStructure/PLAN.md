# PID Module Structure Theorem via the Descent Framework

This plan describes how to formalize the structure theorem for finitely
generated modules over a PID using the project descent-template style.

The theorem is algebraic, not analytic. It should not depend on `ℝ` or `ℂ`.

## 1. Target Theorems

A practical first target should be stated for finitely generated modules over a
PID, with finite presentation data if that is easier to connect to Smith normal
form.

```lean
theorem exists_pid_module_structure
    {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ F T, ModuleStructureDecomposition R M F T
```

A more concrete theorem may use an explicit finite presentation matrix and
Smith normal form:

```lean
theorem exists_structure_of_presentation
    {R g r : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Fintype g] [DecidableEq g] [LinearOrder g]
    [Fintype r] [DecidableEq r] [LinearOrder r]
    (A : Matrix r g R) :
    HasPIDModuleStructure (PresentedModule A)
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
engine.

### Measure

For presentation matrices:

```lean
μ A = min (Fintype.card r) (Fintype.card g)
```

For abstract modules, use number of generators plus torsion complexity. If this
is too hard, keep the abstract theorem as a corollary of the presentation route.

### Predicate

`P A` means the presented module decomposes as a direct sum of a free part and
cyclic torsion factors with divisibility chain.

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
reduction.

### Transport

Invertible row/column operations preserve the presented module up to isomorphism,
so the structure predicate transports backward.

### Lift

A Smith-ready pivot gives one cyclic/free summand, and the recursive tail
structure supplies the rest. Pivot divisibility preserves the invariant-factor
chain.

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
