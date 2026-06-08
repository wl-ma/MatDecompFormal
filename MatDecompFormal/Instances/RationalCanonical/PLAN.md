# Rational Canonical Form via the Descent Framework

This plan describes rational canonical form for finite-dimensional linear maps
over a field using the project descent-template style.

The theorem should not depend on `ℂ`. The natural scalar assumption is `[Field K]`.

## 1. Target Theorem

```lean
theorem exists_rational_canonical_form
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (T : V →ₗ[K] V) :
    ∃ b : Basis (Fin (FiniteDimensional.finrank K V)) K V,
      IsRationalCanonicalMatrix (LinearMap.toMatrix b b T)
```

Matrix-indexed variant:

```lean
theorem exists_rational_canonical_matrix
    {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    ∃ P : Matrix ι ι K, ∃ C : Matrix ι ι K,
      InvertibleMatrix P ∧
      IsRationalCanonicalMatrix C ∧
      A = P * C * P⁻¹
```

## 2. Algebraic Route

View `V` as a finitely generated torsion `K[X]`-module via:

```lean
X • v = T v
```

Then apply the PID module structure theorem over `K[X]`. The invariant factors
produce companion blocks.

Dependency direction:

```text
Smith / ModuleStructure over K[X] -> Rational canonical form
```

## 3. Descent Template Instantiation

### Universe

Options:

1. `LinearOperatorUniverse K` packaging a finite-dimensional `K`-space and
   linear map `T`;
2. square matrices over `K` up to similarity;
3. finitely generated torsion `K[X]`-modules with chosen generators.

The module universe is mathematically clean; the matrix universe may fit the
existing square driver more easily.

### Measure

Use `finrank K V` or `Fintype.card ι`.

### Predicate

`P T` means `T` has rational canonical form, equivalently a basis whose matrix
is block diagonal with companion matrices of invariant factors.

### Base

Zero-dimensional vector spaces have the empty canonical matrix.

### Transform

Similarity/change of basis:

```lean
B = P⁻¹ * A * P
```

or module isomorphism for the `K[X]`-module formulation.

### Readiness

A ready object has an isolated cyclic invariant summand with annihilator
polynomial `p`, plus a smaller invariant quotient/submodule.

### Slice

The complementary invariant quotient/submodule or the remaining block after
removing one companion block.

### Reach

Use module structure theorem to find a cyclic summand. Initially isolate this as
an oracle:

```lean
structure RationalCanonicalStepOracle (K V T) where
  cyclicSummand : ...
  slice : ...
  progress : finrank slice < finrank V
  ready : RationalCanonicalDescentReady ...
```

Then discharge it from PID module structure over `K[X]`.

### Transport

Canonical form is invariant under similarity/change of basis.

### Lift

A cyclic summand with annihilator `p` gives a companion block; combine it with
the recursive rational canonical form of the slice.

### Driver

If using matrices, reuse the square driver. If using modules/linear maps, add an
`AlgebraicDescentInstance` with the same fields as the template contract.

## 4. Required Lemmas

- `K[X]` is a PID for field `K`.
- Linear map to `K[X]`-module bridge.
- Cyclic module basis gives companion matrix.
- Direct sum of invariant subspaces gives block diagonal matrix.
- Similarity transport.
- Block lift for companion block plus tail rational canonical form.

## 5. File Layout

```text
MatDecompFormal/Instances/RationalCanonical/PLAN.md
MatDecompFormal/Instances/RationalCanonical.lean
MatDecompFormal/Instances/RationalCanonical/Details.lean
MatDecompFormal/Instances/RationalCanonical/Strategy.lean
MatDecompFormal/Instances/RationalCanonical/Direct.lean
MatDecompFormal/Instances/RationalCanonical/Existence.lean
```

## 6. Verification

```bash
lake build MatDecompFormal.Instances.RationalCanonical
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/RationalCanonical -S
```
