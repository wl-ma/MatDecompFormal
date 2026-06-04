# Jordan Form via the Descent Framework

This plan describes Jordan form using the project descent-template style.

The main theorem should not be specialized to `ℂ`. Use a field `K` together
with a splitting hypothesis for the specific operator. An algebraically closed
field theorem can be a corollary.

## 1. Target Theorems

Split-polynomial theorem:

```lean
theorem exists_jordan_form_of_splits
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (T : V →ₗ[K] V)
    (hsplit : T.charpoly.Splits (RingHom.id K)) :
    ∃ b : Basis (Fin (FiniteDimensional.finrank K V)) K V,
      IsJordanMatrix (LinearMap.toMatrix b b T)
```

Matrix variant:

```lean
theorem exists_jordan_matrix_of_splits
    {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    ∃ P : Matrix ι ι K, ∃ J : Matrix ι ι K,
      InvertibleMatrix P ∧
      IsJordanMatrix J ∧
      A = P * J * P⁻¹
```

Algebraically closed corollary:

```lean
theorem exists_jordan_form
    {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : V →ₗ[K] V) : ...
```

## 2. Algebraic Route

Two acceptable routes:

1. Rational canonical form plus splitting of invariant factors into powers of
   linear factors, then convert companion blocks into Jordan blocks.
2. Primary decomposition plus nilpotent Jordan-chain descent on each generalized
   eigenspace.

Preferred dependency direction:

```text
ModuleStructure -> RationalCanonical -> Jordan
```

but the nilpotent chain descent can be developed directly if it better matches
mathlib APIs.

## 3. Descent Template Instantiation

### Universe

Use a linear-operator universe carrying:

- field `K`;
- finite-dimensional `K`-space `V`;
- linear operator `T`;
- splitting evidence for `charpoly T` when needed.

For primary/nilpotent descent, use sub-universes for a fixed eigenvalue and a
nilpotent operator on a finite-dimensional space.

### Measure

Use `finrank K V`. For nilpotent-chain descent, optionally pair it with the
nilpotency index.

### Predicate

`P T` means `T` has a Jordan basis/Jordan matrix.

### Base

Zero-dimensional spaces and zero nilpotent spaces have the empty Jordan form.

### Transform

Similarity/change of basis, or invariant-subspace decomposition isomorphism.

### Readiness

Depending on route:

- rational route: invariant factors are split into linear powers;
- nilpotent route: a maximal Jordan chain has been isolated;
- primary route: one generalized eigenspace or one Jordan block is isolated.

### Slice

The invariant quotient/complement after removing one Jordan block or one primary
component.

### Reach

Initially use explicit step oracles:

```lean
structure JordanStepOracle (K V T hsplit) where
  block : JordanBlockData K V T
  slice : JordanUniverse K
  progress : finrank slice < finrank V
  ready : JordanDescentReady ...
```

Then discharge via rational canonical form or primary decomposition/nilpotent
chain lemmas.

### Transport

Jordan form is invariant under similarity/change of basis.

### Lift

Add one Jordan block or one primary-component Jordan decomposition to the tail
block using block diagonal assembly.

### Driver

Use an `AlgebraicDescentInstance` if the square matrix driver is too restrictive.
The final theorem must be assembled by this driver.

## 4. Required Lemmas

- Similarity transport for Jordan form.
- Block diagonal lift of Jordan matrices.
- Splitting of primary components under `charpoly.Splits`.
- Nilpotent operator has a Jordan chain decomposition.
- Companion block for `(X - λ)^k` is similar to a Jordan block.
- Basis/direct-sum to block-matrix bridge.

## 5. File Layout

```text
MatDecompFormal/Instances/Jordan/PLAN.md
MatDecompFormal/Instances/Jordan.lean
MatDecompFormal/Instances/Jordan/Details.lean
MatDecompFormal/Instances/Jordan/Strategy.lean
MatDecompFormal/Instances/Jordan/Direct.lean
MatDecompFormal/Instances/Jordan/Existence.lean
```

## 6. Verification

```bash
lake build MatDecompFormal.Instances.Jordan
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Jordan -S
```
