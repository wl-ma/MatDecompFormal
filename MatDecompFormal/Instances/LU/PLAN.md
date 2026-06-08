# LU Decomposition via the Descent Framework

This plan describes LU decomposition without pivoting, using the same project
descent-template style as PLU.

LU is not available for every square matrix over a division ring without row
permutation. The final theorem must therefore expose an appropriate readiness
condition, such as nonzero recursive pivots or nonzero leading principal minors.
PLU remains the unconditional pivoting theorem.

## 1. Target Theorems

Conditional no-pivot LU theorem:

```lean
theorem exists_lu_of_noPivotReady
    {R ι : Type*} [DivisionRing R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : LURecursivePivotReady A) :
    HasLU A
```

Eventually, add equivalent criterion theorem:

```lean
theorem exists_lu_of_leadingPrincipalMinors
    {R ι : Type*} [Field R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : AllLeadingPrincipalMinorsNonzero A) :
    HasLU A
```

The unconditional PLU theorem should not be weakened into LU; LU must retain its
extra no-pivot hypothesis.

## 2. Predicate

Use the same triangular predicates as PLU:

```lean
def LU_Schema : DecompositionSchema ι ι R where
  Factors := Matrix ι ι R × Matrix ι ι R
  property := fun (L, U) =>
    IsUnitLowerTriangular L ∧ IsUpperTriangular U
  equation := fun A (L, U) => A = L * U
```

## 3. Descent Template Instantiation

### Universe

Square matrices over `R`:

```lean
SquareUniverse R
```

### Measure

```lean
μ x = Fintype.card x.ι
```

### Predicate

`P x := LURecursivePivotReady x.A → HasLU x.A`, or alternatively package
readiness into the universe.

### Base

Empty/subsingleton matrices have trivial LU: `A = 1 * A`.

### Transform

No row permutation is allowed. The transformation is identity.

### Readiness

The head pivot must be nonzero:

```lean
A head head ≠ 0
```

and the Schur complement must recursively satisfy the readiness predicate.

### Slice

Schur complement of the head pivot, same formula as PLU pivot branch:

```lean
A₂₂ - A₂₁ * A₁₁⁻¹ * A₁₂
```

### Reach

For LU, reach is supplied by the assumption `LURecursivePivotReady`; unlike PLU,
there is no pivot-to-head transformation.

### Transport

Identity transport only.

### Lift

If the Schur complement has LU, assemble:

```lean
L = fromBlocks 1 0 L₂₁ Ltail
U = fromBlocks A₁₁ A₁₂ 0 Utail
```

where `L₂₁ = A₂₁ * A₁₁⁻¹`.

### Driver

Use the square decomposition driver. If expressing recursive readiness as an
input predicate does not fit the current driver directly, add a small LU-specific
strategy data wrapper with `P x := Ready x -> HasLU x`.

## 4. Algebraic Assumptions

- Basic schema and base cases only need `[Semiring R]`.
- Pivot Schur-complement step needs subtraction and inverses, so use
  `[DivisionRing R]` initially.
- A commutative `[Field R]` assumption is only needed for determinant/leading
  principal minor criteria.

Do not specialize to `ℝ` or `ℂ`.

## 5. File Layout

```text
MatDecompFormal/Instances/LU/PLAN.md
MatDecompFormal/Instances/LU.lean
MatDecompFormal/Instances/LU/Details.lean
MatDecompFormal/Instances/LU/Strategy.lean
MatDecompFormal/Instances/LU/Direct.lean
MatDecompFormal/Instances/LU/Existence.lean
```

## 6. Implementation Order

1. Define `LU_Schema` and `HasLU`.
2. Prove trivial base cases.
3. Define recursive no-pivot readiness.
4. Reuse PLU pivot Schur-slice helpers where possible.
5. Build identity-transform square strategy core.
6. Prove LU block lift.
7. Assemble framework-routed conditional theorem.
8. Add leading-principal-minor criterion as a later corollary.

## Descent Template Contract

This plan is required to use the project descent template. The implementation
must explicitly instantiate `Universe`, `μ`, `P`, `base`, `transform`,
`readiness`, `slice`, `reach`, `transport`, `lift`, `driver`, and `final theorem`.
The final theorem must be obtained from the driver, not from a direct-only proof.

## 7. Verification

```bash
lake build MatDecompFormal.Instances.LU
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/LU -S
```
