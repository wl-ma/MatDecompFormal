# LU Decomposition via the Descent Framework

This plan describes LU decomposition without pivoting, using the same project
descent-template style as PLU.

LU is not available for every square matrix without row permutation. The final
public theorem therefore exposes a determinant-style no-zero-pivot condition,
proved equivalent to the recursive pivot-readiness predicate used internally by
the descent driver. PLU remains the unconditional pivoting theorem.

## 1. Target Theorems

Public no-pivot LU theorem:

```lean
theorem exists_lu
    {R ι : Type*} [Field R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : HasNoZeroLUPivots A) :
    HasLU A
```

`HasNoZeroLUPivots A` is the preferred public-facing hypothesis: at every
no-pivot Schur-complement descent step, the current `1 × 1` leading pivot has
nonzero determinant. This is not merely a name wrapper; the API proves

```lean
theorem hasNoZeroLUPivots_iff_recursivePivotReady :
    HasNoZeroLUPivots A ↔ LURecursivePivotReady A
```

The theorem uses this determinant-style condition and crosses to
`LURecursivePivotReady` only through this equivalence. The determinant-style
criterion is also proved equivalent to the Schur-descendant API:

```lean
theorem hasNoZeroLUPivots_iff_nonzeroLUSchurPivots :
    HasNoZeroLUPivots A ↔ HasNonzeroLUSchurPivots A

theorem exists_lu_of_noZeroPivots
    {R ι : Type*} [Field R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : HasNoZeroLUPivots A) :
    HasLU A
```

The Schur-descendant theorem remains available as an implementation-facing
public criterion over `[DivisionRing R]`:

```lean
theorem exists_lu_of_nonzeroLUSchurPivots
    {R ι : Type*} [DivisionRing R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : HasNonzeroLUSchurPivots A) :
    HasLU A
```

The compatibility theorem below is kept for implementation-oriented users and
preserves the weakest direct driver-facing assumption:

```lean
theorem exists_lu_of_noPivotReady
    {R ι : Type*} [DivisionRing R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : LURecursivePivotReady A) :
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

`P x := LURecursivePivotReady x.A → HasLU x.A` internally. Public theorems use
`HasNoZeroLUPivots x.A → HasLU x.A` and the proved equivalence

```lean
HasNoZeroLUPivots A ↔ LURecursivePivotReady A
```

to feed the driver.
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
- Pivot Schur-complement step needs subtraction and inverses, so the internal
  recursive theorem uses `[DivisionRing R]`.
- The main public determinant criterion uses `[Field R]`, since determinants
  require commutativity.
- The Schur-descendant criterion remains available over `[DivisionRing R]` when
  avoiding commutativity is more important than determinant-style readability.

Do not specialize to `ℝ` or `ℂ`.

## 5. File Layout

```text
MatDecompFormal/Instances/LU/PLAN.md
MatDecompFormal/Instances/LU.lean
MatDecompFormal/Instances/LU/Details.lean
MatDecompFormal/Instances/LU/Strategy.lean
MatDecompFormal/Instances/LU/Direct.lean
MatDecompFormal/Instances/LU/Existence.lean
MatDecompFormal/Instances/LU/NonrecursiveCriterion.lean
```

## 6. Implementation Order

1. Define `LU_Schema` and `HasLU`.
2. Prove trivial base cases.
3. Define recursive no-pivot readiness and determinant no-pivot criterion.
4. Reuse PLU pivot Schur-slice helpers where possible.
5. Build identity-transform square strategy core.
6. Prove LU block lift.
7. Prove the Schur-descendant criterion is equivalent to recursive pivot
   readiness.
8. Prove the determinant criterion is equivalent to the Schur-descendant
   criterion for fields.
9. Assemble the framework-routed internal theorem and public theorems stated in
   the non-internal criteria.

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
