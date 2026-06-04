# UTV Decomposition via the Descent Framework

This plan describes how to formalize UTV-style decompositions using the project
rectangular descent template while keeping algebraic assumptions layered.

There are two useful variants:

1. a generic two-sided equivalence over a field with invertible row/column
   factors;
2. a unitary UTV factorization over `RCLike` scalars.

The generic theorem should come first unless the intended numerical UTV theorem
specifically requires unitary factors.

## 1. Target Theorems

Generic rectangular triangular equivalence over a field:

```lean
theorem exists_triangular_equivalence
    {R m n : Type*} [Field R]
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    ∃ P : Matrix m m R, ∃ Q : Matrix n n R, ∃ T : Matrix m n R,
      InvertibleMatrix P ∧
      InvertibleMatrix Q ∧
      IsRectangularUpperTriangular T ∧
      A = P * T * Q
```

Unitary UTV corollary over `RCLike`:

```lean
theorem exists_utv
    {𝕜 m n : Type*} [RCLike 𝕜]
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) :
    ∃ U : Matrix m m 𝕜, ∃ V : Matrix n n 𝕜, ∃ T : Matrix m n 𝕜,
      IsUnitaryMatrix U ∧
      IsUnitaryMatrix V ∧
      IsRectangularUpperTriangular T ∧
      A = U * T * Vᴴ
```

## 2. Middle-Factor Predicate

Define rectangular upper triangularity generically:

```lean
def IsRectangularUpperTriangular
    {R m n : Type*} [Zero R] [LinearOrder m] [LinearOrder n]
    (T : Matrix m n R) : Prop :=
  ∀ i j, rowRank i > colRank j → T i j = 0
```

For arbitrary finite index types, the head-tail recursive predicate may be more
robust: lower-left block zero and tail block rectangular upper triangular.

## 3. Descent Shape

For nonempty row and column types:

1. Split rows and columns by head-tail equivalences.
2. Transform to a ready matrix.
3. Ready means lower-left block is zero after reindexing:

   ```lean
   B'.toBlocks₂₁ = 0
   ```

4. Recurse on `B'.toBlocks₂₂`.
5. Lift using block-diagonal invertible extensions.
6. For the unitary corollary, use block-diagonal unitary extensions.

## 4. Framework Mapping

### Transformation

Generic:

```lean
B = P * A * Q
```

with `P`, `Q` invertible. Unitary corollary:

```lean
B = Uᴴ * A * V
```

### Reduction

Use rectangular lower-right submatrix reduction:

```lean
slice B = B.toBlocks₂₂
```

### Measure

Use the SVD rectangular measure:

```lean
min (Fintype.card m) (Fintype.card n)
```

## 5. Required Lemmas

- Generic `InvertibleMatrix` helpers.
- `IsRectangularUpperTriangular` base cases and reindex invariance.
- Generic two-sided invertible transport.
- Optional two-sided unitary transport, reusable from SVD.
- Block lift from lower-left-zero block shape.
- Generic field-level row/column elimination step.
- Optional Householder/Givens step over `RCLike`.

Initial generic oracle:

```lean
structure UTVStepOracle
    (R m n : Type*) [Field R]
    [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  P : Matrix m n R → Matrix m m R
  Q : Matrix m n R → Matrix n n R
  invertible_P : ∀ A, InvertibleMatrix (P A)
  invertible_Q : ∀ A, InvertibleMatrix (Q A)
  ready : ∀ A, UTVDescentReady ((P A) * A * (Q A))
```

## 6. File Layout

```text
MatDecompFormal/Instances/UTV/PLAN.md
MatDecompFormal/Instances/UTV.lean
MatDecompFormal/Instances/UTV/Details.lean
MatDecompFormal/Instances/UTV/Strategy.lean
MatDecompFormal/Instances/UTV/Direct.lean
MatDecompFormal/Instances/UTV/Existence.lean
```

## 7. Implementation Order

1. Define generic rectangular triangular predicate.
2. Define generic triangular equivalence target.
3. Define optional unitary UTV target separately.
4. Prove base cases.
5. Build rectangular strategy core with generic invertible two-sided transform.
6. Add conditional framework theorem through the rectangular driver.
7. Prove generic transport and block lift.
8. Discharge the field-level step oracle.
9. Add the `RCLike` unitary corollary if needed.

## 8. Relation to Other Instances

- Generic UTV is close to Gaussian elimination and should not require `ℂ`.
- Unitary UTV is close to SVD and should share two-sided unitary transport.
- Schur shares the same lower-left-zero recursive shape.


## Descent Template Contract

This plan is required to use the project descent template. The implementation
must explicitly instantiate these components rather than only giving a direct
standalone proof:

1. `Universe`: the object being recursively decomposed.
2. `μ`: a natural-number or well-founded measure.
3. `P`: the target predicate on the universe.
4. `base`: proof for objects at the base measure.
5. `transform`: an allowed equivalence/similarity/unitary/change-of-generators
   step that moves an object to a ready form.
6. `readiness`: the predicate saying the transformed object can be sliced.
7. `slice`: the smaller recursive subproblem.
8. `reach`: proof that every non-base object can reach a ready sliceable object.
9. `transport`: proof that `P` moves backward across `transform`.
10. `lift`: proof that `P (slice x)` implies `P x` for ready objects.
11. `driver`: assembly through the relevant decomposition-driver instance or a
    new algebraic driver with the same fields.
12. `final theorem`: obtained from the driver, not from a direct-only proof.

If the existing square/rectangular matrix drivers do not fit, add a reusable
algebraic descent driver instead of bypassing the template.

## 9. Verification

```bash
lake build MatDecompFormal.Instances.UTV
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/UTV -S
```
