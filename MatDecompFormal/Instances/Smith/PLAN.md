# Smith Normal Form via the Descent Framework

This plan describes how to formalize Smith normal form using the project's
descent-template style. Unlike SVD, Schur, Hessenberg, or UTV, this is not a
unitary decomposition over `ℂ`; it is a row/column equivalence theorem over
rings with enough divisibility structure, preferably stated with the weakest
practical algebraic assumptions.

## 1. Algebraic Scope

The final theorem should be as generic as possible. Do not specialize to
`ℝ` or `ℂ`.

Candidate assumption levels:

1. **Euclidean domain**: easiest constructive descent because there is a norm
   decreasing under division.
2. **PID**: standard mathematical scope for Smith normal form.
3. **Bezout domain plus an additional termination/noetherian condition**:
   closer to minimal algebra but harder to drive constructively.

Recommended implementation path:

1. First prove a framework theorem over an explicit `SmithStepOracle`.
2. Instantiate the oracle for a Euclidean domain.
3. Generalize to PID once the required mathlib APIs are identified.

Avoid baking a concrete scalar type into definitions. All definitions should be
parameterized by `R`.

## 2. Target Theorem

Primary target over a PID-like domain:

```lean
theorem exists_smith_normal_form
    {R m n : Type*}
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    ∃ P : Matrix m m R, ∃ Q : Matrix n n R, ∃ D : Matrix m n R,
      Matrix.det P ∈ nonZeroDivisors R ∧
      Matrix.det Q ∈ nonZeroDivisors R ∧
      IsUnit (Matrix.det P) ∧
      IsUnit (Matrix.det Q) ∧
      IsSmithNormalForm D ∧
      D = P * A * Q
```

The determinant conditions may be simplified to `IsUnit (Matrix.det P)` and
`IsUnit (Matrix.det Q)` once the local invertibility API is chosen.

Equivalent statement:

```lean
∃ P Q D,
  InvertibleMatrix P ∧
  InvertibleMatrix Q ∧
  IsSmithNormalForm D ∧
  D = P * A * Q
```

Use whichever is easier to compose with existing row/column operation lemmas.

## 3. Smith Predicate

For a rectangular diagonal matrix `D : Matrix m n R`, Smith normal form should
state:

1. `D` is rectangular diagonal.
2. The diagonal entries form a divisibility chain:

   ```lean
   d₀ ∣ d₁ ∣ d₂ ∣ ...
   ```

3. Entries off the chosen diagonal are zero.
4. Optional normalization, depending on the ring:
   - for a field, use `1`s followed by `0`s;
   - for `ℤ`, use positive diagonal entries;
   - for a generic PID, avoid canonical associates unless a normalization API
     is supplied.

Required predicate shape:

```lean
structure SmithNormalFormData
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n R) where
  r : Type*
  fintype_r : Fintype r
  order : Fin (Fintype.card r) ≃ r
  row : r → m
  col : r → n
  diag : r → R
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  entry_eq :
    ∀ i j, D i j = ∑ k, if row k = i ∧ col k = j then diag k else 0
  divides_chain :
    ∀ k : Fin (Fintype.card r),
      (hnext : (k : Nat) + 1 < Fintype.card r) →
        diag (order k) ∣ diag (order ⟨(k : Nat) + 1, hnext⟩)
```

The primary diagonal support must stay data-oriented: `r` is an arbitrary finite
index type, and `diag`, `row`, and `col` must remain indexed by that `r`. Do
not redefine the support as a numeric length and then use `Fin r`, `Fin rank`,
`Fin (Fintype.card r)`, a list, or a vector as the primary diagonal
representation. In particular, do not change the data model to
`r : Nat`/`rank : Nat` with fields such as `diag : Fin r -> R`. The only
acceptable use of `Fin (Fintype.card r)` in the core data is as the complete
enumeration witness

```lean
order : Fin (Fintype.card r) ≃ r
```

used to state adjacent divisibility through `order`. All actual diagonal
payload remains data-oriented over `r`. This keeps the local Smith data
compatible with the rest of the instances, while still ruling out the old
vacuous successor-relation proof.

## 4. Descent Shape

For a matrix `A : Matrix m n R`:

1. If one side is empty, the zero matrix is already Smith.
2. If `A = 0`, use the all-zero diagonal.
3. Otherwise find a nonzero pivot and move it to the head/head position using
   row and column swaps.
4. Use Bezout/gcd row and column operations to make the pivot divide all entries
   in its row and column.
5. If the pivot does not divide some entry in the remaining block, use a
   standard Smith reduction step to replace the pivot by a proper divisor or a
   smaller Euclidean norm representative, then repeat.
6. Once the pivot divides every entry, clear the rest of the head row and head
   column.
7. Recurse on the lower-right block.
8. Lift the tail Smith form and preserve the divisibility chain by the pivot
   divisibility condition.

The recursive slice is again the lower-right block after a head-tail split.

## 5. Framework Mapping

### Transformation

Smith transformations are two-sided equivalences by invertible matrices:

```lean
B = P * A * Q
```

where `P` and `Q` are invertible over `R`.

This differs from SVD/UTV because no conjugate transpose or unitary structure is
available. Define a reusable transformation relation:

```lean
structure TwoSidedInvertibleTransform
    (m n R : Type*) where
  P : Matrix m m R
  Q : Matrix n n R
  invP : InvertibleMatrix P
  invQ : InvertibleMatrix Q
```

### Readiness

After transformation, the matrix is Smith-ready if:

1. the head/head pivot is the chosen diagonal entry;
2. the head row and head column are zero away from the pivot;
3. the pivot divides every entry in the tail block.

Sketch:

```lean
def SmithDescentReady (A : Matrix m n R) : Prop :=
  let A' := Matrix.reindex rowHeadTail colHeadTail A
  A'.toBlocks₁₂ = 0 ∧
  A'.toBlocks₂₁ = 0 ∧
  (∀ i j, A'.toBlocks₁₁ () () ∣ A'.toBlocks₂₂ i j)
```

### Reduction

Use the rectangular lower-right block:

```lean
slice A = A.toBlocks₂₂
```

### Measure

The structural recursion uses:

```lean
min (Fintype.card m) (Fintype.card n)
```

The internal pivot-improvement loop needs a separate well-founded measure:

- Euclidean norm of the pivot for Euclidean domains;
- ideal inclusion/order for PID route;
- explicit oracle route before this is discharged.

## 6. Required Lemmas

### Basic matrix equivalence

- Identity invertible matrix.
- Product of invertible matrices is invertible.
- Block diagonal extension of invertible matrices.
- Transport:

  ```lean
  HasSmith B → B = P * A * Q → Invertible P → Invertible Q → HasSmith A
  ```

### Base cases

- Empty row type.
- Empty column type.
- Zero matrix.

### Block lift

Given a Smith-ready block matrix:

```lean
fromBlocks d 0 0 B₂₂
```

and a Smith decomposition of `B₂₂`, lift it to a Smith decomposition of the full
matrix. The lift must prove:

1. rectangular diagonal shape;
2. the first diagonal entry divides the first tail diagonal entry;
3. tail divisibility chain is preserved;
4. block-diagonal transformations remain invertible.

### Pivot step

Initially isolate the hard algebra:

```lean
structure SmithStepOracle
    (R m n : Type*) [CommRing R]
    [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  P : Matrix m n R → Matrix m m R
  Q : Matrix m n R → Matrix n n R
  invertible_P : ∀ A, InvertibleMatrix (P A)
  invertible_Q : ∀ A, InvertibleMatrix (Q A)
  ready : ∀ A, SmithDescentReady ((P A) * A * (Q A))
```

Then discharge it in stages:

1. field/rank-normal-form case;
2. Euclidean domain case;
3. PID case.

## 7. File Layout

Proposed files:

```text
MatDecompFormal/Instances/Smith/PLAN.md
MatDecompFormal/Instances/Smith.lean
MatDecompFormal/Instances/Smith/Details.lean
MatDecompFormal/Instances/Smith/Strategy.lean
MatDecompFormal/Instances/Smith/Direct.lean
MatDecompFormal/Instances/Smith/Existence.lean
```

Roles:

- `Details.lean`: Smith predicates, invertible-matrix helpers, base cases.
- `Strategy.lean`: Smith readiness, invertible two-sided transformation,
  lower-right rectangular reduction, strategy core.
- `Direct.lean`: transport and block lift.
- `Existence.lean`: framework-routed theorem.
- `Smith.lean`: public imports.

## 8. Implementation Order

1. Define a local `InvertibleMatrix` predicate if no suitable project-wide
   predicate already exists.
2. Define `IsSmithNormalForm` and `HasSmith`.
3. Prove base cases.
4. Define `SmithDescentReady`.
5. Build a rectangular strategy core using the existing rectangular driver.
6. Add a conditional theorem using `SmithStepOracle`:

   ```lean
   theorem exists_smith_framework_oracle ...
   ```

7. Prove two-sided invertible transport.
8. Prove block lift.
9. Instantiate the step oracle first for a field or Euclidean domain.
10. Generalize the scalar assumptions toward PID.
11. Expose:

   ```lean
   #check MatDecompFormal.Instances.exists_smith_normal_form
   ```

## 9. Algebra-Minimality Policy

The implementation should avoid unnecessary scalar assumptions:

- Do not use `ℝ` or `ℂ` unless proving a specialized corollary.
- Keep base definitions over `[Zero R]` or `[CommMonoidWithZero R]` where
  possible.
- Use `[CommRing R]` only where matrix multiplication and determinants require
  it.
- Use `[IsDomain R]`, PID, Bezout, or Euclidean assumptions only in the pivot
  existence step.
- Keep theorem names layered:

  ```lean
  exists_smith_framework_oracle
  exists_smith_euclidean
  exists_smith_pid
  ```

This makes it clear which theorem depends on which algebraic structure.


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

## 10. Verification

Expected checks:

```bash
lake build MatDecompFormal.Instances.Smith
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Smith -S
```

The final theorem should route through the rectangular decomposition driver and
should state the weakest scalar assumptions that the proof actually uses.
