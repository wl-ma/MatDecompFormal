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

Recommended first predicate:

```lean
structure SmithDiagonalData
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n R) where
  r : Type*
  fintype_r : Fintype r
  row : r → m
  col : r → n
  diag : r → R
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  entry_eq :
    ∀ i j, D i j = ∑ k, if row k = i ∧ col k = j then diag k else 0
  divides_next :
    ∀ k l, diagonalSuccessor k l → diag k ∣ diag l
```

Later, replace this data-oriented predicate with an order-indexed predicate
after a stable row/column rank API exists.

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
MatDecompFormal/Instances/Smith/PIDBridge.lean
```

## 8. Descent Template Contract

The Smith implementation uses the project descent template rather than a
direct-only proof. The implementation-facing contract is:

1. `Universe`: `RectUniverse R`.
2. `μ`: `rectSubtypeμ`, the minimum of row and column cardinalities.
3. `P`: `Smith_P`, the universe-level `HasSmithNormalForm` predicate.
4. `base`: `smith_base_univ`, reducing zero-dimensional rectangular universes
   to empty-row or empty-column Smith witnesses.
5. `transform`: `smithTwoSidedInvertibleTransform`, a two-sided multiplication
   by explicitly invertible matrices.
6. `readiness`: `SmithDescentReady`, which records an isolated head pivot, zero
   head row and column off the pivot, and divisibility of every tail entry by
   the pivot.
7. `slice`: `smithHeadTailReduction`, the lower-right head-tail submatrix.
8. `reach`: supplied by `ReductionStrategy.mk_reach` through
   `mkRectSubtypeInductionInstanceFromStrategy`; the hard one-step algebra is
   isolated in `SmithStepOracle`.
9. `transport`: `smith_transport_twoSidedUnits` packaged by
   `smith_transport_hook`.
10. `lift`: `smith_of_blockReady_reindex` packaged by `smith_lift_hook`.
11. `driver`: `smith_framework_inst`, built from
    `RectSubtypeInductionInstance`.
12. `final theorem`: currently
    `exists_smith_normal_form_framework_oracle`, obtained via
    `RectSubtypeInductionInstance.prove_for_matrix` with the step oracle
    dependency explicit.

## 9. Verification

```bash
lake build MatDecompFormal.Instances.Smith
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Smith --glob '!PLAN.md' -S
```

Before marking the implementation complete, also check:

```bash
printf 'import MatDecompFormal.Instances.Smith\n#check MatDecompFormal.Instances.exists_smith_normal_form_framework_oracle\n#check MatDecompFormal.Instances.exists_smith_normal_form_framework_gauss_oracle\n#check MatDecompFormal.Instances.exists_smith_normal_form_rank_oracle\n#check MatDecompFormal.Instances.exists_smith_normal_form_field\n#check MatDecompFormal.Instances.exists_smith_normal_form\n#check MatDecompFormal.Instances.SmithStepOracle\n#check MatDecompFormal.Instances.smithStepOracleOfGauss\n' | lake env lean --stdin
printf 'import MatDecompFormal.Instances.Smith\n#check MatDecompFormal.Instances.pidSubmoduleSmithNormalForm\n#check MatDecompFormal.Instances.exists_pid_submodule_smith_normal_form\n#check MatDecompFormal.Instances.PIDMatrixSmithBridge\n#check MatDecompFormal.Instances.exists_smith_normal_form_pid_bridge\n' | lake env lean --stdin
printf 'import MatDecompFormal.Instances.Smith\n#check MatDecompFormal.Instances.gaussInvertibleMatrix_basis_toMatrix\n#check MatDecompFormal.Instances.basis_change_toMatrix_eq_mul\n#check MatDecompFormal.Instances.basis_change_toMatrix_eq_mul_standard\n' | lake env lean --stdin
printf 'import MatDecompFormal.Instances.Smith\n#check MatDecompFormal.Instances.linearMap_eq_range_subtype_comp_rangeRestrict\n#check MatDecompFormal.Instances.linearMap_toMatrix_eq_range_subtype_mul_rangeRestrict\n#check MatDecompFormal.Instances.matrix_eq_range_subtype_mul_rangeRestrict\n' | lake env lean --stdin
printf 'import MatDecompFormal.Instances.Smith\n#check MatDecompFormal.Instances.PIDSmithRankIdx\n#check MatDecompFormal.Instances.smithNormalFormData_of_basisSmithNormalForm\n#check MatDecompFormal.Instances.isSmithNormalForm_of_basisSmithNormalForm\n' | lake env lean --stdin
printf 'import MatDecompFormal.Instances.Smith\n#check MatDecompFormal.Instances.pidSmithRankEquiv\n#check MatDecompFormal.Instances.isSmithNormalForm_of_basisSmithNormalForm_reindex\n#check MatDecompFormal.Instances.hasSmithNormalForm_subtype_matrix_of_basisSmithNormalForm\n' | lake env lean --stdin
rg -n "prove_for_matrix|smith_framework_inst|exists_smith_normal_form_framework|exists_smith_normal_form_framework_oracle|exists_smith_normal_form_framework_gauss_oracle|exists_smith_normal_form_rank_oracle|exists_smith_normal_form_field|exists_smith_normal_form|SmithStepOracle|smithStepOracleOfGauss|PIDMatrixSmithBridge|pidSubmoduleSmithNormalForm|basis_change_toMatrix_eq_mul|gaussInvertibleMatrix_basis_toMatrix|linearMap_eq_range_subtype_comp_rangeRestrict|linearMap_toMatrix_eq_range_subtype_mul_rangeRestrict|matrix_eq_range_subtype_mul_rangeRestrict|PIDSmithRankIdx|pidSmithRankEquiv|isSmithNormalForm_of_basisSmithNormalForm|hasSmithNormalForm_subtype_matrix_of_basisSmithNormalForm" MatDecompFormal/Instances/Smith MatDecompFormal/Instances/Smith.lean -S
```

## 10. Current Status

Completed implementation-facing milestones:

- File skeleton is present:
  `Smith.lean`, `Smith/Details.lean`, `Smith/Strategy.lean`,
  `Smith/Direct.lean`, `Smith/Existence.lean`, and
  `Smith/PIDBridge.lean`.
- Matrix-level target predicate is defined:
  `SmithNormalFormData`, `IsSmithNormalForm`, `HasSmithNormalForm`, and
  universe-level `Smith_P`.
- Base cases are implemented for empty row and empty column types.
- Strategy-side descent skeleton is implemented through the rectangular driver:
  `SmithTailRowIdx`, `SmithTailColIdx`, `SmithDescentReady`,
  `SmithStepOracle`, `smithTwoSidedInvertibleTransform`,
  `smithHeadTailReduction`, and `smith_strategy_core`.
- Gauss rank-step readiness is bridged into Smith readiness:
  `smithDescentReady_of_gaussReady` and `smithStepOracleOfGauss`.
- Transport and lift hooks are concrete:
  `smith_transport_twoSidedUnits`, `smith_transport_hook`,
  `smith_of_blockReady_reindex`, `smith_lift_hook`, and
  `smith_descent_hooks`.
- Framework theorem chain is routed through
  `RectSubtypeInductionInstance.prove_for_matrix`:
  `exists_smith_normal_form_framework` and
  `exists_smith_normal_form_framework_oracle`.
- The rank-normal-form bridge is implemented:
  `hasSmithNormalForm_of_gauss` and
  `exists_smith_normal_form_rank_oracle`.
- The Smith framework can now be driven directly by a Gauss step oracle through
  `exists_smith_normal_form_framework_gauss_oracle`.
- The field case is concrete:
  `exists_smith_normal_form_field` uses the concrete elementary Gauss oracle
  and then runs through the Smith rectangular framework via
  `smithStepOracleOfGauss`.
- The public theorem name `exists_smith_normal_form` is exposed for the
  completed field case. Its `[Field R]` assumptions are intentionally explicit;
  the PID-general theorem remains a future strengthening.
- The mathlib PID free-module Smith normal-form source is exposed through
  `pidSubmoduleSmithNormalForm` and
  `exists_pid_submodule_smith_normal_form`.
- The basis-change part of the matrix bridge is implemented:
  `gaussInvertibleMatrix_basis_toMatrix` repackages mathlib basis-change
  invertibility as `GaussInvertibleMatrix`, while
  `basis_change_toMatrix_eq_mul` and
  `basis_change_toMatrix_eq_mul_standard` convert a linear-map matrix in new
  bases into the explicit `P * A * Q` shape required by
  `HasSmithNormalForm`.
- The original matrix-to-range factorization is now formalized:
  `linearMap_eq_range_subtype_comp_rangeRestrict`,
  `linearMap_toMatrix_eq_range_subtype_mul_rangeRestrict`, and
  `matrix_eq_range_subtype_mul_rangeRestrict` prove that
  `Matrix.toLin' A` factors as the inclusion of its range after the surjection
  onto that range, and that the corresponding matrices multiply to the
  original matrix in standard bases.
- Mathlib's `Module.Basis.SmithNormalForm` diagonal inclusion matrix is now
  bridged to the local matrix predicate by
  `smithNormalFormData_of_basisSmithNormalForm` and
  `isSmithNormalForm_of_basisSmithNormalForm`. The finite SNF rank index is
  universe-lifted through `PIDSmithRankIdx` and `pidSmithRankEquiv` so it can
  live in the same rectangular matrix universe as the ambient basis index.
- The reindexed inclusion matrix is also bridged to the local predicate by
  `isSmithNormalForm_of_basisSmithNormalForm_reindex`.
- The verified range-inclusion half of the PID matrix bridge is implemented:
  `hasSmithNormalForm_subtype_matrix_of_basisSmithNormalForm` packages the
  inclusion map `N.subtype` as a full project-level `HasSmithNormalForm`
  witness, with arbitrary ambient row basis and the mathlib Smith basis on
  columns after universe lifting.
- The remaining conversion from mathlib's submodule/basis SNF to this
  project's explicit matrix theorem is named as `PIDMatrixSmithBridge`, with
  the conditional theorem `exists_smith_normal_form_pid_bridge`.
- The theorem name exposes the remaining mathematical dependency:
  the Euclidean-domain/PID Smith one-step construction is still represented by
  `SmithStepOracle`.

Remaining implementation work:

- Discharge `SmithStepOracle` over a Euclidean domain beyond fields.
- Generalize the oracle discharge to PID assumptions once the required
  divisibility and principal-ideal APIs are identified.
- Mathlib has PID Smith normal form for free-module submodules
  (`Mathlib.LinearAlgebra.FreeModule.PID`, e.g.
  `Submodule.smithNormalForm`), but the remaining bridge is not a direct import:
  it must turn the surjective factor
  `(Matrix.toLin' A).rangeRestrict : (n → R) →ₗ[R] LinearMap.range (Matrix.toLin' A)`
  into an allowed right multiplication by an invertible `n × n` matrix, typically
  via a kernel complement or quotient/free-basis argument. The range inclusion
  theorem already handles the local `IsSmithNormalForm` predicate, the ambient
  basis-change matrix, and the equality for `N.subtype`; the range factorization
  theorem now connects that inclusion to the original matrix up to this
  remaining column-side surjection bridge.

Roles:

- `Details.lean`: Smith predicates, invertible-matrix helpers, base cases.
- `Strategy.lean`: Smith readiness, invertible two-sided transformation,
  lower-right rectangular reduction, strategy core.
- `Direct.lean`: transport and block lift.
- `Existence.lean`: framework-routed theorem.
- `PIDBridge.lean`: mathlib PID submodule SNF entry point and the named
  matrix bridge obligation.
- `Smith.lean`: public imports.

## 11. Next Implementation Order

1. Build `PIDMatrixSmithBridge` by translating `A : Matrix m n R` to
   `Matrix.toLin' A`, applying `Submodule.smithNormalForm` to the range/image
   data, identifying the original matrix with the inclusion map through the
   range basis and the image factorization, and then using
   `basis_change_toMatrix_eq_mul_standard` plus
   `gaussInvertibleMatrix_basis_toMatrix` to package the explicit
   `P * A * Q` witness.
2. Use that bridge to expose the PID-scope matrix theorem.
3. Optionally instantiate `SmithStepOracle` separately for a Euclidean domain
   if a constructive descent proof is preferred over the mathlib PID bridge.
4. Expose an unconditional PID theorem only once the bridge/oracle is
   discharged:

   ```lean
#check MatDecompFormal.Instances.exists_smith_normal_form
   ```

## 12. Algebra-Minimality Policy

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
  exists_smith_normal_form
  exists_smith_euclidean
  exists_smith_pid
  ```

This makes it clear which theorem depends on which algebraic structure.
