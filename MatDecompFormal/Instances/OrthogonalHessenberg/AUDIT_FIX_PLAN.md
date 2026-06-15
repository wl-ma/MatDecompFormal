# Orthogonal Hessenberg Audit Fix Plan

This document gives the implementation plan for strengthening the real
orthogonal and complex unitary Hessenberg reductions. The guiding rule is to
keep the existing boundary-column descent framework and add stronger witness
layers around it, rather than replacing it with a standalone proof.

## Audit Finding

The structural Hessenberg statement is mathematically appropriate: every
finite square matrix over the supported scalar field is orthogonally or
unitarily similar to a Hessenberg matrix. The audit issue is the same as for QR:
Householder and Givens names must not imply a recorded elimination trajectory
unless the elementary boundary steps are part of the theorem data.

For the complex route, "Householder" and "Givens" are implemented through
unitary boundary-column transforms. The final theorem may be a valid unitary
Hessenberg theorem even when it does not expose an exact step trace.

## Target Theorem Layers

### 1. Structural Hessenberg Reduction

Keep these as the base public theorems:

```lean
theorem exists_unitary_hessenberg_reduction ...
theorem exists_orthogonal_hessenberg_reduction ...
```

They should assert the final similarity equation, the final unitary/orthogonal
factor, and the Hessenberg shape.

### 2. Boundary-Framework Theorems

Expose the subtype-descent route explicitly:

```lean
theorem exists_unitaryHessenbergBoundary_framework ...
theorem exists_orthogonalHessenbergBoundary_framework ...
```

These are the theorems to cite for project-framework claims. They should remain
conditional on the appropriate step oracle only where a concrete oracle has not
yet been supplied.

### 3. Product Hessenberg Reduction

For real reductions, add or keep final-factor product witnesses:

```lean
def HasHouseholderProductHessenberg (A : Matrix ι ι ℝ) : Prop
def HasGivensProductHessenberg (A : Matrix ι ι ℝ) : Prop

theorem exists_householder_product_hessenberg_reduction ...
theorem exists_givens_product_hessenberg_reduction ...
```

Only prove the Givens product theorem if the proof supplies a finite Givens
product for the final factor. Do not fake it from a generic orthogonality
statement unless the theorem name and docstring explicitly say it is only a
representability recovery theorem.

### 4. Boundary Trace Hessenberg Reduction

Exact trajectory claims need a trace record:

```lean
structure HessenbergBoundaryTrace (A : Matrix ι ι K) where
  steps : List (Matrix ι ι K)
  active_boundaries : List Nat
  step_shape : ...
  step_isometry : forall Q, Q ∈ steps -> ...
  cumulative_Q : Matrix ι ι K
  cumulative_eq : cumulative_Q = matrixProduct steps
  H : Matrix ι ι K
  hessenberg_H : IsHessenberg H
  final_eq : H = cumulative_Qᴴ * A * cumulative_Q
  boundary_ready_at_step : ...
```

For real variants use transpose and `IsOrthogonalMatrix`; for complex variants
use conjugate transpose and `IsUnitaryMatrix`.

## File-Level Plan

### `Details.lean`

1. Keep `HasUnitaryHessenberg` as the complex structural predicate.
2. Keep `UnitaryHessenbergWitnessData tag A` as the route-tagged witness layer.
3. Add or keep forgetful lemmas:

   ```lean
   theorem hasUnitaryHessenberg_of_witnessData ...
   theorem witnessData_of_hasUnitaryHessenberg ...
   ```

4. If `UnitaryHessenbergTrace` is only a route-tagged final witness, document
   that it is not a per-step boundary trace.

### `Real.lean`

1. Keep `HasOrthogonalHessenberg` and `HasOrthogonalHessenbergBoundary` as the
   real structural and boundary predicates.
2. Maintain product predicates:

   ```lean
   HasHouseholderProductHessenberg
   HasGivensProductHessenberg
   OrthogonalHessenbergTrace
   ```

3. The concrete orthogonal step oracle should be built from the normalized
   boundary column and an orthonormal basis extension. Its public theorem should
   feed `exists_orthogonal_hessenberg_reduction`.
4. Strengthen the Householder route first. A global real Householder product
   theorem is acceptable when it is explicitly a final-factor product theorem.
5. Add a real Givens product theorem only after the boundary Givens module
   supplies a product proof for every recursive boundary step.

### `Concrete.lean`

1. Keep the concrete complex unitary boundary oracle:

   ```lean
   unitaryHessenbergBoundaryStepOracle
   exists_unitary_hessenberg_reduction_complex
   ```

2. The construction should use `boundaryColumnVec`, normalization, orthonormal
   basis extension, and `matrixOfOrthonormalBasis`.
3. Add route-tagged witness theorems for the concrete oracle, but do not call
   them Householder or Givens unless the elementary step predicate matches.

### `Householder/Real.lean` and `Givens/Real.lean`

1. Keep the boundary-column step matrices as the step-level implementation.
2. Prove for each step:

   ```lean
   step_orthogonal
   step_ready
   step_product_shape
   ```

3. Thread `step_product_shape` into the recursive boundary framework before
   exposing a product theorem.
4. Add trace aliases only after the trace record includes the list of boundary
   steps.

### `Householder/Complex.lean` and `Givens/Complex.lean`

1. Keep the complex unitary step oracles as concrete routes to the structural
   unitary Hessenberg theorem.
2. If product/trace names are exposed, introduce complex-specific step
   predicates, for example:

   ```lean
   def IsComplexHouseholderBoundaryStep ...
   def IsComplexGivensBoundaryStep ...
   ```

3. Do not reuse real `IsHouseholderMatrix` or `IsGivensMatrix` unless their
   scalar and conjugation conventions genuinely match the complex step.

## Implementation Order

1. Build the baseline modules:

   ```bash
   lake build MatDecompFormal.Instances.OrthogonalHessenberg.Details
   lake build MatDecompFormal.Instances.OrthogonalHessenberg.Real
   lake build MatDecompFormal.Instances.OrthogonalHessenberg.Concrete
   ```

2. Finalize structural and route-tagged witness lemmas in `Details.lean`.
3. Complete the real Householder product route in `Real.lean` and
   `Householder/Real.lean`.
4. Complete the real Givens product route only if the step product proof is
   available in `Givens/Real.lean`.
5. Add complex Householder/Givens route-tagged witness theorems in their
   complex modules.
6. Add true boundary trace structures after product witnesses build.
7. Rebuild the aggregator:

   ```bash
   lake build MatDecompFormal.Instances.OrthogonalHessenberg
   ```

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.OrthogonalHessenberg
lake build MatDecompFormal.Instances
rg -n "Householder|Givens|trace|Trace|boundary|Boundary|Product|Hessenberg" MatDecompFormal/Instances/OrthogonalHessenberg -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/OrthogonalHessenberg -S -g '*.lean'
```

Manual review criteria:

- structural, boundary-framework, product, and trace theorem names are
  separated;
- Householder/Givens trajectory claims expose step data;
- every stronger predicate has a forgetful lemma back to
  `HasOrthogonalHessenberg` or `HasUnitaryHessenberg`;
- no complex theorem silently uses a real elementary-step predicate with the
  wrong scalar convention.
