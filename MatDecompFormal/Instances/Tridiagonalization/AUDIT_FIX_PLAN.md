# Tridiagonalization Audit Fix Plan

This document gives the implementation plan for strengthening Hermitian
unitary tridiagonalization. The goal is to keep the valid spectral theorem,
make the boundary-framework theorem the implementation-facing route, and add
product or trace layers only where the proof records the elementary unitary
similarities.

## Audit Finding

The mathematical target is correct only for Hermitian matrices: a finite
Hermitian complex matrix is unitarily similar to a tridiagonal matrix. A normal
spectral theorem can prove this as an existence shortcut because diagonal
matrices are tridiagonal. That shortcut is valid, but it is not a formal
Householder or Givens tridiagonalization trajectory.

The repair should keep the Hermitian hypothesis visible, route framework claims
through the boundary-column descent theorem, and add route-tagged product or
trace data for concrete boundary steps.

## Target Theorem Layers

### 1. Spectral Existence

Keep the spectral fallback under an explicit name:

```lean
theorem exists_unitary_tridiagonalization_spectral
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A
```

This theorem is an existence proof, not an elementary reduction trace.

### 2. Boundary Framework

Expose the boundary route:

```lean
theorem exists_unitaryTridiagonalizationBoundary_framework ...

theorem exists_unitary_tridiagonalization_boundary_framework
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A
```

This is the theorem to cite for project framework claims. It should use
`TridiagonalizationBoundaryStepOracle` and the local boundary lift theorem.

### 3. Public Tridiagonalization

The unsuffixed public theorem should be:

```lean
theorem exists_unitary_tridiagonalization
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    HasUnitaryTridiagonalization A
```

It may call the boundary-framework theorem. If it calls the spectral theorem
instead, comments must say that the public route is spectral existence only.

### 4. Product Tridiagonalization

Use route-tagged complex unitary product predicates:

```lean
def IsTaggedUnitaryTridiagonalizationStep
    (tag : String) (Q : Matrix ι ι ℂ) : Prop

def HasHouseholderProductTridiagonalization
    (A : Matrix ι ι ℂ) : Prop

def HasGivensProductTridiagonalization
    (A : Matrix ι ι ℂ) : Prop
```

Do not reuse real QR `IsHouseholderMatrix` or `IsGivensMatrix` unless the
complex scalar and conjugation conventions are formally compatible. For complex
boundary steps, route tags such as `"complex-householder-boundary"` and
`"complex-givens-boundary"` are acceptable if the theorem only claims a tagged
unitary product.

### 5. Trace Tridiagonalization

Exact elementary trajectory claims require:

```lean
structure TridiagonalizationStepTrace (A : Matrix ι ι ℂ) where
  active_boundary : Nat
  before : Matrix ι ι ℂ
  step : Matrix ι ι ℂ
  after : Matrix ι ι ℂ
  step_unitary : IsUnitaryMatrix step
  step_shape : IsTaggedUnitaryTridiagonalizationStep tag step
  hermitian_before : before.IsHermitian
  hermitian_after : after.IsHermitian
  after_eq : after = stepᴴ * before * step
  boundary_progress : ...

structure TridiagonalizationTrace (A : Matrix ι ι ℂ) where
  hermitian_A : A.IsHermitian
  steps : List (TridiagonalizationStepTrace A)
  cumulative_Q : Matrix ι ι ℂ
  cumulative_eq : ...
  T : Matrix ι ι ℂ
  tridiagonal_T : IsTridiagonal T
  final_eq : A = cumulative_Q * T * cumulative_Qᴴ
```

## File-Level Plan

### `Details.lean`

1. Keep `IsTridiagonal` and `HasUnitaryTridiagonalization` as the structural
   target.
2. Keep product predicates separate from structural tridiagonalization:

   ```lean
   HasUnitaryProductTridiagonalization
   HasHouseholderProductTridiagonalization
   HasGivensProductTridiagonalization
   ```

3. Maintain forgetful lemmas:

   ```lean
   hasUnitaryTridiagonalization_of_product
   hasUnitaryTridiagonalization_of_householderProduct
   hasUnitaryTridiagonalization_of_givensProduct
   ```

4. Keep `hA : A.IsHermitian` visible on existence theorems. Do not bury it
   inside witness data.

### `Boundary.lean`

1. Keep `HasUnitaryTridiagonalizationBoundary` and
   `TridiagonalizationBoundaryStepOracle` as the framework boundary.
2. Ensure `tridiagonalizationBoundary_lift_ready` is the local proof used by
   the framework theorem.
3. Preserve Hermitian invariants across unitary similarity in the boundary
   lift.
4. Add a trace-ready version of the boundary proof data only if the framework
   can return or thread a list of boundary steps.

### `Concrete.lean`

1. Supply the concrete boundary step oracle using the current orthonormal-basis
   construction.
2. Prove:

   ```lean
   tridiagonalizationConcreteStepQ_unitary
   tridiagonalizationConcreteStepQ_ready_boundary
   tridiagonalizationConcreteStepQ_ready_matrix
   ```

3. This concrete oracle should feed the boundary-framework theorem, not only
   the spectral fallback.

### `Spectral.lean`

1. Keep `exists_unitary_tridiagonalization_spectral` as the normal-spectral
   existence proof.
2. Make the unsuffixed theorem call the boundary-framework theorem if the
   concrete boundary oracle builds.
3. Add public route aliases:

   ```lean
   exists_unitary_tridiagonalization_householder_boundary
   exists_unitary_tridiagonalization_givens_boundary
   exists_householder_product_tridiagonalization
   exists_givens_product_tridiagonalization
   ```

4. Every route alias should state whether it is a boundary route, a tagged
   unitary product route, or a true trace route.

## Implementation Order

1. Build the baseline:

   ```bash
   lake build MatDecompFormal.Instances.Tridiagonalization
   ```

2. Verify `Details.lean` has structural/product/trace predicates and forgetful
   lemmas.
3. Ensure `Boundary.lean` has the complete framework theorem from step oracle
   plus local lift.
4. Ensure `Concrete.lean` supplies the concrete step oracle.
5. Update `Spectral.lean` so theorem names distinguish spectral fallback and
   boundary-framework public route.
6. Add route-tagged Householder/Givens product aliases using complex boundary
   steps.
7. Add true trace data only after each boundary step's active boundary and
   progress proof are recorded.
8. Rebuild after each checkpoint.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.Tridiagonalization
lake build MatDecompFormal.Instances
rg -n "Spectral|Boundary|Householder|Givens|trace|Trace|Product|tridiagonal|Hermitian" MatDecompFormal/Instances/Tridiagonalization -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Tridiagonalization -S -g '*.lean'
```

Manual review criteria:

- the unsuffixed public theorem either routes through the boundary framework or
  explicitly documents a spectral-only route;
- all meaningful existence theorems keep `A.IsHermitian` visible;
- product theorems use complex unitary step predicates or route tags, not
  mismatched real QR predicates;
- no Householder/Givens trajectory claim exists without trace data.
