# QR Audit Fix Plan

This document is the implementation plan for strengthening the QR instance
after the decomposition audit. It is intentionally code-facing: each item below
should either become a Lean definition/theorem or a verified comment explaining
why the stronger target is not yet claimed.

## Audit Finding

The base QR theorem is mathematically valid as a structural QR decomposition:
it supplies an orthogonal factor and an upper-triangular factor. The weak point
is the Householder/Givens theorem surface. A theorem proved by recovering a
product representation from final orthogonality must not be presented as an
algorithmic elimination trace unless the individual elimination steps and their
cumulative product are part of the formal witness.

The repair should preserve the project square-descent framework. Do not replace
the existing recursive framework with an ad hoc matrix proof. Instead, thread
stronger product or trace data through the existing strategy objects when the
strategy already constructs the elementary transformations.

## Target Theorem Layers

### 1. Structural QR

Keep the public structural theorem:

```lean
theorem exists_qr_decomposition
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    HasQR A
```

This theorem should assert only the ordinary decomposition data: final `Q`,
final `R`, orthogonality of `Q`, upper triangularity of `R`, and `A = Q * R`.

### 2. Product QR

Expose product-representable variants:

```lean
def IsProductOf (P : Matrix ι ι ℝ -> Prop) (Q : Matrix ι ι ℝ) : Prop

def HasHouseholderProductQR
    [LinearOrder ι] (A : Matrix ι ι ℝ) : Prop

def HasGivensProductQR
    [LinearOrder ι] (A : Matrix ι ι ℝ) : Prop

theorem exists_householder_product_qr ...
theorem exists_givens_product_qr ...
```

The product predicate must be a finite product witness, such as a list together
with a proof that every list element is an elementary Householder/Givens matrix.
It is acceptable for this layer to say "the final orthogonal factor is
representable as a product"; it is not acceptable for this layer to imply that
the list is the exact elimination history unless the theorem records that
history.

### 3. Trace QR

Add exact trace statements only where the proof really builds the steps:

```lean
structure QRStepTrace (A : Matrix ι ι ℝ) where
  before : Matrix ι ι ℝ
  step : Matrix ι ι ℝ
  after : Matrix ι ι ℝ
  step_shape : IsHouseholderMatrix step \/ IsGivensMatrix step
  step_orthogonal : IsOrthogonalMatrix step
  after_eq : after = stepᵀ * before
  ready_progress : ...

structure HouseholderQRTrace [LinearOrder ι] (A : Matrix ι ι ℝ) where
  steps : List (Matrix ι ι ℝ)
  step_shape : forall H, H ∈ steps -> IsHouseholderMatrix H
  cumulative_Q : Matrix ι ι ℝ
  cumulative_eq : cumulative_Q = matrixProduct steps
  R : Matrix ι ι ℝ
  upper_R : IsUpperTriangular R
  final_eq : A = cumulative_Q * R
```

Define the Givens analogue with `IsGivensMatrix`. If current code only supports
the final product layer, keep the trace theorem names out of the public API
until this structure is actually populated from recursive steps.

## File-Level Plan

### `Details.lean`

1. Keep `IsOrthogonalMatrix`, `HasQR`, and `HasStructuredQR` as the structural
   layer.
2. Ensure `matrixProduct` and `IsProductOf` are the shared product vocabulary.
3. Add or keep generic conversion lemmas:

   ```lean
   theorem hasQR_of_hasStructuredQR ...
   theorem hasStructuredQR_of_qrProductTrace ...
   theorem hasQR_of_qrProductTrace ...
   ```

4. If trace records remain Prop-level aliases rather than structures, document
   explicitly that they are final-factor product traces, not step-by-step
   elimination traces.

### `Householder.lean`

1. Keep `householderMatrix` and `IsHouseholderMatrix` as the elementary
   reflector predicates.
2. Prove local step facts for the concrete head transformation:

   ```lean
   theorem qrHeadOrthogonalStep_isHouseholderMatrix ...
   theorem qrHeadOrthogonalStep_isHouseholderProduct ...
   ```

3. Strengthen the recursive predicate used by the Householder strategy so that
   recursive lifts preserve `IsHouseholderProduct Q`, not only
   `IsOrthogonalMatrix Q`.
4. The theorem

   ```lean
   theorem isHouseholderProduct_of_isOrthogonalMatrix ...
   ```

   may remain as a recovery theorem, but product QR should prefer the strategy
   proof when available. If a public theorem uses recovery from final
   orthogonality, its docstring must say so.
5. Add forgetful lemmas:

   ```lean
   theorem hasQR_of_hasHouseholderQR ...
   theorem hasQR_of_householderQRTrace ...
   ```

### `Givens.lean`

1. Keep `givensEmbeddedMatrix`, `IsGivensMatrix`, and `IsGivensProduct` as the
   elementary rotation layer.
2. Use the existing sweep constructions as the preferred proof source:

   ```lean
   qrGivensTailList
   qrGivensSweepQCS
   qrGivensSweepQCS_isGivensProduct
   qrGivensSweep_ready
   ```

3. Thread `IsGivensProduct` through the strong strategy predicate, rather than
   recovering it from final orthogonality.
4. If a full trace is implemented, record each pair rotation in the sweep list,
   the active tail index, and the annihilated entry proof.
5. Add forgetful lemmas:

   ```lean
   theorem hasQR_of_hasGivensQR ...
   theorem hasQR_of_givensQRTrace ...
   ```

### `Driver.lean`, `Recursive.lean`, `Strategy.lean`

1. Keep the generic QR driver focused on `HasQR`.
2. Do not make the base strategy depend on Householder or Givens definitions.
3. Put stronger strategy predicates in `Householder.lean` and `Givens.lean`,
   importing the base driver instead of changing the base driver API.

## Implementation Order

1. Build and record the baseline:

   ```bash
   lake build MatDecompFormal.Instances.QR.Driver
   lake build MatDecompFormal.Instances.QR.Householder
   lake build MatDecompFormal.Instances.QR.Givens
   ```

2. In `Details.lean`, finalize shared product vocabulary and forgetful lemmas.
3. In `Householder.lean`, prove the head step is a Householder product, then
   strengthen the recursive lift predicate and expose
   `exists_householder_product_qr`.
4. In `Givens.lean`, prove the sweep product lemma is used by the recursive
   lift and expose `exists_givens_product_qr`.
5. Add trace records only after the product layer builds. Start with final
   product traces, then refine to exact step traces if the recursive framework
   exposes the necessary step sequence.
6. Re-run the module builds after each checkpoint.

## Acceptance Checks

There is currently no `MatDecompFormal/Instances/QR.lean` aggregator file, so
use the concrete modules unless one is added deliberately:

```bash
lake build MatDecompFormal.Instances.QR.Driver
lake build MatDecompFormal.Instances.QR.Householder
lake build MatDecompFormal.Instances.QR.Givens
lake build MatDecompFormal.Instances
rg -n "Householder|Givens|trace|Trace|Product|HasQR" MatDecompFormal/Instances/QR -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/QR -S -g '*.lean'
```

Manual review criteria:

- `exists_qr_decomposition` remains structural.
- product theorem names claim product representability, not exact algorithmic
  history, unless trace data is present;
- Householder and Givens product predicates have forgetful lemmas to `HasQR`;
- no new oracle, axiom, or `sorry` is introduced for the strengthened layer.
