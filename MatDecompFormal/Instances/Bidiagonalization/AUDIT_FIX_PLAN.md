# Bidiagonalization Audit Fix Plan

This document is the implementation plan for turning the bidiagonalization
instance into a clearly layered theorem surface. The spectral/SVD route is
valid as an existence proof, but it should not be the only theorem used to
support framework or algorithmic claims.

## Audit Finding

The current bidiagonalization target is mathematically reasonable: it supplies
left and right unitary or orthogonal factors and an upper-bidiagonal middle
matrix. The gap is that some public routes use spectral/SVD readiness. That
proves existence, but it does not formalize an independent Golub-Kahan,
Householder, or Givens two-sided reduction trajectory.

The repair should keep the valid spectral theorem and add framework-facing
boundary theorems plus explicit left/right product or trace data where the code
actually constructs elementary transformations.

## Target Theorem Layers

### 1. Spectral Existence

Keep the spectral route under explicit names:

```lean
theorem exists_unitary_bidiagonalization_spectral_framework ...
theorem exists_orthogonal_bidiagonalization_spectral_framework ...
```

These theorems may use SVD/spectral block-ready data. Their comments should say
that they are existence theorems, not algorithm traces.

### 2. Boundary Framework

Expose the descent-framework theorem:

```lean
theorem exists_unitary_bidiagonalization_boundary_framework ...
theorem exists_unitary_bidiagonalization_boundary_oracle ...
theorem exists_orthogonal_bidiagonalization_oracle ...
```

This is the route to cite when claiming the result is integrated with the
project's rectangular descent abstractions.

### 3. Left/Right Product Bidiagonalization

Add final-factor product predicates:

```lean
def HasLeftRightProductOrthogonalBidiagonalization
    (A : Matrix m n ℝ) : Prop

def HasLeftRightHouseholderProductBidiagonalization
    (A : Matrix m n ℝ) : Prop

def HasLeftRightGivensProductBidiagonalization
    (A : Matrix m n ℝ) : Prop
```

Each predicate should record:

- final `U : Matrix m m ℝ` and `V : Matrix n n ℝ`;
- final `B : Matrix m n ℝ`;
- orthogonality of `U` and `V`;
- `IsUpperBidiagonal B`;
- finite product witnesses for `U` and `V` where claimed;
- the equation `A = U * B * Vᵀ`.

### 4. Two-Sided Trace Bidiagonalization

Exact algorithmic claims need a two-sided trace:

```lean
structure BidiagonalizationStepTrace (A : Matrix m n K) where
  active_row_boundary : Nat
  active_col_boundary : Nat
  left_step : Matrix m m K
  right_step : Matrix n n K
  left_shape : ...
  right_shape : ...
  before : Matrix m n K
  after : Matrix m n K
  after_eq : after = left_stepᴴ * before * right_step
  ready_progress : ...

structure BidiagonalizationTrace (A : Matrix m n K) where
  steps : List (BidiagonalizationStepTrace A)
  cumulative_U : Matrix m m K
  cumulative_V : Matrix n n K
  cumulative_left_eq : ...
  cumulative_right_eq : ...
  B : Matrix m n K
  bidiagonal_B : IsUpperBidiagonal B
  final_eq : A = cumulative_U * B * cumulative_Vᴴ
```

For real orthogonal traces replace conjugate transpose by transpose.

## File-Level Plan

### `Details.lean`

1. Keep `IsUpperBidiagonal`, `HasUnitaryBidiagonalization`, and
   `HasOrthogonalBidiagonalization` as the structural layer.
2. Add or keep left/right product predicates and forgetful lemmas:

   ```lean
   theorem hasOrthogonalBidiagonalization_of_leftRightProduct ...
   theorem hasOrthogonalBidiagonalization_of_hasLeftRightHouseholderProduct ...
   theorem hasOrthogonalBidiagonalization_of_hasLeftRightGivensProduct ...
   ```

3. If `BidiagonalizationTrace` is currently a final product witness, document
   that it is not a Golub-Kahan step trace.
4. Reuse `QR.Householder` and `QR.Givens` product predicates for real left and
   right factors instead of duplicating elementary matrix definitions.

### `Strategy.lean` and `Direct.lean`

1. Keep `BidiagonalizationStepOracle` and
   `BidiagonalizationBoundaryStepOracle` as the framework boundary.
2. Add stronger step-ready records only if they can be consumed by the existing
   rectangular framework. Do not create a separate recursion outside the
   framework.
3. If a step oracle is spectral, name it as spectral. If it is elementary,
   name it Householder/Givens and expose the step-shape proof.

### `Existence.lean`

1. Keep framework theorems as the assembly layer.
2. Ensure theorem names distinguish:

   ```lean
   exists_unitary_bidiagonalization_framework
   exists_unitary_bidiagonalization_boundary_framework
   exists_unitary_bidiagonalization_oracle
   exists_unitary_bidiagonalization_boundary_oracle
   ```

3. Add comments showing which theorem is conditional on an oracle and which
   theorem has a concrete oracle supplied elsewhere.

### `Spectral.lean`

1. Keep the SVD/spectral construction under spectral names.
2. The spectral theorem may be used to derive structural bidiagonalization and
   final orthogonal product representability.
3. Do not present the spectral theorem as Golub-Kahan or as a sequence of
   Householder/Givens annihilations.
4. If real Householder product representability is recovered from the final
   orthogonal factors, its theorem name and docstring must say final-factor
   product, not step trace.

### Optional New Files

If the elementary two-sided construction becomes large, add dedicated modules:

```text
MatDecompFormal/Instances/Bidiagonalization/Householder.lean
MatDecompFormal/Instances/Bidiagonalization/Givens.lean
```

These files should supply concrete boundary step oracles plus trace data. They
should import `Strategy`, `Direct`, and the relevant QR elementary product
modules.

## Implementation Order

1. Build the baseline:

   ```bash
   lake build MatDecompFormal.Instances.Bidiagonalization
   ```

2. Finalize structural-to-product forgetful lemmas in `Details.lean`.
3. Rename or document spectral theorems in `Spectral.lean` as existence-only.
4. Expose `exists_unitary_bidiagonalization_boundary_framework` as the
   framework-facing theorem.
5. Add real left/right Householder product data by reusing QR product
   representability for final `U` and `V`.
6. Add Givens product data only if both final factors have verified Givens
   product witnesses.
7. Implement exact two-sided trace records only after the boundary step oracle
   exposes the active row/column boundary, left step, right step, and progress
   proof.
8. Rebuild after each checkpoint.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.Bidiagonalization
lake build MatDecompFormal.Instances
rg -n "Spectral|Boundary|boundary|Householder|Givens|trace|Trace|Product|bidiagonal" MatDecompFormal/Instances/Bidiagonalization -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Bidiagonalization -S -g '*.lean'
```

Manual review criteria:

- spectral, boundary-framework, product, and trace theorem names are distinct;
- the public theorem cited for framework integration routes through
  `BidiagonalizationBoundaryStepOracle` or its proof data;
- Householder/Givens product theorems include product witnesses for both left
  and right factors;
- no theorem claims a Golub-Kahan or elementary trajectory without a two-sided
  trace record.
