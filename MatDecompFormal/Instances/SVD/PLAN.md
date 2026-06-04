# Singular Value Decomposition via the Descent Framework

This plan describes how to prove singular value decomposition using the project
rectangular descent framework. SVD is inherently an inner-product theorem, so a
unitary statement cannot be made over an arbitrary field. Still, the plan should
avoid hardcoding `ℂ` into every layer: generic zero/diagonal/block machinery
should be scalar-parametric, and the final analytic theorem should use the
weakest practical inner-product scalar class.

## 1. Target Theorem

Primary theorem over `RCLike` scalars, with a specialized `ℂ` theorem as a
corollary if needed:

```lean
theorem exists_svd
    {𝕜 m n : Type*} [RCLike 𝕜]
    [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    [LinearOrder m] [LinearOrder n]
    (A : Matrix m n 𝕜) :
    ∃ U : Matrix m m 𝕜, ∃ V : Matrix n n 𝕜, ∃ Σ : Matrix m n 𝕜,
      IsUnitaryMatrix U ∧
      IsUnitaryMatrix V ∧
      IsRectangularDiagonalNonnegative Σ ∧
      A = U * Σ * Vᴴ
```

If existing normal/Hermitian spectral lemmas are only available over `ℂ`, first
prove:

```lean
theorem exists_svd_complex ... (A : Matrix m n ℂ) : HasSVD A
```

but keep definitions and block lemmas generic enough to later generalize.

## 2. Predicate Layering

Use scalar-parametric rectangular diagonal shape:

```lean
structure RectangularDiagonalData
    {R m n : Type*} [Zero R]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (S : Matrix m n R) where ...
```

Nonnegativity of singular values requires an ordered real-valued payload and
therefore belongs to the `RCLike`/analytic layer:

```lean
def IsRectangularDiagonalNonnegative (S : Matrix m n 𝕜) : Prop := ...
```

## 3. Mathematical Route

Preferred route via `Aᴴ * A`:

1. Prove Hermitian/positive semidefinite facts in the weakest scalar setting
   supported by mathlib, ideally `RCLike`.
2. Use the normal/Hermitian spectral theorem. If that theorem is currently only
   available over `ℂ`, isolate the dependency in an oracle/corollary.
3. Build singular values, left singular vectors, complete bases, and the
   rectangular diagonal matrix.

## 4. Descent Shape

The recursive shape stays rectangular and unitary:

1. Find a right singular vector and singular value `σ ≥ 0`.
2. Complete left/right vectors to unitary bases.
3. Transform `B = U₁ᴴ * A * V₁`.
4. Show the off-diagonal head row/column blocks vanish and the head scalar is
   `(σ : 𝕜)`.
5. Recurse on the lower-right block.
6. Lift by block-diagonal unitary extension.
7. Transport back.

## 5. Framework Mapping

Use the rectangular driver:

```lean
RectStrategyData
mkRectSubtypeInductionInstanceFromStrategy
RectSubtypeInductionInstance.prove_for_matrix
```

Measure:

```lean
min (Fintype.card m) (Fintype.card n)
```

Step oracle should be parameterized by the scalar class actually needed:

```lean
structure SVDSimilarityOracle
    (𝕜 m n : Type*) [RCLike 𝕜]
    [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  U : Matrix m n 𝕜 → Matrix m m 𝕜
  V : Matrix m n 𝕜 → Matrix n n 𝕜
  unitary_U : ∀ A, IsUnitaryMatrix (U A)
  unitary_V : ∀ A, IsUnitaryMatrix (V A)
  descentReady : ∀ A, SVDDescentReady ((U A)ᴴ * A * (V A))
```

## 6. Required Lemmas

- Generic zero matrix and rectangular diagonal data lemmas over `[Zero R]`.
- `RCLike` unitary transport.
- `RCLike` block-diagonal unitary extension.
- SVD block lift from a ready head-tail matrix and tail SVD.
- Hermitian positive-semidefinite spectral step.
- Orthonormal-basis matrix bridge, shared with Normal.

## 7. File Layout

```text
MatDecompFormal/Instances/SVD.lean
MatDecompFormal/Instances/SVD/Details.lean
MatDecompFormal/Instances/SVD/Strategy.lean
MatDecompFormal/Instances/SVD/Direct.lean
MatDecompFormal/Instances/SVD/Existence.lean
MatDecompFormal/Instances/SVD/PLAN.md
```

## 8. Implementation Order

1. Keep diagonal/zero/block infrastructure scalar-parametric where possible.
2. Keep unitary and nonnegative singular-value statements in the `RCLike` layer.
3. Route the conditional theorem through the rectangular framework.
4. Prove transport and block lift concretely.
5. Discharge the singular-vector oracle using spectral theory.
6. Expose `exists_svd`; add `exists_svd_complex` only as a specialization.

## 9. Algebra-Minimality Policy

- Do not use `ℂ` in definitions that only need `Zero`, `AddCommMonoid`, or
  `Semiring`.
- Use `RCLike` for conjugate transpose/unitary/inner-product facts where mathlib
  supports it.
- Use `ℂ` only where the available spectral theorem forces it, and isolate that
  dependency in theorem names.


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

```bash
lake build MatDecompFormal.Instances.SVD
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/SVD -S
```

## 11. Current Status

Completed framework-facing milestones:

- Rectangular subtype driver support.
- SVD target, zero/base cases, two-sided unitary transport.
- Concrete head-tail block lift from tail SVD.
- Framework-routed theorem chain:
  `exists_svd_framework`, `exists_svd_framework_oracle`,
  `exists_svd_framework_blockOracle`,
  `exists_svd_framework_headSingularVectorData`,
  `exists_svd_framework_headBasisData`.
- Right Gram spectral layer for `Aᴴ * A`:
  `svdRightGram`, Hermitian/positive-semidefinite facts, right eigenvalues,
  singular values, right eigenbasis, and right unitary.
- Basis-level matrix bridge:
  `SVDHeadBasisData`, `svdHeadBasisData_entry`, and
  `svdHeadSingularVectorDataOfHeadBasisData`.
- Right-image inner-product bridge:
  `image_star_dotProduct_image_eq_gram`,
  `svdRightBasis_image_star_dotProduct_image`,
  `star_dotProduct_orthonormalBasis_apply`,
  `svdRightBasis_star_dotProduct`, and
  `svdRightBasis_image_star_dotProduct_image_of_ne`.
- Positive singular-pair head-vector bridge:
  `svdRightBasis_image_star_dotProduct_image_self`,
  `svdSingularValue_sq`, `svdSingularValue_mul_self_complex`,
  `svdRightBasis_image_ne_zero_of_pos_eigenvalue`,
  `svdLeftHeadVectorOfPositive`,
  `svdLeftHeadVectorOfPositive_star_dotProduct_self`,
  `svdRightBasis_image_eq_singularValue_smul_leftHead`,
  `svdLeftHeadVectorOfPositive_head_row_zero`, and
  `svdLeftHeadVectorOfPositive_head_entry`.

Remaining mathematical step:

- Construct `SVDHeadBasisData` from the right Gram spectral data by selecting
  a head right singular vector, finishing the zero singular-value case,
  extending the positive-case left head vector to an orthonormal basis, and
  wiring the completed bases into the framework-routed theorem.
