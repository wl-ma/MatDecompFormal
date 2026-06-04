# Schur Upper Triangularization via the Descent Framework

This plan describes how to formalize Schur-type upper triangularization using
the project descent-template style, with scalar assumptions kept as weak as the
chosen theorem permits.

## 1. Target Theorems

Generic algebraic triangularization over an algebraically closed field:

```lean
theorem exists_schur_upper_triangular
    {K ι : Type*} [Field K] [IsAlgClosed K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    ∃ P : Matrix ι ι K, ∃ T : Matrix ι ι K,
      InvertibleMatrix P ∧
      T.IsUpperTriangular ∧
      A = P * T * P⁻¹
```

Unitary Schur form is stronger and should be a separate corollary over
`RCLike`, usually `ℂ`:

```lean
theorem exists_unitary_schur_upper_triangular
    {𝕜 ι : Type*} [RCLike 𝕜]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι 𝕜) :
    ∃ Q : Matrix ι ι 𝕜, ∃ T : Matrix ι ι 𝕜,
      IsUnitaryMatrix Q ∧
      T.IsUpperTriangular ∧
      A = Q * T * Qᴴ
```

The generic theorem needs eigenvalues, hence algebraic closedness or an explicit
eigenvector oracle. It should not require `ℂ` unless proving the unitary version.

## 2. Predicate

Use mathlib `Matrix.IsUpperTriangular` if it works well with arbitrary finite
linear orders. Otherwise define a local scalar-parametric predicate and bridge
it later.

```lean
def HasSchur (A : Matrix ι ι K) : Prop :=
  ∃ P T, InvertibleMatrix P ∧ T.IsUpperTriangular ∧ A = P * T * P⁻¹
```

For the unitary corollary:

```lean
def HasUnitarySchur (A : Matrix ι ι 𝕜) : Prop :=
  ∃ Q T, IsUnitaryMatrix Q ∧ T.IsUpperTriangular ∧ A = Q * T * Qᴴ
```

## 3. Descent Shape

Generic field route:

1. Choose an eigenvector using `[IsAlgClosed K]` or a `SchurEigenOracle`.
2. Extend the eigenvector to a basis, not necessarily orthonormal.
3. Build an invertible change-of-basis matrix `P₁`.
4. Show `B = P₁⁻¹ * A * P₁` has zero lower-left block.
5. Recurse on `B.toBlocks₂₂`.
6. Lift by block-diagonal invertible extension.
7. Transport back by similarity.

Unitary route:

1. Normalize the eigenvector.
2. Extend it to an orthonormal basis.
3. Use unitary similarity and the same lower-left-zero recursion.

## 4. Framework Mapping

### Transformation

Generic:

```lean
B = P⁻¹ * A * P
```

Unitary corollary:

```lean
B = Qᴴ * A * Q
```

### Reduction

Use the lower-right head-tail submatrix:

```lean
slice B = B.toBlocks₂₂
```

### Readiness

After head-tail reindexing:

```lean
B'.toBlocks₂₁ = 0
```

The top-right block is arbitrary.

### Measure

Use `Fintype.card ι`.

## 5. Required Lemmas

- `InvertibleMatrix` identity/product/block-diagonal extension.
- Generic similarity transport for `HasSchur`.
- Optional unitary transport for `HasUnitarySchur`.
- Base case for empty/subsingleton index types.
- Reindex invariance of upper triangularity.
- Block lift: `fromBlocks A₁₁ A₁₂ 0 T₂₂` is upper triangular if `T₂₂` is.
- Eigenvector existence over `[IsAlgClosed K]`.
- Basis extension from one nonzero vector over a field.
- Optional orthonormal-basis extension over `RCLike`.

Initial generic oracle:

```lean
structure SchurStepOracle
    (K ι : Type*) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  P : Matrix ι ι K → Matrix ι ι K
  invertible_P : ∀ A, InvertibleMatrix (P A)
  ready : ∀ A, SchurDescentReady ((P A)⁻¹ * A * (P A))
```

## 6. File Layout

```text
MatDecompFormal/Instances/Schur/PLAN.md
MatDecompFormal/Instances/Schur.lean
MatDecompFormal/Instances/Schur/Details.lean
MatDecompFormal/Instances/Schur/Strategy.lean
MatDecompFormal/Instances/Schur/Direct.lean
MatDecompFormal/Instances/Schur/Existence.lean
```

## 7. Implementation Order

1. Define generic `HasSchur`.
2. Define optional `HasUnitarySchur` separately.
3. Prove base cases and block upper-triangular lift.
4. Build the square descent strategy with invertible similarity.
5. Add conditional framework theorem through the square driver.
6. Prove generic similarity transport.
7. Discharge the step oracle using algebraically closed field eigenvectors.
8. Add `RCLike`/unitary corollary only after the generic theorem is stable.

## 8. Relation to Hessenberg

Hessenberg reduction is useful algorithmic preprocessing, but Schur existence can
be proved directly by eigenvector descent. Share transport and block lemmas, but
keep algebraic assumptions explicit and layered.


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
lake build MatDecompFormal.Instances.Schur
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Schur -S
```
