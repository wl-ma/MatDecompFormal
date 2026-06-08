# Hessenberg Upper Reduction via the Descent Framework

This plan describes how to formalize upper Hessenberg reduction using the same
project descent-template style as the existing decomposition instances.

The main design constraint is algebraic minimality: the primary theorem should
not default to `ℂ` or a unitary statement unless that structure is genuinely
needed. Inner-product/unitary variants should be layered as corollaries.

## 1. Target Theorems

Primary target: similarity to upper Hessenberg form over a field.

```lean
theorem exists_hessenberg_reduction
    {R ι : Type*} [Field R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) :
    ∃ P : Matrix ι ι R, ∃ H : Matrix ι ι R,
      InvertibleMatrix P ∧
      IsUpperHessenberg H ∧
      A = P * H * P⁻¹
```

A unitary strengthening should be separate:

```lean
theorem exists_unitary_hessenberg_reduction
    {𝕜 ι : Type*} [RCLike 𝕜]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι 𝕜) :
    ∃ Q : Matrix ι ι 𝕜, ∃ H : Matrix ι ι 𝕜,
      IsUnitaryMatrix Q ∧
      IsUpperHessenberg H ∧
      A = Q * H * Qᴴ
```

If upper triangularization is the endpoint, keep it as a Schur theorem rather
than folding it into Hessenberg reduction.

## 2. Predicate

Define upper Hessenberg generically in the scalar type:

```lean
def IsUpperHessenberg
    {R ι : Type*} [Zero R] [LinearOrder ι] (H : Matrix ι ι R) : Prop :=
  ∀ i j, indexDistBelow i j > 1 → H i j = 0
```

Because arbitrary finite `ι` does not have subtraction-friendly coordinates,
prefer one of these encodings:

1. Use a rank map `rankOf : ι → Fin (Fintype.card ι)` induced by the
   `LinearOrder`.
2. State the predicate after reindexing to `Fin (Fintype.card ι)`.
3. Use a head-tail recursive predicate: the tail block is upper Hessenberg and
   the lower-left column has zeros below the first tail head.

The third option best matches the descent framework.

## 3. Descent Shape

For a nontrivial square matrix:

1. Split `ι` by `headTailEquiv`.
2. Reindex `A` into block form.
3. Use an invertible tail transformation to zero out all entries below the first
   entry in the first-column tail vector.
4. Recurse on the lower-right block.
5. Lift the tail Hessenberg witness by block-diagonal invertible extension.
6. Reindex back and transport through similarity.

Over `RCLike`, the step can be strengthened to a unitary Householder/Givens
step, but the generic theorem should use only invertibility.

## 4. Framework Mapping

### Transformation

Generic transformation:

```lean
B = P⁻¹ * A * P
```

where `P` is invertible. For the unitary corollary:

```lean
B = Qᴴ * A * Q
```

### Reduction

Use lower-right head-tail submatrix reduction:

```lean
slice B = B.toBlocks₂₂
```

Tail index:

```lean
HessenbergTailIdx ι := { i : ι // i ≠ headElem }
```

### Measure

Use `Fintype.card ι`; removing the head strictly decreases the measure.

## 5. Required Lemmas

- Generic `InvertibleMatrix` helpers: identity, multiplication, inverse,
  block-diagonal extension.
- `IsUpperHessenberg` base cases for empty/subsingleton index types.
- Reindex invariance for the chosen Hessenberg predicate.
- Block characterization of upper Hessenberg form.
- Similarity transport:

  ```lean
  HasHessenberg B → B = P⁻¹ * A * P → InvertibleMatrix P → HasHessenberg A
  ```

- Tail lift from a ready head-tail block and a tail Hessenberg witness.
- Column-zeroing step over `[Field R]`; Householder/Givens only for the unitary
  corollary.

Initial oracle:

```lean
structure HessenbergStepOracle
    (R ι : Type*) [Field R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  P : Matrix ι ι R → Matrix ι ι R
  invertible_P : ∀ A, InvertibleMatrix (P A)
  ready : ∀ A, HessenbergDescentReady ((P A)⁻¹ * A * (P A))
```

## 6. File Layout

```text
MatDecompFormal/Instances/Hessenberg/PLAN.md
MatDecompFormal/Instances/Hessenberg.lean
MatDecompFormal/Instances/Hessenberg/Details.lean
MatDecompFormal/Instances/Hessenberg/Strategy.lean
MatDecompFormal/Instances/Hessenberg/Direct.lean
MatDecompFormal/Instances/Hessenberg/Existence.lean
```

## 7. Implementation Order

1. Define scalar-parametric `IsUpperHessenberg` and `HasHessenberg`.
2. Define or reuse `InvertibleMatrix`.
3. Prove base cases.
4. Build the square descent strategy with invertible similarity.
5. Add a conditional framework theorem with `HessenbergStepOracle`.
6. Prove generic similarity transport.
7. Prove block lift.
8. Discharge the field-level step oracle.
9. Add optional unitary/RCLike corollary.


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

## 8. Verification

```bash
lake build MatDecompFormal.Instances.Hessenberg
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Hessenberg -S
```
