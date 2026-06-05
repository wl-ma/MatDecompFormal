# Givens Orthogonal Hessenberg Plan

This plan adds an explicit Givens-rotation one-step oracle for
`OrthogonalHessenberg`.  It must use the same boundary-column descent template
already used by `Concrete.lean` and `Real.lean`; only the construction of the
one-step clearing matrix changes.

## 1. Goal

Provide algorithmic Givens versions of the existing public Hessenberg theorems.

Complex/unitary target:

```lean
theorem exists_unitary_hessenberg_reduction_givens
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasUnitaryHessenberg A
```

Real/orthogonal target:

```lean
theorem exists_orthogonal_hessenberg_reduction_givens
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    HasOrthogonalHessenberg A
```

Both final theorems should be wrappers around the existing recursive drivers:

```lean
exists_unitary_hessenberg_reduction givensUnitaryBoundaryStepOracle A
exists_orthogonal_hessenberg_reduction_of_oracle givensOrthogonalBoundaryStepOracle A
```

## 2. Files

Recommended layout:

```text
MatDecompFormal/Instances/OrthogonalHessenberg/Givens/Complex.lean
MatDecompFormal/Instances/OrthogonalHessenberg/Givens/Real.lean
MatDecompFormal/Instances/OrthogonalHessenberg/Givens.lean
```

`Givens.lean` should re-export the real and complex files.  The top-level
`OrthogonalHessenberg.lean` should import it only after the target modules
build.

## 3. Required API

Work at the boundary-column level.  For a positive boundary universe object
`x_sub`, construct a matrix `Q` such that:

```lean
IsUnitaryMatrix Q
HessenbergBoundaryReady
  (unitaryHessenbergBoundarySimilarityObject
    (x_sub : HessenbergBoundaryUniverse ℂ) Q)
```

and similarly over `ℝ`:

```lean
IsOrthogonalMatrix Q
HessenbergBoundaryReady
  (orthogonalHessenbergBoundarySimilarityObject
    (x_sub : HessenbergBoundaryUniverse ℝ) Q)
```

The resulting oracle names should be:

```lean
noncomputable def givensUnitaryBoundaryStepOracle :
    UnitaryHessenbergBoundaryStepOracle

noncomputable def givensOrthogonalBoundaryStepOracle :
    OrthogonalHessenbergBoundaryStepOracle
```

## 4. Sweep Construction

The Givens step clears the active boundary column one coordinate at a time.

Let `head := headElem`.  For each tail coordinate `i ≠ head`, construct a
two-coordinate rotation acting on `(head, i)` so that the `i`-coordinate of the
current vector becomes zero.  The final step matrix is a product:

```lean
Q = G₁ * G₂ * ... * Gₖ
```

The ready condition should be proved from:

```lean
Qᴴ *ᵥ x = scalar • e_head
```

or, over `ℝ`:

```lean
Qᵀ *ᵥ x = scalar • e_head
```

The sweep order should be deterministic.  Prefer the finite linear order
already available on `ι`; do not rely on arbitrary `Finset` iteration unless
the product-order lemma is explicit.

## 5. Reuse Existing QR Givens Code

Before defining new matrices, inspect:

```text
MatDecompFormal/Instances/QR/Givens.lean
```

Reuse existing definitions and lemmas when possible:

- real Givens 2x2 blocks;
- embedded pair rotations;
- orthogonality of embedded rotations;
- product orthogonality;
- transpose/product reversal lemmas.

If QR's Givens API is specialized to QR's column sweep, add small adapter
lemmas in the new Givens files instead of changing QR behavior.

## 6. Complex Route

The complex route needs unitary Givens rotations, not merely real orthogonal
rotations.  If no reusable complex Givens API exists, stage the work as:

1. prove the real orthogonal Givens oracle first;
2. add complex two-coordinate unitary rotations;
3. prove product-unitary and coordinate-zeroing lemmas;
4. package `givensUnitaryBoundaryStepOracle`.

Do not state `exists_unitary_hessenberg_reduction_givens` until the complex
unitary oracle is actually proved.

## 7. Proof Obligations

Minimum local lemmas:

```lean
theorem givens_boundary_step_unitary :
    IsUnitaryMatrix (givensBoundaryStepQ x_sub)

theorem givens_boundary_step_ready :
    HessenbergBoundaryReady
      (unitaryHessenbergBoundarySimilarityObject _ (givensBoundaryStepQ x_sub))

theorem givens_real_boundary_step_orthogonal :
    IsOrthogonalMatrix (givensRealBoundaryStepQ x_sub)

theorem givens_real_boundary_step_ready :
    HessenbergBoundaryReady
      (orthogonalHessenbergBoundarySimilarityObject _ (givensRealBoundaryStepQ x_sub))
```

Then package the oracle and invoke the existing recursive theorem.  Do not
duplicate the recursive Hessenberg lift.

## 8. Verification

Required checks:

```bash
lake build MatDecompFormal.Instances.OrthogonalHessenberg.Givens
lake build MatDecompFormal.Instances.OrthogonalHessenberg
rg -n "\b(sorry|admit|axiom|unsafe|undefined)\b" \
  MatDecompFormal/Instances/OrthogonalHessenberg -g '*.lean' -S
```

The Givens files should contain no placeholders when marked complete.

