# Householder Orthogonal Hessenberg Plan

This plan adds an explicit Householder one-step oracle for
`OrthogonalHessenberg`.  It must use the same boundary-column descent template
already used by `Concrete.lean` and `Real.lean`; only the construction of the
one-step clearing matrix changes.

## 1. Goal

Provide algorithmic Householder versions of the existing public Hessenberg
theorems.

Complex/unitary target:

```lean
theorem exists_unitary_hessenberg_reduction_householder
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasUnitaryHessenberg A
```

Real/orthogonal target:

```lean
theorem exists_orthogonal_hessenberg_reduction_householder
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    HasOrthogonalHessenberg A
```

Both final theorems should be wrappers around the existing recursive drivers:

```lean
exists_unitary_hessenberg_reduction householderUnitaryBoundaryStepOracle A
exists_orthogonal_hessenberg_reduction_of_oracle householderOrthogonalBoundaryStepOracle A
```

## 2. Files

Recommended layout:

```text
MatDecompFormal/Instances/OrthogonalHessenberg/Householder/Complex.lean
MatDecompFormal/Instances/OrthogonalHessenberg/Householder/Real.lean
MatDecompFormal/Instances/OrthogonalHessenberg/Householder.lean
```

`Householder.lean` should re-export the real and complex files.  The top-level
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
noncomputable def householderUnitaryBoundaryStepOracle :
    UnitaryHessenbergBoundaryStepOracle

noncomputable def householderOrthogonalBoundaryStepOracle :
    OrthogonalHessenbergBoundaryStepOracle
```

## 4. One-Step Construction

Let the active boundary column be `c : Matrix ι Unit K`, and let
`x : EuclideanSpace K ι` be the corresponding vector.

Degenerate cases:

1. If `c = 0`, use `Q = 1`.
2. If all entries below `headElem` are already zero, use `Q = 1`.

Nondegenerate Householder step:

```lean
e₀ := standard basis vector at headElem
α  := phase/sign chosen from x headElem
v  := x + α * ‖x‖ • e₀
Q  := I - (2 / ⟪v, v⟫) • (v ⬝ vᴴ)
```

Over `ℝ`, `α` is a sign.  Over `ℂ`, use the phase-adjusted version that avoids
cancellation.  The proof should establish:

```lean
Qᴴ *ᵥ x = scalar • e₀
```

or, over `ℝ`:

```lean
Qᵀ *ᵥ x = scalar • e₀
```

The boundary-ready theorem follows by reading off all coordinates not equal to
`headElem`.

## 5. Reuse Existing QR Householder Code

Before defining new matrices, inspect:

```text
MatDecompFormal/Instances/QR/Householder.lean
```

Reuse existing definitions and lemmas when possible:

- real Householder matrices;
- orthogonality of Householder matrices;
- transpose stability;
- product/transport helpers.

If QR's Householder API is specialized to QR's head-column setup, add small
adapter lemmas in the new Householder files instead of changing QR behavior.

## 6. Proof Obligations

Minimum local lemmas:

```lean
theorem householder_boundary_step_unitary :
    IsUnitaryMatrix (householderBoundaryStepQ x_sub)

theorem householder_boundary_step_ready :
    HessenbergBoundaryReady
      (unitaryHessenbergBoundarySimilarityObject _ (householderBoundaryStepQ x_sub))

theorem householder_real_boundary_step_orthogonal :
    IsOrthogonalMatrix (householderRealBoundaryStepQ x_sub)

theorem householder_real_boundary_step_ready :
    HessenbergBoundaryReady
      (orthogonalHessenbergBoundarySimilarityObject _ (householderRealBoundaryStepQ x_sub))
```

Then package the oracle and invoke the existing recursive theorem.  Do not
duplicate the recursive Hessenberg lift.

## 7. Verification

Required checks:

```bash
lake build MatDecompFormal.Instances.OrthogonalHessenberg.Householder
lake build MatDecompFormal.Instances.OrthogonalHessenberg
rg -n "\b(sorry|admit|axiom|unsafe|undefined)\b" \
  MatDecompFormal/Instances/OrthogonalHessenberg -g '*.lean' -S
```

The Householder files should contain no placeholders when marked complete.

