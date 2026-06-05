# Orthogonal Hessenberg Reduction Plan

This plan separates the orthogonal/unitary Hessenberg theorem from the existing
ordinary Hessenberg instance.  The current `Hessenberg` files prove similarity
by arbitrary invertible elementary transformations.  This instance should prove
the stronger statement where every transformation is orthogonal/unitary and the
inverse is the transpose/conjugate transpose.

## 1. Target Theorems

Real orthogonal form:

```lean
theorem exists_orthogonal_hessenberg_reduction
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    ∃ Q : Matrix ι ι ℝ, ∃ H : Matrix ι ι ℝ,
      IsOrthogonalMatrix Q ∧
      IsUpperHessenberg H ∧
      A = Q * H * Qᵀ
```

Unitary form over `RCLike` should be the primary reusable theorem if the
mathlib API is more mature for conjugate transpose:

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

The real theorem can then be a specialization of the unitary theorem, or it can
use a real-specific orthogonal API if that makes proofs shorter.

## 2. Predicate Layer

Do not replace the existing `HasHessenberg`; introduce a stronger predicate.

```lean
def HasUnitaryHessenberg
    {𝕜 ι : Type*} [RCLike 𝕜]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι 𝕜) : Prop :=
  ∃ Q : Matrix ι ι 𝕜, ∃ H : Matrix ι ι 𝕜,
    IsUnitaryMatrix Q ∧
    IsUpperHessenberg H ∧
    A = Q * H * Qᴴ
```

Add a bridge theorem:

```lean
theorem hasHessenberg_of_hasUnitaryHessenberg
    (h : HasUnitaryHessenberg A) : HasHessenberg A
```

This keeps the stronger theorem available without weakening or rewriting the
ordinary Hessenberg instance.

## 3. Step Construction

The ordinary implementation uses elementary non-orthogonal column clearing.
Orthogonal Hessenberg must instead use Householder or Givens transformations.

For a nontrivial head-tail block matrix

```lean
A = fromBlocks A₁₁ A₁₂ A₂₁ A₂₂
```

construct a unitary tail transformation `Qtail` such that

```lean
Qtailᴴ * A₂₁
```

has all entries below its first tail coordinate equal to zero.  Lift it to the
parent by the block diagonal matrix

```lean
Qstep = fromBlocks 1 0 0 Qtail
```

and transform

```lean
B = Qstepᴴ * A * Qstep
```

Then `B` has the first-column Hessenberg boundary condition and the recursive
problem is the lower-right block `B₂₂`.

## 4. Householder Route

Householder is the preferred one-step construction because it zeros a whole tail
column in one transformation.

Required local API:

```lean
def householderVector (x : Fin n → 𝕜) : Fin n → 𝕜
def householderMatrix (x : Fin n → 𝕜) : Matrix (Fin n) (Fin n) 𝕜
```

Key lemmas:

```lean
theorem householder_unitary :
    IsUnitaryMatrix (householderMatrix x)

theorem householder_maps_to_axis :
    ∀ i, i ≠ 0 →
      (householderMatrix x)ᴴ.mulVec x i = 0
```

Degenerate case: if the tail vector already has zero entries below the first
coordinate, use `1`.  If the vector is nonzero but the leading coordinate causes
the standard Householder denominator to vanish, choose the usual phase/sign to
avoid cancellation.

Over `ℝ`, this is the classical reflector using

```lean
v = x + sign(x₀) * ‖x‖ * e₀
H = I - (2 / ⟪v, v⟫) • (v ⬝ vᵀ)
```

Over `RCLike`, use the phase-adjusted complex version.

## 5. Givens Alternative

If Householder normalization is too heavy in mathlib, use Givens rotations.
Repeatedly zero the entries below the first tail coordinate:

```lean
G_kᴴ * ... * G_2ᴴ * x
```

Required lemmas:

```lean
theorem givens_unitary : IsUnitaryMatrix (givens i j a b)
theorem givens_zeroes_second_coordinate :
    ...
theorem product_unitary :
    all_unitary factors → IsUnitaryMatrix (List.prod factors)
```

This route may be easier algebraically because each step is a two-coordinate
calculation, but it needs more bookkeeping over finite ordered indices.

## 6. Boundary-Aware Recursion

Reuse the main idea from `Hessenberg/Boundary.lean`: a tail similarity changes
both the tail matrix and the parent boundary column.  The orthogonal theorem
should carry the same boundary invariant, but with unitary witnesses.

Proposed boundary predicate:

```lean
def HasUnitaryHessenbergBoundary
    (A : Matrix ι ι 𝕜) (c : Matrix ι Unit 𝕜) : Prop :=
  ∃ Q : Matrix ι ι 𝕜, ∃ H : Matrix ι ι 𝕜,
    IsUnitaryMatrix Q ∧
    IsUpperHessenberg H ∧
    A = Q * H * Qᴴ ∧
    ∀ i, i ≠ headElem → (Qᴴ * c) i () = 0
```

The public theorem follows from the boundary theorem with `c = 0`.

## 7. Framework Mapping

Use the existing square-universe driver for the public square theorem and a
boundary-universe driver for the protected-column invariant.

Transformation token:

```lean
structure UnitarySimilarityToken (𝕜 ι : Type*) where
  Q : Matrix ι ι 𝕜
  unitary_Q : IsUnitaryMatrix Q
```

Transform:

```lean
B = Qᴴ * A * Q
```

Transport:

If `B = Qᴴ * A * Q` and `B = S * H * Sᴴ` with `S` unitary, then

```lean
A = (Q * S) * H * (Q * S)ᴴ
```

using unitary closure under multiplication and conjugate-transpose reversal.

Lift:

If the tail has unitary Hessenberg witness `Qtail`, lift it via

```lean
Qblk = fromBlocks 1 0 0 Qtail
```

and prove `Qblk` is unitary.  The block zero pattern is exactly the ordinary
Hessenberg lift proof, but all similarity witnesses stay unitary.

## 8. Implementation Milestones

Current Lean layout:

```text
MatDecompFormal/Instances/OrthogonalHessenberg.lean
MatDecompFormal/Instances/OrthogonalHessenberg/Concrete.lean
MatDecompFormal/Instances/OrthogonalHessenberg/Details.lean
MatDecompFormal/Instances/OrthogonalHessenberg/Strategy.lean
MatDecompFormal/Instances/OrthogonalHessenberg/Direct.lean
MatDecompFormal/Instances/OrthogonalHessenberg/Existence.lean
MatDecompFormal/Instances/OrthogonalHessenberg/Real.lean
MatDecompFormal/Instances/OrthogonalHessenberg/Householder/PLAN.md
MatDecompFormal/Instances/OrthogonalHessenberg/Givens/PLAN.md
```

Completed:

1. `Details.lean` defines `HasUnitaryHessenberg`,
   `HasUnitaryHessenbergBoundary`, and bridge lemmas to ordinary Hessenberg.
2. The implementation reuses the project `IsUnitaryMatrix` API over `ℂ`,
   including identity, multiplication, reindexing, block diagonal, and unitary
   similarity transport lemmas.
3. `Direct.lean` proves the boundary lift assuming a one-step unitary
   column-clearing oracle.
4. `Existence.lean` instantiates the `SubtypeInductionInstance` descent
   framework over the boundary universe.
5. `Existence.lean` exposes
   `exists_unitary_hessenberg_reduction`, conditional on
   `UnitaryHessenbergBoundaryStepOracle`.
6. `Concrete.lean` discharges the one-step oracle nonconstructively by extending
   the normalized active boundary column to an orthonormal basis.
7. `Concrete.lean` exposes the unconditional complex theorem
   `exists_unitary_hessenberg_reduction_complex`.
8. `Real.lean` instantiates the same boundary descent template for real
   orthogonal similarities using transpose and `IsOrthogonalMatrix`.
9. `Real.lean` discharges the real one-step oracle nonconstructively by
   extending the normalized active boundary column to a real orthonormal basis.
10. `Real.lean` exposes the unconditional real theorem
   `exists_orthogonal_hessenberg_reduction`.

Remaining:

1. Implement the explicit Householder one-step oracle according to
   `Householder/PLAN.md`.
2. Implement the explicit Givens one-step oracle according to
   `Givens/PLAN.md`.
3. Generalize from the current `ℂ` unitary API plus separate real orthogonal API
   to a reusable `RCLike` statement if the needed project-level
   conjugate-transpose/unitary lemmas are made scalar-parametric.

## 9. Non-Goals

This plan does not change `MatDecompFormal.Instances.Hessenberg`.  That instance
remains the algebraic invertible-similarity theorem.

This plan also does not prove Schur triangularization.  Hessenberg reduction is
only the first-stage reduction to upper Hessenberg form.
