# UTV Audit Fix Plan

This plan describes the code changes needed after the Instances decomposition
audit. It supplements `PLAN.md`; do not overwrite the original plan.

## Audit Finding

`HasUTV` currently uses `IsRectangularUpperTriangular`, but that predicate is
defined as `IsRectangularDiagonalNonnegative`. The theorem is therefore closer
to an SVD-like diagonal middle-factor theorem than a traditional UTV
decomposition.

## Goal

Make the UTV middle factor genuinely rectangular upper triangular/trapezoidal,
or explicitly rename the current theorem as a diagonal/SVD-specialized UTV.

Preferred repair:

```lean
def IsRectangularUpperTriangular
    {R m n : Type*} [Zero R]
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (T : Matrix m n R) : Prop :=
  ∀ i j, rowRank i > colRank j -> T i j = 0
```

For arbitrary finite types, a recursive head-tail form is also acceptable:
lower-left block is zero and the tail block is rectangular upper triangular.

## Required Changes

1. Replace the current alias to `IsRectangularDiagonalNonnegative` with a genuine
   triangular/trapezoidal predicate.
2. Keep a separate predicate if the diagonal nonnegative theorem is still useful:

   ```lean
   def IsRectangularDiagonalUTVMiddle := IsRectangularDiagonalNonnegative
   def HasDiagonalUTV ...
   ```

3. Prove:
   - zero/base cases for the triangular predicate;
   - reindex invariance;
   - block lift from lower-left-zero ready form;
   - transport across two-sided unitary equivalence.
4. Rework any proof that currently imports SVD only to obtain the diagonal
   middle factor. SVD may prove a diagonal specialization, but ordinary UTV
   should have its own triangular middle-factor statement.
5. Keep or add forgetful lemmas:

   ```lean
   IsRectangularDiagonalNonnegative T -> IsRectangularUpperTriangular T
   HasSVD A -> HasUTV A
   ```

   These lemmas are valid only after the triangular predicate is weaker than the
   diagonal predicate, not definitionally equal to it.

## Non-Goals

- Do not define "upper triangular" as "diagonal nonnegative".
- Do not require nonnegative diagonal entries for ordinary UTV.
- Do not remove the SVD theorem or diagonal specialization if downstream code
  uses it.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.UTV
lake build MatDecompFormal.Instances
rg -n "IsRectangularUpperTriangular|IsRectangularDiagonalNonnegative|HasDiagonalUTV|HasUTV" MatDecompFormal/Instances/UTV -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/UTV -S
```

Manual review criterion: `#print IsRectangularUpperTriangular` must not reduce
to `IsRectangularDiagonalNonnegative`.
