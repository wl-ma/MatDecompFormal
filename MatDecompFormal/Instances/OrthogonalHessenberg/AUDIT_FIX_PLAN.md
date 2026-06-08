# Orthogonal Hessenberg Audit Fix Plan

This plan describes the code changes needed after the Instances decomposition
audit. It supplements the existing orthogonal/unitary Hessenberg implementation.

## Audit Finding

The mathematical statement for orthogonal/unitary Hessenberg reduction is
appropriate. The caveat is the same as for QR: Householder and Givens variants
must not be described as preserving exact algorithmic trajectories unless the
step sequence is part of the formal data.

## Goal

Make the API distinguish:

1. existence of an orthogonal/unitary similarity to Hessenberg form;
2. existence where the final similarity factor is representable as a
   Householder/Givens product;
3. existence with a recorded boundary-step trajectory.

Only the third item should be used to support claims about formalized
Householder or Givens reduction traces.

## Required Changes

1. Inspect:
   - `Householder/Real.lean`
   - `Householder/Complex.lean`
   - `Givens/Real.lean`
   - `Givens/Complex.lean`
   - `Concrete.lean`
2. Identify whether the current Householder/Givens predicates are obtained from
   general orthogonality/unitarity or from explicit boundary steps.
3. If they are recovered from final orthogonality, rename theorem comments or
   add aliases that say "product-representable" rather than "algorithm trace".
4. If exact trajectory support is desired, introduce a trace record containing:
   - active boundary index at each step;
   - elementary transformation matrix;
   - proof of Householder/Givens shape;
   - cumulative similarity product;
   - preservation of Hessenberg boundary invariant.
5. Add forgetful lemmas from trace-level reductions to the current ordinary
   orthogonal/unitary Hessenberg statements.

## Non-Goals

- Do not change the ordinary `exists_orthogonal_hessenberg_reduction` theorem
  unless its statement is mathematically wrong.
- Do not force the generic Hessenberg instance to use unitary/orthogonal data.
- Do not claim an executable numerical Hessenberg algorithm from a bridge-only
  existence theorem.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.OrthogonalHessenberg
lake build MatDecompFormal.Instances
rg -n "Householder|Givens|trace|boundary|Product" MatDecompFormal/Instances/OrthogonalHessenberg -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/OrthogonalHessenberg -S
```

Manual review criterion: any theorem advertised as a Householder/Givens
trajectory must expose the sequence of elementary transformations or a record
equivalent to it.
