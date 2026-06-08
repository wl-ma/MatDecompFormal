# Tridiagonalization Audit Fix Plan

This plan describes the code changes needed after the Instances decomposition
audit. It supplements the existing tridiagonalization implementation.

## Audit Finding

The Hermitian tridiagonalization target is mathematically valid. The caveat is
that `Spectral.lean` contains a spectral fallback, which is a non-algorithmic
existence shortcut and should not be conflated with a Householder/Givens
tridiagonalization trajectory.

## Goal

Expose the distinction between:

1. spectral existence of unitary tridiagonalization;
2. boundary-driver tridiagonalization;
3. optional Householder/Givens trajectory-aware tridiagonalization.

The public theorem used to support framework claims should route through the
boundary strategy, not only through the spectral fallback.

## Required Changes

1. Inspect `Spectral.lean` and label or alias spectral fallback theorems as
   existence-only.
2. Inspect `Boundary.lean`, `Strategy.lean`, `Direct.lean`, and `Existence.lean`
   to identify the strongest boundary-driver theorem already available.
3. If the current public theorem chooses the spectral route, add or expose a
   boundary-routed theorem with clear naming.
4. If exact algorithm trajectory is required, introduce a trace record:
   - active boundary index;
   - elementary unitary similarity step;
   - proof of Householder/Givens shape when claimed;
   - cumulative unitary factor;
   - Hermitian and tridiagonal boundary invariants.
5. Add forgetful lemmas from trace-level data to ordinary unitary
   tridiagonalization.

## Non-Goals

- Do not remove the spectral theorem; it is valid as an existence proof.
- Do not claim an algorithmic Householder/Givens route unless the trace record is
  part of the theorem data.
- Do not drop the Hermitian hypothesis from the meaningful decomposition target.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.Tridiagonalization
lake build MatDecompFormal.Instances
rg -n "Spectral|Boundary|Householder|Givens|trace|tridiagonal" MatDecompFormal/Instances/Tridiagonalization -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Tridiagonalization -S
```

Manual review criterion: the public theorem used for algorithm/framework claims
must not be only a spectral fallback unless the claim is explicitly
existence-only.
