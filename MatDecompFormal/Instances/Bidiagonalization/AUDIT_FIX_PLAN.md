# Bidiagonalization Audit Fix Plan

This plan describes the code changes needed after the Instances decomposition
audit. It supplements the existing bidiagonalization implementation.

## Audit Finding

The current bidiagonalization statements are mathematically reasonable, but some
paths reuse SVD/spectral readiness. That proves existence but does not formalize
the independent Golub-Kahan or Householder bidiagonalization trajectory.

## Goal

Keep existence theorems, but split the API into:

1. spectral/existence bidiagonalization;
2. boundary-framework bidiagonalization;
3. optional Householder/Givens trajectory-aware bidiagonalization.

Only the third form should support claims about the exact classical algorithmic
step sequence.

## Required Changes

1. Inspect `Spectral.lean` and identify public theorems whose proof is an
   SVD/spectral fallback.
2. Rename comments or add aliases so these are clearly existence theorems.
3. Inspect `Strategy.lean`, `Direct.lean`, and `Existence.lean` for boundary
   route support.
4. Prefer a public boundary-framework theorem when discussing the recursive
   decomposition framework.
5. If an algorithm trace is needed, introduce a bidiagonalization trace record:
   - active row/column boundary;
   - left and right elementary unitary transformations;
   - proof each step is Householder or Givens when claimed;
   - cumulative `U` and `V`;
   - final upper bidiagonal invariant.
6. Add forgetful lemmas from trace-level data to ordinary bidiagonalization.

## Non-Goals

- Do not remove the spectral existence path if it is useful.
- Do not claim Golub-Kahan trajectory from a theorem proved only through SVD.
- Do not weaken the final bidiagonal shape predicate.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.Bidiagonalization
lake build MatDecompFormal.Instances
rg -n "Spectral|boundary|Householder|Givens|trace|bidiagonal" MatDecompFormal/Instances/Bidiagonalization -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Bidiagonalization -S
```

Manual review criterion: theorem names and comments must show whether the proof
is spectral/existence-only or records a concrete bidiagonalization process.
