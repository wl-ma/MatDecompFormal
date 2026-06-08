# LU Audit Fix Plan

This plan describes the code changes needed after the Instances decomposition
audit. It supplements `PLAN.md`; do not overwrite the original plan.

## Audit Finding

`exists_lu` and `exists_lu_of_noPivotReady` are mathematically sound and are
well integrated with the square strategy framework. The weak point is
architectural: the public leading-principal-minor criterion currently has a
separate hand-written induction path, which weakens the paper claim that the
framework absorbs the repeated proof pattern.

## Goal

Keep the no-pivot LU theorem unchanged, but route the nonrecursive determinant
criterion through the existing recursive readiness/framework theorem.

Target public shape:

```lean
theorem exists_lu_of_nonzeroProperLeadingPrincipalMinors
    ... (A : Matrix ι ι R)
    (hA : HasNoZeroLUPivots A) :
    HasLU A
```

The proof should be:

```text
HasNoZeroLUPivots A
  -> LURecursivePivotReady A
  -> exists_lu / exists_lu_of_noPivotReady
  -> HasLU A
```

The theorem name may stay compatible with the current public API.

## Required Changes

1. Audit `NonrecursiveCriterion.lean` and identify the theorem or lemma that
   converts the determinant-style condition into `LURecursivePivotReady`.
2. If this conversion is missing, add it as a bridge lemma. The lemma should
   prove readiness only; it should not construct the LU factors directly.
3. Replace the hand-written induction in the public criterion theorem with a
   call to the framework-routed LU theorem.
4. Keep the existing `HasLU` statement and factor predicates unchanged.
5. Preserve all current public theorem names where possible.

## Non-Goals

- Do not make LU unconditional. PLU remains the unconditional pivoting theorem.
- Do not change the meaning of `LURecursivePivotReady` unless the existing
  definition is provably too weak or too strong.
- Do not duplicate PLU pivoting logic inside LU.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.LU
lake build MatDecompFormal.Instances
rg -n "exists_lu_of_nonzeroProperLeadingPrincipalMinors" MatDecompFormal/Instances/LU -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/LU -S
```

Manual review criterion: the public leading-principal-minor theorem should call
the recursive readiness bridge and the framework theorem, not run its own
matrix-size induction.
