# Schur Audit Fix Plan

This plan describes the code changes needed after the Instances decomposition
audit. It supplements `PLAN.md`; do not overwrite the original plan.

## Audit Finding

The current Schur instance proves algebraic upper triangularization over an
algebraically closed field using an arbitrary invertible similarity. This is
mathematically correct, but it is not the standard unitary Schur theorem from
complex numerical linear algebra.

## Goal

Keep the existing algebraic triangularization theorem and make the unitary
Schur theorem a separate, stronger API.

Existing theorem should be documented and named as algebraic triangularization:

```lean
theorem exists_schur ... :
  ∃ P T, InvertibleMatrix P ∧ T.IsUpperTriangular ∧ A = P * T * P⁻¹
```

Optional stronger theorem:

```lean
theorem exists_unitary_schur
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    ∃ Q T, IsUnitaryMatrix Q ∧ T.IsUpperTriangular ∧ A = Q * T * Qᴴ
```

## Required Changes

1. Ensure names and comments for the current theorem say algebraic
   triangularization, not unitary Schur.
2. If the paper needs a unitary Schur claim, add a separate schema/predicate:
   `HasUnitarySchur`.
3. Reuse the existing descent shape when possible:
   - choose eigenvector;
   - extend to an orthonormal basis;
   - recurse on the tail block;
   - lift by block diagonal unitary extension.
4. If orthonormal-basis completion is not currently available, expose an
   explicit `UnitarySchurStepOracle` rather than weakening the statement.
5. Add forgetful lemma:

   ```lean
   HasUnitarySchur A -> HasSchur A
   ```

## Non-Goals

- Do not replace the algebraic theorem with a complex-only theorem.
- Do not make `P` unitary in `HasSchur`; create a separate predicate.
- Do not use the name "unitary Schur" for the current invertible-similarity
  theorem.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.Schur
lake build MatDecompFormal.Instances
rg -n "HasSchur|HasUnitarySchur|exists_schur|exists_unitary_schur" MatDecompFormal/Instances/Schur -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Schur -S
```

Manual review criterion: the public API must make it impossible to confuse
algebraic triangularization with unitary Schur decomposition.
