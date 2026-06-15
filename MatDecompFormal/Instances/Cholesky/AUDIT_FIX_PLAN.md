# Cholesky Audit Fix Plan

This plan records the Cholesky audit repair. The implementation is now split
between `MatDecompFormal/Instances/LDL` and `MatDecompFormal/Instances/Cholesky`;
the top-level `MatDecompFormal/Instances/Cholesky.lean` file is a re-export.

## Audit Finding

The old `Cholesky_Schema` recorded factors `(L, D)` and only required
`D.IsDiag` with equation:

```lean
A = L * D * Lᵀ
```

This is closer to a weak LDL-style factorization than standard Cholesky. It does
not require `L` to be lower/unit-lower triangular, and it does not require
positive diagonal entries in `D`.

## Goal

Use two explicit public surfaces: a strengthened LDL theorem and a true
Cholesky theorem derived from LDL.

Preferred path for a true Cholesky claim:

```lean
def HasCholesky (A : Matrix ι ι R) : Prop :=
  ∃ L : Matrix ι ι R,
    IsLowerTriangular L ∧
    PositiveDiagonal L ∧
    A = L * Lᵀ
```

Acceptable LDL path if the existing proof infrastructure is retained:

```lean
def HasLDLDecomposition (A : Matrix ι ι R) : Prop :=
  ∃ L D : Matrix ι ι R,
    IsUnitLowerTriangular L ∧
    D.IsDiag ∧
    PositiveDiagonal D ∧
    A = L * D * Lᵀ
```

If the project keeps the theorem name `exists_cholesky_decomposition`, then the
predicate must match the standard Cholesky statement. Otherwise rename the
current theorem surface to LDL-style names and expose a separate Cholesky theorem
only when the stronger factorization is proved.

## Required Changes

1. Expose LDL separately through `MatDecompFormal.Instances.LDL`.
2. For LDL:
   - rename `Cholesky_Schema` or add `LDL_Schema`;
   - require lower/unit-lower triangularity of `L`;
   - require positivity of diagonal entries of `D`;
   - keep the recursive Schur-complement route if it can prove these properties.
3. For true Cholesky:
   - derive square-root diagonal factors from positive `D`;
   - construct `C = L * sqrt(D)` or an equivalent triangular factor;
   - prove `A = C * Cᵀ` and triangular/positive-diagonal properties.
4. Do not keep the old weak Cholesky wrapper.
5. Update comments so the theorem name and mathematical content match.

## Non-Goals

- Do not leave `HasCholesky` as only `D.IsDiag`.
- Do not rely on a direct LDL theorem as the public Cholesky theorem unless the
  missing triangularity and positivity properties are also exported.
- Do not silently break public names without adding compatibility wrappers or
  clearly documenting the rename.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances
lake build MatDecompFormal
rg -n "HasCholesky|Cholesky_Schema|LDL|PositiveDiagonal|IsUnitLowerTriangular|IsLowerTriangular" MatDecompFormal/Instances/Cholesky MatDecompFormal/Instances/LDL -g '*.lean' -S
rg -n "s[o]rry|a[d]mit|a[x]iom|u[n]safe|u[n]defined" MatDecompFormal/Instances/Cholesky MatDecompFormal/Instances/LDL MatDecompFormal/Components/Properties -g '*.lean' -S
```

Manual review criterion: the public theorem called Cholesky must no longer prove
only a weak LDL-style statement.
