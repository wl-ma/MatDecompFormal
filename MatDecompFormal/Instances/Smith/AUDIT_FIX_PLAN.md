# Smith Normal Form Audit Fix Plan

This plan describes the code changes needed after the Instances decomposition
audit. It supplements `PLAN.md`; do not overwrite the original plan.

## Audit Finding

`SmithNormalFormData` stores a `successor : r -> r -> Prop` and only requires
divisibility along that relation. Because the relation is not constrained to be
a linear chain through all diagonal entries, the divisibility condition can be
too weak. For example, an empty successor relation makes `divides_next`
vacuously true.

## Goal

Strengthen the Smith normal form predicate so it states the standard invariant
factor divisibility chain.

Preferred data model:

```lean
structure SmithNormalFormData
    (D : Matrix m n R) where
  r : Nat
  diag : Fin r -> R
  row : Fin r -> m
  col : Fin r -> n
  row_strictMono_or_ordered : ...
  col_strictMono_or_ordered : ...
  entry_diag : forall k, D (row k) (col k) = diag k
  entry_zero : forall i j, ... -> D i j = 0
  divides_chain : forall k : Fin (r - 1), diag k.castSucc ∣ diag k.succ
```

An ordered finite type or list-indexed representation is also acceptable if it
forces every adjacent diagonal entry to participate in the chain.

## Required Changes

1. Replace the unconstrained `successor` field with an ordered/indexed chain.
2. Ensure the diagonal support is ordered consistently with the row/column
   embedding.
3. Update zero and base cases for the new data.
4. Update reindexing lemmas.
5. Update Gauss-to-Smith bridge:
   - over a field/rank-normal-form specialization, all nonzero diagonal entries
     may be `1`;
   - the chain proof should be explicit, not vacuous through an empty successor.
6. Update Smith block lift:
   - prove the head pivot divides the first tail diagonal entry;
   - preserve the tail chain.
7. Recheck `PIDBridge.lean`; the public PID theorem must target the strengthened
   predicate.
8. Add helper lemmas showing the old data-oriented diagonal shape is still
   available if other instances only need shape.

## Non-Goals

- Do not keep arbitrary `successor` as the only divisibility structure.
- Do not claim standard SNF from a predicate that only says the matrix is
  diagonal.
- Do not solve canonical associate normalization unless needed for a specialized
  theorem over `Int` or another normalized PID.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.Smith
lake build MatDecompFormal.Instances.ModuleStructure
lake build MatDecompFormal.Instances
rg -n "successor|divides_next|divides_chain|IsSmithNormalForm|SmithNormalFormData" MatDecompFormal/Instances/Smith -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Smith -S
```

Manual review criterion: there must be no path where the divisibility condition
for a multi-entry Smith diagonal is made vacuous by choosing an empty or partial
successor relation.
