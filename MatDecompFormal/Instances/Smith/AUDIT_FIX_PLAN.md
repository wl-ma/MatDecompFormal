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
factor divisibility chain, and keep the final public decomposition theorems
fully proved at PID scope. In particular, the final public theorems must not
take any extra oracle, bridge, chain-proof, or matrix-Smith assumption beyond
the usual algebraic hypotheses.

Required data model:

Preserve the current data-oriented representation. Do not replace the primary
diagonal index by a numeric length such as `r : Nat`, and do not make
`diag`/`row`/`col` primarily indexed by `Fin r`. The Smith data should continue
to store an arbitrary finite index type `r`, with `diag`, `row`, and `col`
indexed by that type. Do not change the core representation to
`r : Nat`/`rank : Nat` plus fields such as `diag : Fin r -> R`; `Fin` is only
allowed as an ordering/enumeration layer over the existing data-oriented
support. The separate complete ordering witness is used only to state adjacent
divisibility:

```lean
structure SmithNormalFormData
    (D : Matrix m n R) where
  r : Type u
  fintype_r : Fintype r
  order : Fin (Fintype.card r) ≃ r
  diag : r -> R
  row : r -> m
  col : r -> n
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  entry_diag : forall k, D (row k) (col k) = diag k
  entry_zero : forall i j, ... -> D i j = 0
  divides_chain :
    forall k : Fin (Fintype.card r),
      (hnext : (k : Nat) + 1 < Fintype.card r) ->
        diag (order k) ∣ diag (order ⟨(k : Nat) + 1, hnext⟩)
```

Here `Fin (Fintype.card r)` is acceptable only as a total enumeration of the
existing index type through `order`; it is not the primary representation of
the diagonal data. The ordering witness must be an equivalence from all adjacent
positions onto all diagonal indices. A partial successor relation is not
acceptable.

List/vector views may be added as helper lemmas if useful, but they must not
replace the primary data-oriented `r : Type u` representation.

## Required Changes

1. Replace the unconstrained `successor` field with a complete ordering witness,
   such as `order : Fin (Fintype.card r) ≃ r`, and state the divisibility chain
   along this order.
2. Keep `diag`, `row`, and `col` indexed by the existing finite type `r`; ensure
   the diagonal support is ordered consistently through `order` and the
   row/column embeddings remain injective.
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
   predicate and must be unconditional over a PID:

   ```lean
   theorem exists_smith_normal_form
       {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
       {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
       [Fintype n] [DecidableEq n] [LinearOrder n]
       (A : Matrix m n R) :
       HasSmithNormalForm A
   ```

   It must not have parameters such as `PIDMatrixSmithBridge R`,
   `PIDProjectionSplitBridge R`, an explicit `hchain`, an oracle, or any
   equivalent assumption that already contains the target theorem.
8. Strengthen the PID bridge enough to prove the invariant-factor chain:
   - mathlib's current `Module.Basis.SmithNormalForm` data records the diagonal
     basis shape but does not expose adjacent divisibility;
   - add a local strengthened PID Smith theorem/structure that carries both the
     mathlib diagonal basis data and the proof
     `∀ k, a k ∣ a (k + 1)`;
   - construct this strengthened data by preserving the divisibility invariant
     through the PID/submodule induction or by proving an equivalent local
     invariant-factor theorem;
   - use the strengthened data to build the final matrix-level
     `HasSmithNormalForm` without leaving a bridge hypothesis in public API.
9. Update `ModuleStructure/Existence.lean` so the public PID module-structure
   theorems also have no extra Smith bridge assumptions. They may depend on the
   unconditional `exists_smith_normal_form`, but must not expose
   `PIDMatrixSmithBridge`, `PIDProjectionSplitBridge`, or equivalent parameters.
10. Add helper lemmas showing the old data-oriented diagonal shape is still
   available if other instances only need shape.

## Non-Goals

- Do not keep arbitrary `successor` as the only divisibility structure.
- Do not replace the data-oriented `r : Type u` index in
  `SmithNormalFormData` with `r : Nat`, `Fin r`, or a list/vector primary
  representation.
- Do not claim standard SNF from a predicate that only says the matrix is
  diagonal.
- Do not replace the missing PID chain proof by an explicit bridge/oracle
  parameter in a final public theorem.
- Do not make `exists_smith_normal_form` conditional on
  `PIDMatrixSmithBridge`, `PIDProjectionSplitBridge`, or a theorem equivalent
  to itself.
- Do not solve canonical associate normalization unless needed for a specialized
  theorem over `Int` or another normalized PID.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.Smith
lake build MatDecompFormal.Instances.ModuleStructure
lake build MatDecompFormal.Instances
rg -n "successor|divides_next|divides_chain|IsSmithNormalForm|SmithNormalFormData" MatDecompFormal/Instances/Smith -S
rg -n "PIDMatrixSmithBridge|PIDProjectionSplitBridge|bridge :|hchain|oracle" MatDecompFormal/Instances/Smith MatDecompFormal/Instances/ModuleStructure -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Smith -S
```

Manual review criterion: there must be no path where the divisibility condition
for a multi-entry Smith diagonal is made vacuous by choosing an empty or partial
successor relation.

Additional manual review criteria:

- `exists_smith_normal_form` is a fully proved PID-scope theorem with no extra
  theorem-like assumptions.
- Public PID module-structure theorems expose no Smith bridge/oracle argument.
- Any remaining bridge names, if kept for internal development, are not used as
  hypotheses of public final theorems and are clearly marked internal.
- The chain proof for PID data is produced by the local strengthened PID bridge,
  not supplied by the caller.
- `SmithNormalFormData` keeps `r : Type u` with `diag`, `row`, and `col`
  indexed by `r`; any `Fin (Fintype.card r)` usage is only an ordering or
  enumeration witness and not a replacement primary data index.
