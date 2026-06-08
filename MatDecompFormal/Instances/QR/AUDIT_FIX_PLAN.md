# QR Audit Fix Plan

This plan describes the code changes needed after the Instances decomposition
audit. It supplements the existing QR implementation; no original plan file is
being replaced.

## Audit Finding

The standard QR statement is usable. The audit caveat concerns algorithm-style
variants: Householder and Givens predicates can be recovered from general
orthogonality, so the theorem names may suggest a recorded reflector/rotation
trajectory that the proof object does not actually preserve.

## Goal

Separate structural QR existence from trajectory-aware QR variants.

The final API should make one of these facts explicit:

1. A structural theorem:

   ```lean
   exists_qr_decomposition
   ```

   only claims `A = Q * R` with an orthogonal/unitary `Q`.

2. A product-representation theorem:

   ```lean
   exists_householder_product_qr
   exists_givens_product_qr
   ```

   may state that the final orthogonal factor is representable as a product of
   reflectors/rotations, but must not claim it is the exact algorithmic trace
   unless a step sequence is recorded.

3. A trajectory theorem, if implemented:

   ```lean
   exists_householder_qr_with_trace
   exists_givens_qr_with_trace
   ```

   must include an explicit finite sequence/list/vector of transformations and
   an invariant saying their cumulative product is the final factor.

## Required Changes

1. Inspect `Householder.lean` and `Givens.lean` for lemmas of the form
   `isHouseholderProduct_of_isOrthogonalMatrix` or analogous Givens recovery.
2. Rename or add theorem aliases so recovered-product theorems are not presented
   as exact algorithm traces.
3. If a trace-level theorem is desired, define a small trace record containing:
   - the finite list of elementary reflectors or rotations;
   - a proof each step has the intended shape;
   - the cumulative product;
   - the final equation `A = Q * R`.
4. Keep the existing structural QR theorem intact.
5. Add forgetful lemmas from trace-level data to structural QR data.

## Non-Goals

- Do not weaken the standard QR theorem.
- Do not force Householder/Givens traces into the base QR schema.
- Do not claim numerical stability, pivot choices, or executable extraction.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.QR
lake build MatDecompFormal.Instances
rg -n "Householder|Givens|trace|Product" MatDecompFormal/Instances/QR -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/QR -S
```

Manual review criterion: theorem names and comments must distinguish a product
representation recovered from orthogonality from an explicitly recorded
transformation sequence.
