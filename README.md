# MatDecompFormal

## Project Overview

`MatDecompFormal` is a Lean 4 + Mathlib repository for formalizing matrix decomposition
existence proofs with a reusable "transformation + reduction + induction" framework.
The repository is still research-oriented: some parts are stable enough to use, while
other parts remain internal or unfinished.

## Current Status

The project currently has completed PLU and QR existence proof pipelines for square
matrices, organized around reusable abstractions and framework code. It also contains a
Cholesky-style result over `ℝ`, packaged from Mathlib's `LDL` theory.

This is not yet a finished library of matrix decomposition existence theorems. Some
internal modules are incomplete, and several directions are still under development.

## Implemented

- `PLU`: existence theorems for square matrices over a field, both in the `Fin n` world
  and the `FinEnum`-indexed formulation.
- `QR`: existence theorems for square real matrices, both on the internal `Fin` layer
  and on the external `FinEnum` presentation layer.
- `Cholesky`: a Cholesky-style `LDL` packaging for positive definite real square matrices.
- Reusable framework pieces for decomposition schemas, reduction strategies, and subtype
  induction over matrix universes.
- Reusable component lemmas for permutation, triangularity, reindexing, block lifting,
  and reduction steps used by the PLU and QR developments.

## Not Yet Finished

- `RowEchelon` is not yet finalized and still contains `sorry`; it is kept as an
  internal module and is not part of the public aggregate exports.
- `Rank` is currently a retained property-layer module rather than a completed instance
  line.
- Some modules remain preparatory or internal even though the PLU and QR public instance
  lines are complete.

## Repository Layout

- `MatDecompFormal/Abstractions`: decomposition schemas, transformations, and reduction strategies.
- `MatDecompFormal/Framework`: universe setup and induction machinery.
- `MatDecompFormal/Components`: reusable matrix properties, reductions, transformations, and block lifting.
- `MatDecompFormal/Instances`: concrete exposed instance developments (`PLU`, `QR`,
  and the conditional `Cholesky` wrapper).

## Build

```bash
lake build
```

## Entry Points

- `import MatDecompFormal`
  Use this as the full public entry point. It exposes the abstractions, components,
  framework layers, and the currently exported instances.
- `import MatDecompFormal.Instances`
  Use this to access just the currently exposed concrete instances: `PLU`, `QR`, and
  the conditional `Cholesky` wrapper.
