# MatDecompFormal

## Project Overview

`MatDecompFormal` is a Lean 4 library for formalizing matrix decomposition
existence proofs. The project develops reusable abstractions for decomposition
schemas, matrix transformations, reduction methods, and well-founded induction
over matrix universes.

The current library includes formal developments for PLU and QR existence
statements, together with supporting components for permutation matrices,
triangular matrix properties, reindexing, block lifting, and reduction steps.
The repository is intended to be a relatively independent Lean formalization
library built on top of Mathlib.

## Project Structure and Main Contents

- `MatDecompFormal/Abstractions`

  Core abstract interfaces for decomposition schemas, transformations,
  reduction methods, reduction strategies, and matrix-property typeclasses.

- `MatDecompFormal/Framework`

  General framework code, including matrix universe types, `Fin` and `FinEnum`
  index bridges, and induction principles for dimension-changing reductions.

- `MatDecompFormal/Components`

  Reusable formal components for matrix properties, block algebra, reductions,
  lifting lemmas, and elementary transformations.

- `MatDecompFormal/Instances`

  Concrete matrix decomposition developments, including PLU, QR, and a
  Cholesky-style wrapper based on Mathlib's LDL theory.

- `MatDecompFormal.lean`

  The main aggregate import for the library.

## Usage

Build the project with Lake:

```bash
lake build
```

Use the full public entry point in Lean:

```lean
import MatDecompFormal
```

Use the instance-level entry point for currently exposed decomposition
developments:

```lean
import MatDecompFormal.Instances
```

The project assumes the Lean toolchain specified in `lean-toolchain` and the
dependencies pinned by `lake-manifest.json`.

## Contributors

Wanli Ma, Beijing International Center for Mathematical Research, Peking
University, China (wlma@pku.edu.cn)

Zichen Wang, School of Mathematical Sciences, Peking University, China
(zichenwang25@stu.pku.edu.cn)

Zaiwen Wen, Beijing International Center for Mathematical Research, Peking
University, China (wenzw@pku.edu.cn)

## License

Released under the Apache 2.0 license. See `LICENSE` for details.
