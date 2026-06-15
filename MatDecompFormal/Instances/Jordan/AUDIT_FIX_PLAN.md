# Jordan Audit Fix Plan

This document is the implementation plan for strengthening the ordinary and
generalized Jordan instances. It supplements `PLAN.md`; do not overwrite the
original plan. The goal is to make the split-field assumptions, generalized
block bridge, ordinary Jordan specialization, and optional chain-level data
explicit in the API.

## Audit Finding

The existing Jordan theorem surface is broad: it includes generalized Jordan
form, split-field ordinary Jordan form, algebraically closed corollaries, and a
complex corollary. The mathematical risk is not the final statement but the
visibility of assumptions and proof data. Ordinary Jordan form over a general
field requires a splitting hypothesis; generalized Jordan form can be routed
through rational-canonical or elementary-factor data. Neither route should be
presented as an explicit Jordan-chain construction unless chain vectors and
their relations are recorded.

## Target Theorem Layers

### 1. Generalized Jordan

Keep the arbitrary-field generalized theorem:

```lean
theorem exists_generalized_jordan_matrix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {K : Type v} [Field K] (A : Matrix ι ι K) :
    HasGeneralizedJordanMatrix A
```

Add block witness data for this theorem:

```lean
theorem generalizedJordanBlockData
    (A : Matrix ι ι K) :
    GeneralizedJordanBlockWitnessData A
```

### 2. Split-Field Ordinary Jordan

Keep the splitting hypothesis visible:

```lean
theorem exists_jordan_matrix_of_splits
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A
```

Add a block-data theorem with the same visible hypothesis:

```lean
theorem jordanBlockData_of_splits
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    JordanBlockData A
```

### 3. Algebraically Closed and Complex Corollaries

Keep corollaries as wrappers:

```lean
theorem exists_jordan_matrix_algClosed ...
theorem exists_jordan_matrix_complex ...
theorem jordanBlockData_algClosed ...
theorem jordanBlockData_complex ...
```

They should derive the required split hypothesis explicitly using the local
algebraically closed or complex polynomial splitting theorem.

### 4. Bridge and Framework Theorems

Expose the proof route:

```text
generalized RCF/elementary-factor bridge
generalized block data
split specialization
ordinary Jordan block data
public existence theorem
```

The route should be visible in theorem names and comments.

### 5. Optional Jordan Chain Data

Only add chain-level claims after defining actual chain data:

```lean
structure JordanChain (A : Matrix ι ι K) where
  eigenvalue : K
  vectors : List (ι -> K)
  nonempty_vectors : vectors ≠ []
  chain_relations : ...

structure JordanChainData (A : Matrix ι ι K) where
  chains : List (JordanChain A)
  chain_linearIndependent : ...
  chain_spans_top : ...
  basis_matrix : Matrix ι ι K
  block_matrix : Matrix ι ι K
  block_shape : IsJordanMatrix block_matrix
  final_eq : A = basis_matrix * block_matrix * basis_matrix⁻¹
```

Do not claim this layer until the vectors, independence, spanning, and
intertwining equations are proved.

## Required Witness Data

### Ordinary Jordan Block Data

Use existing final-shape predicates:

```lean
structure JordanBlockData (A : Matrix ι ι K) where
  P : Matrix ι ι K
  J : Matrix ι ι K
  P_inv : Matrix ι ι K
  hP : HasMatrixInverse P P_inv
  is_jordan : IsJordanMatrix J
  final_eq : A = P * J * P_inv
```

Route-tagged bridge data may wrap this:

```lean
structure JordanBridgeBlockData (tag : String) (A : Matrix ι ι K) where
  data : JordanBlockData A
```

### Generalized Jordan Block Data

Keep generalized data separate:

```lean
structure GeneralizedJordanBlockWitnessData (A : Matrix ι ι K) where
  P : Matrix ι ι K
  G : Matrix ι ι K
  P_inv : Matrix ι ι K
  hP : HasMatrixInverse P P_inv
  is_generalized : IsGeneralizedJordanMatrix G
  final_eq : A = P * G * P_inv
```

Use distinct theorem names for ordinary and generalized data to avoid namespace
collisions with rational canonical form and with each other:

```lean
hasJordanMatrix_of_jordanBlockData
jordanBlockData_of_hasJordanMatrix
jordanBlockData_of_jordanBridgeBlockData
jordanBridgeBlockData_of_jordanBlockData

hasGeneralizedJordanMatrix_of_generalizedJordanBlockData
generalizedJordanBlockData_of_hasGeneralizedJordanMatrix
generalizedJordanBlockData_of_generalizedBridgeBlockData
generalizedBridgeBlockData_of_generalizedJordanBlockData
```

Avoid unqualified names such as `blockData_of_bridgeBlockData` in the shared
`MatDecompFormal.Instances` namespace.

## File-Level Plan

### `Details.lean`

1. Keep:

   ```lean
   jordanBlock
   JordanMatrixData
   IsJordanMatrix
   HasJordanMatrix
   ```

2. Add or keep ordinary block witness data and conversion lemmas with
   Jordan-prefixed names.
3. Keep comments near `Jordan_P` saying the split hypothesis is theorem input,
   not hidden framework state.
4. Ensure block diagonal, reindex, unit, and singleton lemmas remain the local
   shape library for recursive proofs.

### `Generalized.lean`

1. Keep:

   ```lean
   generalizedJordanBlock
   GeneralizedJordanBlockData
   IsGeneralizedJordanMatrix
   HasGeneralizedJordanMatrix
   ```

2. Add generalized witness and bridge block data using generalized-prefixed
   theorem names.
3. Provide forgetful lemmas to `HasGeneralizedJordanMatrix`.
4. Avoid theorem names that collide with `Jordan/Details.lean` or
   `RationalCanonical/Details.lean`.

### `GeneralizedExistence.lean`

1. Keep the generalized block driver framework:

   ```lean
   GeneralizedJordanBlockDriverBridge
   exists_generalized_jordan_matrix_framework_bridge
   exists_generalized_jordan_matrix
   ```

2. Add public data theorem wrappers:

   ```lean
   generalizedJordanBlockData_framework_bridge
   generalizedJordanBlockData
   ```

3. If the route uses rational canonical form or elementary factors, leave that
   route visible in theorem names or comments.

### `ElementaryFactors.lean` and `GeneralizedCompanion.lean`

1. Keep elementary-factor companion blocks as the bridge from rational
   canonical data to generalized Jordan blocks.
2. Expose enough block metadata to prove `GeneralizedJordanBlockWitnessData`,
   especially polynomial powers, exponents, and block sizes.
3. Do not claim ordinary Jordan form from irreducible powers unless the
   splitting specialization has converted the irreducible factor to a linear
   factor.

### `Existence.lean`

1. Keep ordinary Jordan framework and RCF split bridge theorems:

   ```lean
   exists_jordan_matrix_framework_rcf_split_bridge
   exists_jordan_matrix_framework_rcf_divisibility_bridge
   exists_jordan_matrix_framework_rcf_companion_charpoly_bridge
   exists_jordan_matrix_framework_block_oracle
   ```

2. Comments should state which theorems are conditional on block/oracle data
   and which are public split-field wrappers.
3. Do not expose an unsuffixed ordinary theorem here unless its split
   hypothesis is visible.

### `SplitSpecialization.lean`

1. Keep the conversion theorem:

   ```lean
   hasJordanMatrix_of_hasGeneralizedJordanMatrix_of_splits
   ```

2. Add block-data wrappers:

   ```lean
   jordanBlockData_of_splits_generalized_bridge
   jordanBlockData_of_splits
   jordanBlockData_algClosed
   jordanBlockData_complex
   ```

3. Ensure the proof route is:

   ```text
   generalized block data
   polynomial splitting hypothesis
   ordinary Jordan block data
   public ordinary Jordan theorem
   ```

4. Keep `exists_jordan_form_*` basis-level theorems as forgetful or repackaged
   wrappers from matrix Jordan data.

### `LowDim.lean`

1. Keep low-dimensional companion-to-Jordan proofs as concrete support lemmas.
2. Do not use low-dimensional theorems as a substitute for the general split
   specialization.

## Implementation Order

1. Build the baseline:

   ```bash
   lake build MatDecompFormal.Instances.Jordan.Details
   lake build MatDecompFormal.Instances.Jordan.Generalized
   ```

2. Rename ordinary and generalized block-data conversion lemmas to the prefixed
   names listed above.
3. Add ordinary `JordanBlockData` forgetful lemmas in `Details.lean`.
4. Add generalized witness/bridge data and forgetful lemmas in
   `Generalized.lean`.
5. In `GeneralizedExistence.lean`, expose
   `generalizedJordanBlockData_framework_bridge` and
   `generalizedJordanBlockData`.
6. In `SplitSpecialization.lean`, expose `jordanBlockData_of_splits` and the
   algebraically closed/complex block-data corollaries.
7. Verify ordinary public theorems keep `hsplit` visible outside algebraically
   closed wrappers.
8. Add `JordanChainData` only after a genuine chain-vector proof exists.
9. Rebuild after each checkpoint.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.Jordan
lake build MatDecompFormal.Instances
rg -n "Jordan|Generalized|Split|Bridge|Data|trace|Trace|chain|Classical.choose" MatDecompFormal/Instances/Jordan -S
rg -n "blockData_of_bridgeBlockData|bridgeBlockData_of_blockData" MatDecompFormal/Instances/Jordan MatDecompFormal/Instances/RationalCanonical -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Jordan -S -g '*.lean'
```

Manual review criteria:

- generalized Jordan, split ordinary Jordan, algebraically closed corollaries,
  complex corollaries, block data, and future chain data are separate theorem
  layers;
- all ordinary non-algebraically-closed Jordan theorems expose the splitting
  hypothesis;
- conversion lemma names are prefixed enough to avoid namespace collisions;
- no theorem claims explicit Jordan chains unless `JordanChainData` is present
  and fully proved.
