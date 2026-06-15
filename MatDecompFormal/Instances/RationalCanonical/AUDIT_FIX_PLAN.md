# Rational Canonical Audit Fix Plan

This document is the implementation plan for strengthening the rational
canonical form instance. It supplements `PLAN.md`; do not overwrite the
original plan. The goal is to expose the algebraic block data produced by the
framework and module bridge, while avoiding claims of an executable rational
canonical algorithm.

## Audit Finding

The rational canonical theorem should be an arbitrary-field theorem. Its proof
is necessarily bridge-heavy: it uses finite-dimensional `K[X]` module structure
and cyclic summands, then converts that data into companion blocks consumed by
the square descent framework. This is a valid existence proof, but the public
API should expose the canonical block witness data instead of hiding everything
behind an unstructured oracle.

## Target Theorem Layers

### 1. Framework Oracle Layer

Keep the low-level framework theorem:

```lean
theorem exists_rational_canonical_matrix_framework
    (oracle : RationalCanonicalStepOracle K) ... :
    HasRationalCanonical A
```

This theorem is the square-descent assembly theorem. It is not, by itself, the
complete public rational canonical theorem unless the oracle is supplied by a
bridge theorem.

### 2. Block Framework Layer

Expose the block-size descent route:

```lean
theorem exists_rational_canonical_matrix_block_framework ...
theorem rationalCanonicalBlockData_block_framework ...
```

This layer should use a cyclic-block oracle and return final canonical block
data, not only a bare `HasRationalCanonical` proposition.

### 3. Module Bridge Layer

Expose bridge theorems that build the required oracle or block data from the
polynomial-module decomposition:

```lean
theorem exists_rational_canonical_matrix_module_bridge ...
theorem rationalCanonicalBlockData_module_bridge ...
theorem exists_rational_canonical_matrix_polynomial_block_bridge ...
theorem rationalCanonicalBlockData_polynomial_block_bridge ...
```

These theorem names should make the bridge route visible.

### 4. Public Existence and Public Block Data

The final theorem surface should include both:

```lean
theorem exists_rational_canonical_matrix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {K : Type v} [Field K] (A : Matrix ι ι K) :
    HasRationalCanonical A

theorem rationalCanonicalBlockData
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {K : Type v} [Field K] (A : Matrix ι ι K) :
    RationalCanonicalBlockData A
```

The existence theorem should be a forgetful wrapper around block data whenever
possible.

## Required Witness Data

Use existing companion and block predicates. The block witness should not
invent a parallel canonical shape definition.

```lean
structure RationalCanonicalBlockData (A : Matrix ι ι K) where
  P : Matrix ι ι K
  T : Matrix ι ι K
  P_inv : Matrix ι ι K
  hP : HasMatrixInverse P P_inv
  canonical_T : IsRationalCanonicalMatrix T
  final_eq : A = P * T * P_inv
```

If richer block metadata is already available, refine this structure with:

- list or sigma family of companion blocks;
- monic polynomial proof for each block polynomial;
- positive degree proof where required;
- block-order or divisibility relation for canonical ordering;
- cardinality and block-size equality proofs.

Add a route-tagged bridge wrapper only as bookkeeping:

```lean
structure RationalCanonicalBridgeBlockData (tag : String) (A : Matrix ι ι K) where
  data : RationalCanonicalBlockData A
```

The tag records proof route, not algorithmic trace.

## File-Level Plan

### `Details.lean`

1. Keep:

   ```lean
   RationalCanonicalMatrixData
   IsRationalCanonicalMatrix
   HasRationalCanonical
   ```

2. Add or keep:

   ```lean
   RationalCanonicalBlockData
   RationalCanonicalBridgeBlockData
   RationalCanonicalTrace
   ```

3. Use prefixed theorem names to avoid global namespace collisions with Jordan:

   ```lean
   hasRationalCanonical_of_blockData
   rationalCanonicalBlockData_of_hasRationalCanonical
   rationalCanonicalBlockData_of_bridgeBlockData
   rationalCanonicalBridgeBlockData_of_blockData
   ```

4. Add forgetful lemmas from bridge and block data to
   `HasRationalCanonical`.
5. Keep base, reindex, block diagonal, and companion matrix theorems as the
   local algebraic shape library.

### `Strategy.lean` and `Direct.lean`

1. Keep `RationalCanonicalStepOracle`,
   `RationalCanonicalHeadTailBlockReady`, and related readiness predicates as
   the descent interface.
2. Add no module-theory assumptions here. This layer should remain the generic
   matrix descent framework.
3. Ensure the head-tail lift theorem records the companion head block and tail
   canonical theorem strongly enough for block-data extraction.

### `ModuleBridge.lean`

1. Keep the `K[X]` module definitions and cyclic summand certificates visible.
2. The bridge must expose named data structures, such as:

   ```lean
   RationalCanonicalPolynomialModuleData
   RationalCanonicalPolynomialModuleDecompositionData
   RationalCanonicalSelectedCyclicSummand
   RationalCanonicalCyclicBlockStepData
   RationalCanonicalModuleStepData
   RationalCanonicalPolynomialModuleBridge
   ```

3. Convert bridge data into the exact framework oracle:

   ```lean
   rationalCanonicalStepOracleOfModuleBridge
   ```

4. Add block-data theorems:

   ```lean
   rationalCanonicalBlockData_module_bridge
   rationalCanonicalBlockData_polynomial_module_bridge
   ```

5. Do not hide the PID/module-structure theorem behind an uninformative
   `Classical.choose`; if choice is used, the chosen object should be a named
   bridge data structure with stated invariants.

### `BlockStrategy.lean`

1. Keep the block-step oracle:

   ```lean
   RationalCanonicalBlockStepOracle
   RationalCanonicalPolynomialBlockBridge
   ```

2. Build the block framework theorem and block-data theorem:

   ```lean
   exists_rational_canonical_matrix_block_framework
   rationalCanonicalBlockData_block_framework
   ```

3. Build the public theorem chain:

   ```text
   polynomial module/block bridge
   rationalCanonicalBlockData_polynomial_block_bridge
   rationalCanonicalBlockData
   exists_rational_canonical_matrix
   ```

4. Add comments near `exists_rational_canonical_matrix` showing this route.

### `Existence.lean`

1. Keep only framework assembly and oracle-conditional theorem statements here.
2. Public unconditional theorems should live in `BlockStrategy.lean` or a file
   that imports the module bridge, so the dependency route is explicit.

## Implementation Order

1. Build baseline:

   ```bash
   lake build MatDecompFormal.Instances.RationalCanonical.Details
   lake build MatDecompFormal.Instances.RationalCanonical.ModuleBridge
   lake build MatDecompFormal.Instances.RationalCanonical.BlockStrategy
   ```

2. Finalize `RationalCanonicalBlockData` and namespaced conversion lemmas in
   `Details.lean`.
3. Ensure framework lift lemmas in `Strategy.lean` and `Direct.lean` expose
   enough data for block-data extraction.
4. In `ModuleBridge.lean`, construct a named bridge object from the polynomial
   module decomposition and convert it to a step oracle.
5. In `BlockStrategy.lean`, prove the block framework theorem and then the
   public block-data theorem.
6. Make `exists_rational_canonical_matrix` a forgetful wrapper from
   `rationalCanonicalBlockData`.
7. Recheck the dependency on strengthened `ModuleStructure` and Smith/module
   predicates after those modules are repaired.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.RationalCanonical
lake build MatDecompFormal.Instances
rg -n "Oracle|Bridge|Block|Data|exists_rational_canonical|trace|Trace|Classical.choose" MatDecompFormal/Instances/RationalCanonical -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/RationalCanonical -S -g '*.lean'
```

Manual review criteria:

- the public theorem route is readable as framework plus module/block bridge;
- public block data is available independently of the final existence theorem;
- canonical block predicates include companion shape and ordering/divisibility
  invariants where the local definition requires them;
- the theorem remains over `[Field K]`, not an algebraically closed field;
- bridge data is not advertised as an executable rational canonical algorithm.
