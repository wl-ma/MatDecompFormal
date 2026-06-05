# Rational Canonical Form via the Descent Framework

This plan describes rational canonical form for finite-dimensional linear maps
over a field using the project descent-template style.

The theorem should not depend on `ℂ`. The natural scalar assumption is `[Field K]`.

Current Lean status: the general matrix and finite-module entry points are now
implemented over `[Field K]`:

```lean
theorem exists_rational_canonical_matrix
    {K : Type v} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasRationalCanonical A

theorem exists_rational_canonical_form
    {K : Type v} {V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (T : V →ₗ[K] V) :
    ∃ b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V,
      HasRationalCanonical (LinearMap.toMatrix b b T)
```

Both route through the cyclic block-size subtype-descent template in
`BlockStrategy.lean`, via the concrete selected-summand bridge built in
`ModuleBridge.lean`.

## 1. Target Theorem

```lean
theorem exists_rational_canonical_form
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (T : V →ₗ[K] V) :
    ∃ b : Basis (Fin (FiniteDimensional.finrank K V)) K V,
      IsRationalCanonicalMatrix (LinearMap.toMatrix b b T)
```

Matrix-indexed variant:

```lean
theorem exists_rational_canonical_matrix
    {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    ∃ P : Matrix ι ι K, ∃ C : Matrix ι ι K,
      InvertibleMatrix P ∧
      IsRationalCanonicalMatrix C ∧
      A = P * C * P⁻¹
```

## 2. Algebraic Route

View `V` as a finitely generated torsion `K[X]`-module via:

```lean
X • v = T v
```

Then apply the PID module structure theorem over `K[X]`. The invariant factors
produce companion blocks.

Dependency direction:

```text
Smith / ModuleStructure over K[X] -> Rational canonical form
```

## 3. Descent Template Instantiation

### Universe

Options:

1. `LinearOperatorUniverse K` packaging a finite-dimensional `K`-space and
   linear map `T`;
2. square matrices over `K` up to similarity;
3. finitely generated torsion `K[X]`-modules with chosen generators.

The module universe is mathematically clean; the matrix universe may fit the
existing square driver more easily.

### Measure

Use `finrank K V` or `Fintype.card ι`.

### Predicate

`P T` means `T` has rational canonical form, equivalently a basis whose matrix
is block diagonal with companion matrices of invariant factors.

### Base

Zero-dimensional vector spaces have the empty canonical matrix.

### Transform

Similarity/change of basis:

```lean
B = P⁻¹ * A * P
```

or module isomorphism for the `K[X]`-module formulation.

### Readiness

A ready object has an isolated cyclic invariant summand with annihilator
polynomial `p`, plus a smaller invariant quotient/submodule.

### Slice

The complementary invariant quotient/submodule or the remaining block after
removing one companion block.

### Reach

Use module structure theorem to find a cyclic summand. Initially isolate this as
an oracle:

```lean
structure RationalCanonicalStepOracle (K V T) where
  cyclicSummand : ...
  slice : ...
  progress : finrank slice < finrank V
  ready : RationalCanonicalDescentReady ...
```

Then discharge it from PID module structure over `K[X]`.

### Transport

Canonical form is invariant under similarity/change of basis.

### Lift

A cyclic summand with annihilator `p` gives a companion block; combine it with
the recursive rational canonical form of the slice.

### Driver

If using matrices, reuse the square driver. If using modules/linear maps, add an
`AlgebraicDescentInstance` with the same fields as the template contract.

## 4. Required Lemmas

- `K[X]` is a PID for field `K`.
- Linear map to `K[X]`-module bridge.
- Cyclic module basis gives companion matrix.
- Direct sum of invariant subspaces gives block diagonal matrix.
- Similarity transport.
- Block lift for companion block plus tail rational canonical form.

## 5. File Layout

```text
MatDecompFormal/Instances/RationalCanonical/PLAN.md
MatDecompFormal/Instances/RationalCanonical.lean
MatDecompFormal/Instances/RationalCanonical/Details.lean
MatDecompFormal/Instances/RationalCanonical/Strategy.lean
MatDecompFormal/Instances/RationalCanonical/Direct.lean
MatDecompFormal/Instances/RationalCanonical/Existence.lean
MatDecompFormal/Instances/RationalCanonical/ModuleBridge.lean
MatDecompFormal/Instances/RationalCanonical/BlockStrategy.lean
```

## 6. Current Lean Status

Implemented:

- `RationalCanonicalMatrixData`
- `SingleCompanionBlockForm`
- `companionMatrixFin`
- `IsCompanionMatrix`
- `isCompanionMatrix_companionMatrixFin`
- `singleCompanionBlockForm_companionMatrixFin`
- `isCompanionMatrix_adjoinRoot_leftMulMatrix_powerBasis`
- `singleCompanionBlockForm_adjoinRoot_leftMulMatrix_powerBasis`
- `isRationalCanonicalMatrix_companionMatrixFin`
- `hasRationalCanonical_companionMatrixFin`
- `isCompanionMatrix_unit_X_sub_C`
- `singleCompanionBlockForm_unit_X_sub_C`
- `isRationalCanonicalMatrix_unit`
- `hasRationalCanonical_unit`
- `rationalCanonicalBlockDiagLex`
- `isRationalCanonicalMatrix_blockDiag_lex`
- `hasMatrixInverse_blockDiag_lex`
- `hasRationalCanonical_blockDiag_lex`
- `isRationalCanonicalMatrix_singleCompanion`
- `IsRationalCanonicalMatrix`
- `HasRationalCanonical`
- `RationalCanonical_P`
- `base_rationalCanonical_empty`
- `rationalCanonical_transport_similarity`
- `RationalCanonicalTailIdx`
- `rationalCanonicalTailSlice`
- `RationalCanonicalLiftReady`
- `RationalCanonicalDescentReady`
- `rationalCanonicalTailSlice_eq_toBlocks₂₂`
- `RationalCanonicalHeadTailBlockReady`
- `rationalCanonicalHeadTailBlockReady_of_unit_block_eq`
- `rationalCanonicalLiftReady_of_headTailBlockReady`
- `RationalCanonicalStepOracle`
- `rationalCanonicalSimilarityTransform`
- `rationalCanonicalHeadTailReduction`
- `rationalCanonical_strategy_core`
- `rationalCanonical_transport_hook`
- `rationalCanonical_lift_hook`
- `rationalCanonical_strategy_proof`
- `rationalCanonical_base_univ`
- `rationalCanonical_strategy_data`
- `rationalCanonical_framework_inst`
- `exists_rational_canonical_matrix_framework`
- `RationalCanonicalModuleStepData`
- `RationalCanonicalModuleStructureBridge`
- `RationalCanonicalMatrixPolynomialModule`
- `RationalCanonicalPolynomialModuleData`
- `rationalCanonicalMatrixPolynomialModule_finite`
- `rationalCanonicalMatrixPolynomialModule_torsion`
- `rationalCanonicalPolynomialModuleData`
- `associated_pow`
- `quotient_span_singleton_pow_equiv_of_associated`
- `quotient_span_singleton_equiv_adjoinRoot_restrictScalars`
- `RationalCanonicalPolynomialModuleDecompositionData`
- `rationalCanonicalPolynomialModuleDecompositionData`
- `RationalCanonicalSelectedCyclicSummand`
- `RationalCanonicalSelectedCyclicSummand.quotientEquivAdjoinRoot`
- `RationalCanonicalSelectedCyclicSummandBridge`
- `RationalCanonicalEffectiveSummandIndex`
- `RationalCanonicalEffectiveSummandIndexBridge`
- `rationalCanonicalMatrixPolynomialModule_nontrivial_of_nonempty`
- `subsingleton_quotient_span_one`
- `rationalCanonicalDecomposition_quotient_subsingleton_of_all_exponents_zero`
- `directSum_subsingleton_of_forall_subsingleton`
- `piSelectedComplementEquiv`
- `directSumSelectedComplementEquiv`
- `rationalCanonicalSelectedAmbientSplit`
- `RationalCanonicalSelectedTailModule`
- `rationalCanonicalSelectedTailModule_finite`
- `rationalCanonicalSelectedTailBasis`
- `rationalCanonicalSelectedAmbientBasis`
- `rationalCanonicalSelectedVectorBasis`
- `rationalCanonicalSelectedTailFinBasis`
- `rationalCanonicalSelectedVectorFinBasis`
- `rationalCanonicalSelectedBasisMatrix`
- `rationalCanonicalSelectedVectorFinBasis_card_eq`
- `rationalCanonicalSelectedIndexEquiv`
- `rationalCanonicalSelectedReindexedBasis`
- `rationalCanonicalSelectedSquareBasisMatrix`
- `rationalCanonicalSelectedSquareBasisMatrixInv`
- `rationalCanonicalSelectedSquareBasisMatrix_inverse`
- `rationalCanonicalSelectedBasisLinearMapMatrix`
- `rationalCanonicalSelectedBasisLinearMapMatrix_eq_similarity`
- `rationalCanonicalDecomposition_exists_positive_exponent`
- `rationalCanonicalEffectiveSummandIndexOfDecomposition`
- `rationalCanonicalEffectiveSummandIndexBridge`
- `rationalCanonicalSelectedCyclicSummandOfIndex`
- `rationalCanonicalSelectedCyclicSummandBridgeOfEffectiveIndexBridge`
- `RationalCanonicalPolynomialModuleBridge`
- `rationalCanonicalModuleStructureBridgeOfPolynomialModuleBridge`
- `rationalCanonicalStepOracleOfModuleBridge`
- `exists_rational_canonical_matrix_module_bridge`
- `exists_rational_canonical_matrix_polynomial_module_bridge`
- `exists_rational_canonical_form_module_bridge`
- `RationalCanonicalBlockStepOracle`
- `RationalCanonicalSelectedCompanionBlock`
- `rationalCanonicalSelectedCompanionBlock`
- `RationalCanonicalPolynomialBlockStepData`
- `RationalCanonicalPolynomialBlockBridge`
- `rationalCanonicalBlockStepOracleOfPolynomialBlockBridge`
- `rationalCanonicalBlockStep`
- `rationalCanonicalBlockStepMatrix`
- `rationalCanonicalBlockSliceUniverse`
- `rationalCanonicalBlockSliceData`
- `rationalCanonicalBlock_transport`
- `rationalCanonicalBlock_lift`
- `rationalCanonicalBlockProofData`
- `rationalCanonicalBlockReach`
- `rationalCanonical_block_framework_inst`
- `exists_rational_canonical_matrix_block_framework`
- `exists_rational_canonical_matrix_polynomial_block_bridge`
- `exists_rational_canonical_form_polynomial_block_bridge`

Current target data is intentionally stronger than a vacuous marker:

- every `RationalCanonicalMatrixData.invariantFactor` is monic;
- every block size is positive;
- `blockSize b = (invariantFactor b).natDegree`;
- total block size is `Fintype.card ι`;
- `RationalCanonicalMatrixData.blockIndexEquiv` explicitly decomposes the
  ambient matrix index as `(b : block) × Fin (blockSize b)`;
- `RationalCanonicalMatrixData.block_form` proves that after this reindexing
  the matrix is the dependent block diagonal matrix of the concrete companion
  matrices `companionMatrixFin (invariantFactor b)`;
- every `RationalCanonicalModuleStepData` carries a monic cyclic annihilator,
  a positive cyclic block size, and
  `cyclic_blockSize = cyclic_annihilator.natDegree`;
- every `RationalCanonicalModuleStepData` must now supply structured
  one-index head-tail block data for `Pinv * A * P`: a `head : Matrix Unit Unit K`
  and an equality showing that the head-tail reindexing is
  `rationalCanonicalBlockDiagLex head tail`; `RationalCanonicalModuleStepData.headTailReady`
  converts this into `RationalCanonicalHeadTailBlockReady`;
- `RationalCanonicalCyclicBlockStepData` records the mathematically correct
  variable-size cyclic companion block step: a block index, tail index,
  similarity matrices, a monic cyclic annihilator, an explicit companion head
  block, and a block-diagonal equation after reindexing;
- `RationalCanonicalHeadTailBlockReady.head_isRC` requires the one-index head
  block itself to satisfy `IsRationalCanonicalMatrix`, not merely to be similar
  to some rational-canonical matrix;
- `SingleCompanionBlockForm` is the current one-block companion payload entry
  point.  It already requires monicity, positive degree, degree/card equality,
  and the explicit `IsCompanionMatrix` predicate.  The standard matrix
`companionMatrixFin p` is now verified by
`singleCompanionBlockForm_companionMatrixFin`,
`isRationalCanonicalMatrix_companionMatrixFin`, and
`hasRationalCanonical_companionMatrixFin`.  The bridge from cyclic quotients to
companion blocks has also started: for monic `p`,
`isCompanionMatrix_adjoinRoot_leftMulMatrix_powerBasis` proves that multiplication
by `AdjoinRoot.root p` in `AdjoinRoot.powerBasis'` is exactly this companion
matrix, and `singleCompanionBlockForm_adjoinRoot_leftMulMatrix_powerBasis`
packages it as a verified one-block payload.  The `ULift` version
`singleCompanionBlockForm_adjoinRoot_leftMulMatrix_powerBasis_ulift` lets this
head block live in the same universe as arbitrary matrix indices.
- For the one-index square descent head, every `Unit × Unit` block is now
  concretely identified with the companion matrix of `X - C a` through
  `isCompanionMatrix_unit_X_sub_C`,
  `singleCompanionBlockForm_unit_X_sub_C`,
  `isRationalCanonicalMatrix_unit`, and `hasRationalCanonical_unit`.

The Lean universe parameters for the rational-canonical details are separated:
the scalar field lives in `Type v`, while matrix indices and block labels live
in `Type u`.  This avoids forcing standard block indices such as
`Fin p.natDegree` into the same universe as `K`.

The core framework theorem is intentionally oracle-routed:

```lean
theorem exists_rational_canonical_matrix_framework
    {K : Type v} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        RationalCanonicalStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasRationalCanonical A
```

This is assembled through `SquareSubtypeInductionInstance.prove_for_matrix`.
There is now also a named module-structure entry point:

```lean
theorem exists_rational_canonical_matrix_module_bridge
    {K : Type v} [Field K]
    (bridge : RationalCanonicalModuleStructureBridge.{u, v} K)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasRationalCanonical A
```

This theorem is still routed through the same square descent driver: the bridge
is converted into `RationalCanonicalStepOracle` by
`rationalCanonicalStepOracleOfModuleBridge`, then discharged by
`SquareSubtypeInductionInstance.prove_for_matrix`.

The module bridge has also been refined to the concrete polynomial-module
source attached to a matrix:

```lean
abbrev RationalCanonicalMatrixPolynomialModule
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :=
  Module.AEval' (Matrix.toLin' A)

theorem rationalCanonicalMatrixPolynomialModule_torsion
    {K : Type v} {ι : Type u} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :
    Module.IsTorsion K[X] (RationalCanonicalMatrixPolynomialModule K ι A)
```

The torsion proof is no longer an assumption: it is derived from
Cayley-Hamilton using `LinearMap.aeval_self_charpoly`.  The finite
`K[X]`-module instance comes from the finite `K`-space structure of `ι → K`.
The PID decomposition data is also no longer just a plan item:

```lean
structure RationalCanonicalPolynomialModuleDecompositionData
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) where
  idx : Type v
  fintype_idx : Fintype idx
  prime : idx → K[X]
  prime_irreducible : ∀ i, Irreducible (prime i)
  exponent : idx → Nat
  decomposition :
    Nonempty <|
      RationalCanonicalMatrixPolynomialModule K ι A ≃ₗ[K[X]]
        DirectSum idx (fun i => K[X] ⧸ K[X] ∙ prime i ^ exponent i)
```

It is constructed from `Module.equiv_directSum_of_isTorsion`, using the
canonical finite/torsion data above.  The still-open bridge is now the named
`RationalCanonicalPolynomialModuleBridge`, whose `stepData` receives both the
canonical finite torsion module data and this PID direct-sum decomposition data,
then must produce the one-index descent step.  It specializes to
`RationalCanonicalModuleStructureBridge` via
`rationalCanonicalModuleStructureBridgeOfPolynomialModuleBridge`.

The finite-dimensional linear-operator wrapper is also present:

```lean
theorem exists_rational_canonical_form_module_bridge
    {K : Type v} {V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (bridge : RationalCanonicalModuleStructureBridge.{u, v} K)
    (T : V →ₗ[K] V) :
    ∃ b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V,
      HasRationalCanonical (LinearMap.toMatrix b b T)
```

It reindexes `Module.finBasis K V` to `ULift (Fin (Module.finrank K V))` and
calls
`exists_rational_canonical_matrix_module_bridge`, so the actual decomposition
proof remains matrix descent-template routed.

The reusable block-combination part of the lift is now implemented:
`hasRationalCanonical_blockDiag_lex` combines a head block and a recursive tail
block over the lexicographic sum index used by the project head-tail template.
The strategy layer packages the exact expected one-step shape as
`RationalCanonicalHeadTailBlockReady`: after `headTailLexEquiv`, the transformed
matrix is `rationalCanonicalBlockDiagLex head tail`, where `tail` is precisely
`rationalCanonicalTailSlice`.  The theorem
`rationalCanonicalLiftReady_of_headTailBlockReady` converts this structured
shape into the lift predicate consumed by `SquareStrategyLiftType`.
The convenience constructor `rationalCanonicalHeadTailBlockReady_of_unit_block_eq`
builds this structured readiness directly from the one-index block equation,
using `isRationalCanonicalMatrix_unit` for the head block.

Important correction: the existing square head-tail template removes a
`Unit × Unit` head block.  That is a valid conditional skeleton, but it is too
strong for the unconditional rational canonical theorem over an arbitrary
field.  A cyclic summand for an irreducible polynomial of degree greater than
one generally contributes an indecomposable companion block with no one-
dimensional invariant direct summand over `K`.  Therefore the general
`[Field K]` theorem cannot honestly discharge
`RationalCanonicalModuleStepData` at every step merely by decomposing a cyclic
summand into one-index block-diagonal steps.

The concrete cyclic-block step is now constructed from the provided PID
decomposition data: it isolates a cyclic summand, identifies its companion
basis, and produces `RationalCanonicalCyclicBlockStepData`.  The final
unconditional theorem is routed through a project descent-template driver that
removes a positive-size block, not through an invalid one-dimensional
invariant-head oracle.

Important template constraint: the current project `SquareStrategyCore` fixes
the slice index type from the ambient index type by removing the distinguished
head element.  A cyclic summand of degree `d` cannot be removed as a
variable-size block by this existing square driver without extending the
framework.  Under the hard requirement that the final theorem use a descent
template, the active plan is to add a framework-level cyclic/block-slice driver
with the same template contract:

```text
cyclic block transform
  -> smaller tail slice
  -> measure drops by Fintype.card blockIdx
  -> block-diagonal companion lift
  -> subtype/descent prove_for_matrix analogue
```

The already implemented one-index theorem remains useful as a conditional
framework skeleton and for decompositions where a genuine one-dimensional
invariant head is available, but it is not the final general `[Field K]`
rational canonical route.

The block-size descent template is now implemented in `BlockStrategy.lean`.
It does not bypass recursion: it instantiates the lower-level
`SquareSliceData`/`SquareProofData` path and assembles
`rationalCanonical_block_framework_inst` with `mkSquareSubtypeInductionInstance`.
The theorem
`exists_rational_canonical_matrix_block_framework` is conditional on
`RationalCanonicalBlockStepOracle`.

The polynomial-module-to-block bridge is also named:

```lean
structure RationalCanonicalSelectedCyclicSummand
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K)
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A)

The selected summand does not assume the PID prime is already monic.  It
records a monic associated `cyclic_factor`, its positive exponent, the monic
annihilator `cyclic_factor ^ exponent`, positive degree, and a quotient
equivalence from the raw PID quotient to the monic quotient.
The quotient equivalence can be discharged by
`quotient_span_singleton_pow_equiv_of_associated`, after proving the selected
monic factor is associated to the PID factor.
The helper `rationalCanonicalSelectedCyclicSummandOfIndex` constructs this
payload from a concrete summand index plus positive exponent using polynomial
normalization under `classical`; its public signature remains over `[Field K]`.

The selection obligation is split further and the effective-index part is now
constructed:

```lean
structure RationalCanonicalEffectiveSummandIndex
    (K : Type v) (ι : Type u) [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K)
    (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A)

structure RationalCanonicalEffectiveSummandIndexBridge
    (K : Type v) [Field K] where
  choose :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      (A : Matrix ι ι K) →
        RationalCanonicalPolynomialModuleData K ι A →
          (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) →
            RationalCanonicalEffectiveSummandIndex K ι A decomposition
```

The effective-index bridge is implemented by
`rationalCanonicalEffectiveSummandIndexBridge`.  Its proof uses
`rationalCanonicalMatrixPolynomialModule_nontrivial_of_nonempty`: if every PID
exponent were zero, each quotient would be `K[X] ⧸ K[X] ∙ 1`, hence
subsingleton, so the finite direct sum and therefore the canonical module would
be subsingleton, contradicting nontriviality of the positive-dimensional
underlying vector space.  `rationalCanonicalSelectedCyclicSummandBridgeOfEffectiveIndexBridge`
then promotes this smaller combinatorial bridge to the full selected-summand
bridge by normalizing the chosen irreducible factor to a monic associated
polynomial.  The selected summand also has
`RationalCanonicalSelectedCyclicSummand.quotientEquivAdjoinRoot`, a `K`-linear
identification of the raw selected PID quotient with `AdjoinRoot` of the monic
annihilator.  This uses the stored `K[X]`-linear quotient equivalence and the
fact that `AdjoinRoot p` is definitionally `K[X] ⧸ (p)` as a `K`-vector space.

structure RationalCanonicalSelectedCyclicSummandBridge
    (K : Type v) [Field K] where
  select :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      (A : Matrix ι ι K) →
        RationalCanonicalPolynomialModuleData K ι A →
          (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) →
            RationalCanonicalSelectedCyclicSummand K ι A decomposition

structure RationalCanonicalPolynomialBlockBridge
    (K : Type v) [Field K] where
  stepData :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      (A : Matrix ι ι K) →
        RationalCanonicalPolynomialModuleData K ι A →
          (decomposition : RationalCanonicalPolynomialModuleDecompositionData K ι A) →
            RationalCanonicalSelectedCyclicSummand K ι A decomposition →
              RationalCanonicalPolynomialBlockStepData K ι A decomposition selected
```

It converts to `RationalCanonicalBlockStepOracle` through
`rationalCanonicalBlockStepOracleOfPolynomialBlockBridge`, and the theorem
`exists_rational_canonical_matrix_polynomial_block_bridge` discharges the final
matrix statement through the block-size subtype-descent driver.  The
`RationalCanonicalPolynomialBlockStepData` wraps the emitted matrix block step
with consistency proofs:

```lean
step.cyclic_annihilator = selected.annihilator
step.cyclic_blockSize = selected.annihilator.natDegree
```

This bridge is now concrete.  `rationalCanonicalPolynomialBlockBridge` is built
from `rationalCanonicalSelectedAlgebraicBlockCertificateBridge`, then combined
with
`rationalCanonicalSelectedCyclicSummandBridgeOfEffectiveIndexBridge
rationalCanonicalEffectiveSummandIndexBridge` by
`exists_rational_canonical_matrix`.  Thus the final public matrix theorem no
longer takes a bridge or oracle parameter.

The head-block part of `stepData` is now factored out:
`rationalCanonicalSelectedCompanionBlock` builds the standard companion block
with index `ULift (Fin selected.annihilator.natDegree)` and proof
`SingleCompanionBlockForm head selected.annihilator`.  The PID direct-sum
splitting entrance is also factored out:
`directSumSelectedComplementEquiv` splits a finite direct sum into the selected
summand and the direct sum over complementary indices, using
`piSelectedComplementEquiv` plus `DirectSum.linearEquivFunOnFintype`.
`rationalCanonicalSelectedAmbientSplit` composes this split with the PID
decomposition and `selected.quotientEquivAdjoinRoot`, giving a `K`-linear
equivalence from the canonical matrix module to
`AdjoinRoot selected.annihilator × tail`.
The first basis layer is now factored out as well:
`RationalCanonicalSelectedTailModule` names the complement,
`rationalCanonicalSelectedTailModule_finite` proves it finite-dimensional over
`K` by projecting the finite canonical matrix module through the split,
`rationalCanonicalSelectedTailBasis` chooses a vector-space basis of the tail,
and `rationalCanonicalSelectedAmbientBasis` combines the selected AdjoinRoot
power basis with that tail basis and maps it back to the canonical matrix
module.  The basis is now also transferred back to the underlying vector space:
`rationalCanonicalSelectedVectorBasis` maps it through
`(Module.AEval'.of (Matrix.toLin' A)).symm`, `rationalCanonicalSelectedTailFinBasis`
and `rationalCanonicalSelectedVectorFinBasis` give a Fin-indexed version of the
tail and whole selected/tail basis, and `rationalCanonicalSelectedBasisMatrix`
records the columns of this basis in the standard `Pi.basisFun` coordinates.
The selected/tail index is now also squared up:
`rationalCanonicalSelectedVectorFinBasis_card_eq` proves its cardinality is
`Fintype.card ι`, `rationalCanonicalSelectedIndexEquiv` chooses the ambient
index equivalence, `rationalCanonicalSelectedReindexedBasis` reindexes the basis
by `ι`, and `rationalCanonicalSelectedSquareBasisMatrix` gives the square
candidate `P`.  `rationalCanonicalSelectedSquareBasisMatrixInv` and
`rationalCanonicalSelectedSquareBasisMatrix_inverse` supply the corresponding
`Pinv` and `HasMatrixInverse` witness.  The matrix-level similarity has also
been tied back to the selected basis:
`rationalCanonicalSelectedBasisLinearMapMatrix` is the matrix of
`Matrix.toLin' A` in the selected/tail basis, and
`rationalCanonicalSelectedBasisLinearMapMatrix_eq_similarity` proves it is
exactly `Pinv * A * P`.

The block equation is isolated as a precise selected/tail certificate:
`RationalCanonicalSelectedBlockStepCertificate` contains
`SingleCompanionBlockForm (rationalCanonicalSelectedSplitHead selected)
selected.annihilator` and `RationalCanonicalSelectedSplitBlockEquation selected`.
The mechanical conversion from that certificate to the actual cyclic block
descent payload is implemented by
`rationalCanonicalCyclicBlockStepDataOfSelectedCertificate`.  It constructs the
ULift-indexed block and tail types required by the square subtype driver,
chooses the selected-basis `P` and `Pinv`, proves the inverse, fills the block
size/progress numerology, and transports the Fin-indexed selected/tail split to
the driver universe.

The block bridge layer has also been narrowed:
`RationalCanonicalSelectedBlockStepCertificateBridge` asks only for the
selected/tail certificate, and
`rationalCanonicalPolynomialBlockBridgeOfSelectedCertificateBridge` turns it
into `RationalCanonicalPolynomialBlockBridge`.  The concrete algebraic bridge
is now implemented by
`rationalCanonicalSelectedAlgebraicBlockCertificateBridge`, so the driver
assembly, step-data plumbing, and selected/tail matrix certificate are all
discharged in Lean.

The certificate is now split one level further.  The matrix block equation can
be supplied by `RationalCanonicalSelectedSplitBlockCertificate`, which only asks
for the two off-diagonal blocks of
`rationalCanonicalSelectedSplitLinearMapMatrix selected` to be zero; the theorem
`rationalCanonicalSelectedSplitBlockEquation_of_certificate` turns this into
`RationalCanonicalSelectedSplitBlockEquation selected`.  The head block proof
can be supplied by `RationalCanonicalSelectedHeadCompanionCertificate`, an
equality identifying the head block with `Algebra.leftMulMatrix` for
`AdjoinRoot.root`; `rationalCanonicalSelected_head_companion_of_certificate`
turns that equality into `SingleCompanionBlockForm`.  These two facts are
bundled by `RationalCanonicalSelectedAlgebraicBlockCertificate`, and
`rationalCanonicalSelectedBlockStepCertificateOfAlgebraicCertificate` converts
the finer certificate into the selected block-step certificate.

The raw `K[X]`-linear split is now named separately as
`rationalCanonicalSelectedRawAmbientSplit`, before the selected quotient is
transported to `AdjoinRoot` as a `K`-linear space.  This gives two direct action
lemmas:
`rationalCanonicalSelectedRawAmbientSplit_head_X_smul` and
`rationalCanonicalSelectedRawAmbientSplit_tail_X_smul`.  The standard quotient
identification also has the action lemma
`quotient_span_singleton_equiv_adjoinRoot_restrictScalars_X_smul`, proving that
the `K[X]` action of `X` on `K[X] ⧸ (p)` becomes multiplication by
`AdjoinRoot.root p`.

That selected quotient transport has now been completed.  The normalized
intermediate equivalence is
`RationalCanonicalSelectedCyclicSummand.quotientEquivCyclicFactorAdjoinRoot`,
with action lemma
`RationalCanonicalSelectedCyclicSummand.quotientEquivCyclicFactorAdjoinRoot_X_smul`.
The equality transport through `selected.annihilator_eq` is handled by
`adjoinRootLinearEquivOfEq` and `adjoinRootLinearEquivOfEq_root_mul`, giving the
selected action theorem
`RationalCanonicalSelectedCyclicSummand.quotientEquivAdjoinRoot_X_smul`.

The selected ambient split has also been lifted from the raw `K[X]` split:
`rationalCanonicalSelectedAmbientSplit_head_X_smul` says the selected head
coordinate of `X • m` is multiplication by `AdjoinRoot.root`, and
`rationalCanonicalSelectedAmbientSplit_tail_X_smul` says the tail coordinate is
still `X`-multiplication.  The pointwise transported-operator lemmas
`rationalCanonicalSelectedAmbientSplit_conj_toLin_head` and
`rationalCanonicalSelectedAmbientSplit_conj_toLin_tail` connect this action to
the original matrix operator via `Module.AEval'.of`.

The selected split matrix has now been reduced away from the arbitrary ambient
index equivalence.  The theorem
`rationalCanonicalSelectedSplitLinearMapMatrix_eq_vectorFinBasis` rewrites
`rationalCanonicalSelectedSplitLinearMapMatrix selected` as the matrix of
`Matrix.toLin' A` in the Fin-indexed selected/tail basis, followed only by the
canonical `sumToLexEquiv` reindex.  This isolates the remaining matrix work from
the noncomputable `Fintype.equivOfCardEq` used to reindex the selected basis by
the original ambient index type.

These pointwise split-coordinate action lemmas have now been turned into
matrix statements for `rationalCanonicalSelectedSplitLinearMapMatrix`.
The coordinate lemmas
`rationalCanonicalSelectedVectorFinBasis_head_head`,
`rationalCanonicalSelectedVectorFinBasis_head_tail_zero`, and
`rationalCanonicalSelectedVectorFinBasis_tail_head_zero` prove that the head
block is `Algebra.leftMulMatrix` for root multiplication and that both
off-diagonal blocks are zero.  They feed
`rationalCanonicalSelectedHeadCompanionCertificate_concrete`,
`rationalCanonicalSelectedSplitBlockCertificate_concrete`, and finally
`rationalCanonicalSelectedAlgebraicBlockCertificate`.

The predicate data is no longer an arbitrary `Prop` payload.  Empty matrices
use the empty block index, single companion blocks use an explicit equivalence
to `PUnit × Fin p.natDegree`, and multi-block combination composes the
left/right block decompositions into a dependent block diagonal decomposition
over a sum of block labels.

## 7. Verification

```bash
lake build MatDecompFormal.Instances.RationalCanonical
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/RationalCanonical -S
lake env lean --stdin <<'EOF'
import MatDecompFormal.Instances.RationalCanonical
#check MatDecompFormal.Instances.exists_rational_canonical_matrix
#check MatDecompFormal.Instances.exists_rational_canonical_form
#check MatDecompFormal.Instances.exists_rational_canonical_matrix_module_bridge
#check MatDecompFormal.Instances.exists_rational_canonical_form_module_bridge
#check MatDecompFormal.Instances.isCompanionMatrix_companionMatrixFin
#check MatDecompFormal.Instances.singleCompanionBlockForm_companionMatrixFin
#check MatDecompFormal.Instances.isCompanionMatrix_adjoinRoot_leftMulMatrix_powerBasis
#check MatDecompFormal.Instances.singleCompanionBlockForm_adjoinRoot_leftMulMatrix_powerBasis
#check MatDecompFormal.Instances.singleCompanionBlockForm_reindex
#check MatDecompFormal.Instances.isRationalCanonicalMatrix_companionMatrixFin
#check MatDecompFormal.Instances.hasRationalCanonical_companionMatrixFin
#check MatDecompFormal.Instances.isCompanionMatrix_unit_X_sub_C
#check MatDecompFormal.Instances.singleCompanionBlockForm_unit_X_sub_C
#check MatDecompFormal.Instances.isRationalCanonicalMatrix_unit
#check MatDecompFormal.Instances.hasRationalCanonical_unit
#check MatDecompFormal.Instances.rationalCanonicalBlockDiagLex
#check MatDecompFormal.Instances.rationalCanonicalBlockDiagLex_reindex
#check MatDecompFormal.Instances.isRationalCanonicalMatrix_blockDiag_lex
#check MatDecompFormal.Instances.hasMatrixInverse_blockDiag_lex
#check MatDecompFormal.Instances.hasRationalCanonical_blockDiag_lex
#check MatDecompFormal.Instances.rationalCanonicalTailSlice_eq_toBlocks₂₂
#check MatDecompFormal.Instances.RationalCanonicalHeadTailBlockReady
#check MatDecompFormal.Instances.rationalCanonicalHeadTailBlockReady_of_unit_block_eq
#check MatDecompFormal.Instances.rationalCanonicalLiftReady_of_headTailBlockReady
#check MatDecompFormal.Instances.isRationalCanonicalMatrix_singleCompanion
#check MatDecompFormal.Instances.RationalCanonicalModuleStepData.headTailReady
#check MatDecompFormal.Instances.RationalCanonicalMatrixPolynomialModule
#check MatDecompFormal.Instances.RationalCanonicalPolynomialModuleData
#check MatDecompFormal.Instances.rationalCanonicalMatrixPolynomialModule_torsion
#check MatDecompFormal.Instances.rationalCanonicalPolynomialModuleData
#check MatDecompFormal.Instances.associated_pow
#check MatDecompFormal.Instances.quotient_span_singleton_pow_equiv_of_associated
#check MatDecompFormal.Instances.quotient_span_singleton_equiv_adjoinRoot_restrictScalars
#check MatDecompFormal.Instances.quotient_span_singleton_equiv_adjoinRoot_restrictScalars_X_smul
#check MatDecompFormal.Instances.adjoinRootLinearEquivOfEq
#check MatDecompFormal.Instances.adjoinRootLinearEquivOfEq_root_mul
#check MatDecompFormal.Instances.RationalCanonicalPolynomialModuleDecompositionData
#check MatDecompFormal.Instances.rationalCanonicalPolynomialModuleDecompositionData
#check MatDecompFormal.Instances.RationalCanonicalSelectedCyclicSummand
#check MatDecompFormal.Instances.RationalCanonicalSelectedCyclicSummand.quotientEquivCyclicFactorAdjoinRoot
#check MatDecompFormal.Instances.RationalCanonicalSelectedCyclicSummand.quotientEquivAdjoinRoot
#check MatDecompFormal.Instances.RationalCanonicalSelectedCyclicSummand.quotientEquivCyclicFactorAdjoinRoot_X_smul
#check MatDecompFormal.Instances.RationalCanonicalSelectedCyclicSummand.quotientEquivAdjoinRoot_X_smul
#check MatDecompFormal.Instances.RationalCanonicalSelectedCyclicSummandBridge
#check MatDecompFormal.Instances.RationalCanonicalEffectiveSummandIndex
#check MatDecompFormal.Instances.RationalCanonicalEffectiveSummandIndexBridge
#check MatDecompFormal.Instances.rationalCanonicalMatrixPolynomialModule_nontrivial_of_nonempty
#check MatDecompFormal.Instances.rationalCanonicalDecomposition_exists_positive_exponent
#check MatDecompFormal.Instances.rationalCanonicalEffectiveSummandIndexOfDecomposition
#check MatDecompFormal.Instances.rationalCanonicalEffectiveSummandIndexBridge
#check MatDecompFormal.Instances.rationalCanonicalSelectedCyclicSummandOfIndex
#check MatDecompFormal.Instances.rationalCanonicalSelectedCyclicSummandBridgeOfEffectiveIndexBridge
#check MatDecompFormal.Instances.RationalCanonicalCyclicBlockStepData
#check MatDecompFormal.Instances.rationalCanonicalSelectedAmbientSplit_head_X_smul
#check MatDecompFormal.Instances.rationalCanonicalSelectedAmbientSplit_tail_X_smul
#check MatDecompFormal.Instances.rationalCanonicalSelectedTailXLinearMap
#check MatDecompFormal.Instances.rationalCanonicalSelectedAmbientSplit_conj_toLin_head
#check MatDecompFormal.Instances.rationalCanonicalSelectedAmbientSplit_conj_toLin_tail
#check MatDecompFormal.Instances.rationalCanonicalSelectedSplitLinearMapMatrix_eq_vectorFinBasis
#check MatDecompFormal.Instances.RationalCanonicalSelectedBlockStepCertificate
#check MatDecompFormal.Instances.RationalCanonicalSelectedSplitBlockCertificate
#check MatDecompFormal.Instances.rationalCanonicalSelectedSplitBlockEquation_of_certificate
#check MatDecompFormal.Instances.RationalCanonicalSelectedHeadCompanionCertificate
#check MatDecompFormal.Instances.rationalCanonicalSelected_head_companion_of_certificate
#check MatDecompFormal.Instances.RationalCanonicalSelectedAlgebraicBlockCertificate
#check MatDecompFormal.Instances.rationalCanonicalSelectedBlockStepCertificateOfAlgebraicCertificate
#check MatDecompFormal.Instances.rationalCanonicalCyclicBlockStepDataOfSelectedCertificate
#check MatDecompFormal.Instances.RationalCanonicalSelectedCompanionBlock
#check MatDecompFormal.Instances.rationalCanonicalSelectedCompanionBlock
#check MatDecompFormal.Instances.RationalCanonicalPolynomialBlockStepData
#check MatDecompFormal.Instances.RationalCanonicalPolynomialModuleBridge
#check MatDecompFormal.Instances.rationalCanonicalModuleStructureBridgeOfPolynomialModuleBridge
#check MatDecompFormal.Instances.exists_rational_canonical_matrix_polynomial_module_bridge
#check MatDecompFormal.Instances.RationalCanonicalModuleStructureBridge
#check MatDecompFormal.Instances.RationalCanonicalBlockStepOracle
#check MatDecompFormal.Instances.RationalCanonicalPolynomialBlockBridge
#check MatDecompFormal.Instances.RationalCanonicalSelectedBlockStepCertificateBridge
#check MatDecompFormal.Instances.rationalCanonicalPolynomialBlockBridgeOfSelectedCertificateBridge
#check MatDecompFormal.Instances.RationalCanonicalSelectedAlgebraicBlockCertificateBridge
#check MatDecompFormal.Instances.rationalCanonicalSelectedAlgebraicBlockCertificateBridge
#check MatDecompFormal.Instances.rationalCanonicalSelectedBlockStepCertificateBridgeOfAlgebraicBridge
#check MatDecompFormal.Instances.rationalCanonicalPolynomialBlockBridge
#check MatDecompFormal.Instances.rationalCanonicalBlockStepOracleOfPolynomialBlockBridge
#check MatDecompFormal.Instances.rationalCanonicalBlockSliceData
#check MatDecompFormal.Instances.rationalCanonicalBlockReach
#check MatDecompFormal.Instances.rationalCanonical_block_framework_inst
#check MatDecompFormal.Instances.exists_rational_canonical_matrix_block_framework
#check MatDecompFormal.Instances.exists_rational_canonical_matrix_polynomial_block_bridge
#check MatDecompFormal.Instances.exists_rational_canonical_form_polynomial_block_bridge
EOF
```
