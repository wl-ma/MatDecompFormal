# Schur Upper Triangularization via the Descent Framework

This plan describes how to formalize Schur-type upper triangularization using
the project descent-template style, with scalar assumptions kept as weak as the
chosen theorem permits.

## 1. Target Theorems

Generic algebraic triangularization over an algebraically closed field:

```lean
theorem exists_schur_upper_triangular
    {K ι : Type*} [Field K] [IsAlgClosed K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    ∃ P : Matrix ι ι K, ∃ T : Matrix ι ι K,
      InvertibleMatrix P ∧
      T.IsUpperTriangular ∧
      A = P * T * P⁻¹
```

Unitary Schur form is stronger and should be a separate corollary over
`RCLike`, usually `ℂ`:

```lean
theorem exists_unitary_schur_upper_triangular
    {𝕜 ι : Type*} [RCLike 𝕜]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι 𝕜) :
    ∃ Q : Matrix ι ι 𝕜, ∃ T : Matrix ι ι 𝕜,
      IsUnitaryMatrix Q ∧
      T.IsUpperTriangular ∧
      A = Q * T * Qᴴ
```

The generic theorem needs eigenvalues, hence algebraic closedness or an explicit
eigenvector oracle. It should not require `ℂ` unless proving the unitary version.

## 2. Predicate

Use mathlib `Matrix.IsUpperTriangular` if it works well with arbitrary finite
linear orders. Otherwise define a local scalar-parametric predicate and bridge
it later.

```lean
def HasSchur (A : Matrix ι ι K) : Prop :=
  ∃ P T, InvertibleMatrix P ∧ T.IsUpperTriangular ∧ A = P * T * P⁻¹
```

For the unitary corollary:

```lean
def HasUnitarySchur (A : Matrix ι ι 𝕜) : Prop :=
  ∃ Q T, IsUnitaryMatrix Q ∧ T.IsUpperTriangular ∧ A = Q * T * Qᴴ
```

## 3. Descent Shape

Generic field route:

1. Choose an eigenvector using `[IsAlgClosed K]` or a `SchurEigenOracle`.
2. Extend the eigenvector to a basis, not necessarily orthonormal.
3. Build an invertible change-of-basis matrix `P₁`.
4. Show `B = P₁⁻¹ * A * P₁` has zero lower-left block.
5. Recurse on `B.toBlocks₂₂`.
6. Lift by block-diagonal invertible extension.
7. Transport back by similarity.

Unitary route:

1. Normalize the eigenvector.
2. Extend it to an orthonormal basis.
3. Use unitary similarity and the same lower-left-zero recursion.

## 4. Framework Mapping

Use the existing square-universe driver:

```lean
SquareStrategyData
mkSquareSubtypeInductionInstanceFromStrategy
SquareSubtypeInductionInstance.prove_for_matrix
```

The proof must not end with a direct induction theorem. A direct theorem may be
kept only as a local hook for `transport` or `lift`; the public theorem must be
obtained from the square driver.

### Transformation

Generic:

```lean
B = P⁻¹ * A * P
```

Unitary corollary:

```lean
B = Qᴴ * A * Q
```

### Reduction

Use the lower-right head-tail submatrix:

```lean
slice B = B.toBlocks₂₂
```

### Readiness

After head-tail reindexing:

```lean
B'.toBlocks₂₁ = 0
```

The top-right block is arbitrary.

### Measure

Use `Fintype.card ι`.

## 5. Strict Descent-Template Contract

This is the implementation contract for Schur. Every item below must appear as
a concrete definition, theorem, or field in the final implementation.

### 5.1 Universe

Use the existing square universe:

```lean
SquareUniverse K
```

The theorem is square-only, so the rectangular driver is not appropriate.

### 5.2 Measure

Use the standard square-subtype measure already provided by the framework:

```lean
squareSubtypeμ x = Fintype.card x.ι
squareSubtypeμBase = 0
```

The recursive index is the head-tail complement:

```lean
abbrev SchurTailIdx
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { i : ι // i ≠ headElem (α := ι) }
```

Required progress lemma:

```lean
theorem schur_tail_card_lt
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    Fintype.card (SchurTailIdx ι) < Fintype.card ι
```

This is the strict-decrease proof used in `μ_slice`.

### 5.3 Predicate `P`

The generic predicate should be a proposition on `SquareUniverse K`:

```lean
def HasSchur
    {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ P : Matrix ι ι K, ∃ T : Matrix ι ι K,
    InvertibleMatrix P ∧ T.IsUpperTriangular ∧ A = P * T * P⁻¹

def Schur_P (x : SquareUniverse K) : Prop :=
  HasSchur x.A
```

If `Matrix.IsUpperTriangular` is awkward under arbitrary finite linear orders,
introduce a local recursive predicate first:

```lean
def IsSchurUpperTriangular (T : Matrix ι ι K) : Prop := ...
```

and prove a bridge to mathlib's predicate later. The recursive predicate should
say that, after `headTailEquiv`, the lower-left block is zero and the tail block
is recursively upper triangular.

### 5.4 Base

The universe-level base theorem must have the framework shape:

```lean
theorem schur_base_univ
    (x : SquareUniverse K) :
    ((∀ x_sub : PosSquareUniverse K, (x_sub : SquareUniverse K) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      Schur_P x
```

The proof obtains `Fintype.card x.ι = 0` from
`squareSubtypeBaseDimEqZero`, then uses:

```lean
P = 1
T = x.A
```

For an empty index type, upper triangularity is vacuous and `A = 1 * A * 1⁻¹`.

### 5.5 Transform

The strategy transform is invertible similarity:

```lean
structure SchurSimilarityToken
    (K ι : Type*) [Field K] [Fintype ι] [DecidableEq ι] where
  P : Matrix ι ι K
  invP : InvertibleMatrix P

def schurSimilarityTransform :
    Transformation (Matrix ι ι K)
```

The transformed matrix is:

```lean
transform A token = token.P⁻¹ * A * token.P
```

The relation `r B A` records the existence of such a token with
`B = token.P⁻¹ * A * token.P`.

### 5.6 Readiness

Readiness isolates exactly the condition needed to recurse on the lower-right
block:

```lean
def SchurDescentReady
    (A : Matrix ι ι K) : Prop :=
  let A' := Matrix.reindex (headTailEquiv (α := ι)) (headTailEquiv (α := ι)) A
  A'.toBlocks₂₁ = 0
```

Equivalently, the head vector spans an invariant one-dimensional subspace:

```lean
∀ i : SchurTailIdx ι,
  A (i : ι) (headElem (α := ι)) = 0
```

The implementation may use whichever form is easier, but it must prove a bridge
to the block-lift lemma.

### 5.7 Slice

Use the lower-right head-tail block:

```lean
def schurHeadTailReduction :
    ReductionMethod ι ι (SchurTailIdx ι) (SchurTailIdx ι) K
```

The slice is:

```lean
Matrix.submatrix A
  (fun i : SchurTailIdx ι => (i : ι))
  (fun j : SchurTailIdx ι => (j : ι))
```

or equivalently `A'.toBlocks₂₂` after reindexing by `headTailEquiv`.

### 5.8 Reach

Reach is constructed by the strategy from a one-step oracle:

```lean
structure SchurStepOracle
    (K ι : Type*) [Field K] [IsAlgClosed K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  P : Matrix ι ι K → Matrix ι ι K
  invertible_P : ∀ A, InvertibleMatrix (P A)
  ready : ∀ A, SchurDescentReady ((P A)⁻¹ * A * (P A))
```

The first framework theorem should remain conditional on this oracle:

```lean
theorem exists_schur_framework_oracle
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        SchurStepOracle K ι)
    ...
```

The unconditional algebraically closed theorem is obtained only after
constructing `SchurStepOracle` from eigenvectors.

### 5.9 Transport

Transport moves a Schur witness backward across invertible similarity:

If:

```lean
B = P⁻¹ * A * P
B = S * T * S⁻¹
```

then:

```lean
A = (P * S) * T * (P * S)⁻¹
```

Required theorem:

```lean
theorem schur_transport_similarity
    (h : B = P⁻¹ * A * P)
    (hP : InvertibleMatrix P)
    (hB : HasSchur B) :
    HasSchur A
```

This theorem supplies the `transport` field of `SquareStrategyProofData`.

### 5.10 Lift

Lift converts a tail Schur witness into a full Schur witness for a ready
head-tail matrix.

For a ready block matrix:

```lean
B' = fromBlocks B₁₁ B₁₂ 0 B₂₂
```

and a tail witness:

```lean
B₂₂ = S₂₂ * T₂₂ * S₂₂⁻¹
```

construct:

```lean
S = blockDiag 1 S₂₂
T = fromBlocks B₁₁ (B₁₂ * S₂₂) 0 T₂₂
```

Then prove:

```lean
B' = S * T * S⁻¹
T.IsUpperTriangular
```

Required theorem:

```lean
theorem schur_lift_from_tail
    (A : Matrix ι ι K)
    (hready : SchurDescentReady A)
    (htail : HasSchur (schurTailSlice A hready)) :
    HasSchur A
```

This theorem supplies the `lift` field of `SquareStrategyProofData`.

### 5.11 Driver

The strategy core must be a `SquareStrategyCore`:

```lean
noncomputable def schur_strategy_core
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        SchurStepOracle K ι) :
    SquareStrategyCore K
```

Fields:

```lean
SliceIdx := SchurTailIdx
strategy.transform := schurSimilarityTransform oracle
strategy.reduction := schurHeadTailReduction
strategy.goal_is_sliceable := ...
strategy.μ := fun _ => Fintype.card ι
strategy.μ_slice := fun _ => Fintype.card (SchurTailIdx ι)
```

Then package proof hooks:

```lean
noncomputable def schur_strategy_data
    (oracle : ...)
    (hooks : SchurDescentHooks oracle) :
    SquareStrategyData K Schur_P
```

and instantiate:

```lean
noncomputable def schur_framework_inst
    (oracle : ...)
    (hooks : SchurDescentHooks oracle) :
    SquareSubtypeInductionInstance K :=
  mkSquareSubtypeInductionInstanceFromStrategy
    Schur_P
    schur_base_univ
    (schur_strategy_data oracle hooks)
```

### 5.12 Final Theorems

The conditional theorem must be routed through:

```lean
SquareSubtypeInductionInstance.prove_for_matrix
```

Expected theorem chain:

```lean
theorem exists_schur_framework
    (oracle : ...)
    (hooks : SchurDescentHooks oracle)
    (A : Matrix ι ι K) :
    HasSchur A

theorem exists_schur_framework_oracle
    (oracle : ...)
    (A : Matrix ι ι K) :
    HasSchur A

theorem exists_schur
    {K ι : Type u} [Field K] [IsAlgClosed K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasSchur A
```

`exists_schur` may call `exists_schur_framework_oracle`, but it must not use a
direct standalone induction proof.

## 6. Mathematical Oracle Discharge

The unconditional theorem over `[IsAlgClosed K]` requires the concrete
construction of `SchurStepOracle`.

### 6.1 Eigenvector

For nonempty finite `ι`, prove or import:

```lean
theorem exists_eigenvector_of_isAlgClosed
    (A : Matrix ι ι K) :
    ∃ λ : K, ∃ v : ι → K, v ≠ 0 ∧ A *ᵥ v = λ • v
```

This is the only point where algebraic closedness is used in the generic Schur
proof.

### 6.2 Basis Completion

Construct an invertible basis matrix `P` whose first column is `v`.

Required data:

```lean
structure SchurHeadEigenData
    (A : Matrix ι ι K) where
  lambda : K
  basis : Basis ι K (ι → K)
  head_eq_eigenvector : basis (headElem (α := ι)) = v
  eigen : A *ᵥ v = lambda • v
```

The resulting change-of-basis matrix must satisfy:

```lean
((P A)⁻¹ * A * (P A)) i (headElem (α := ι)) = 0
```

for every tail `i`, giving `SchurDescentReady`.

### 6.3 Optional Unitary Schur

The unitary theorem is not part of the first generic proof. It should be layered
after `exists_schur`:

```lean
theorem exists_unitary_schur_upper_triangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasUnitarySchur A
```

It uses orthonormal basis completion and unitary similarity, but the same
Universe/μ/P/base/readiness/slice/lift/driver shape should be reused.

## 7. Required Lemmas

- `InvertibleMatrix` identity/product/block-diagonal extension.
- Generic similarity transport for `HasSchur`.
- Optional unitary transport for `HasUnitarySchur`.
- Base case for empty/subsingleton index types.
- Reindex invariance of upper triangularity.
- Block lift: `fromBlocks A₁₁ A₁₂ 0 T₂₂` is upper triangular if `T₂₂` is.
- Eigenvector existence over `[IsAlgClosed K]`.
- Basis extension from one nonzero vector over a field.
- Optional orthonormal-basis extension over `RCLike`.

Initial generic oracle:

```lean
structure SchurStepOracle
    (K ι : Type*) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  P : Matrix ι ι K → Matrix ι ι K
  invertible_P : ∀ A, InvertibleMatrix (P A)
  ready : ∀ A, SchurDescentReady ((P A)⁻¹ * A * (P A))
```

## 8. File Layout

```text
MatDecompFormal/Instances/Schur/PLAN.md
MatDecompFormal/Instances/Schur.lean
MatDecompFormal/Instances/Schur/Details.lean
MatDecompFormal/Instances/Schur/Strategy.lean
MatDecompFormal/Instances/Schur/Direct.lean
MatDecompFormal/Instances/Schur/Existence.lean
```

Roles:

- `Details.lean`: `HasSchur`, upper-triangular predicate helpers, base cases,
  block-diagonal matrix helpers, and tail-index facts.
- `Strategy.lean`: `SchurTailIdx`, `SchurDescentReady`,
  `SchurStepOracle`, similarity transform, reduction, and
  `schur_strategy_core`.
- `Direct.lean`: `schur_transport_similarity`,
  `schur_lift_from_ready`, `schur_lift_hook`, and `SchurDescentHooks`.
- `Existence.lean`: framework instance and theorem chain through
  `SquareSubtypeInductionInstance.prove_for_matrix`.
- `Schur.lean`: public imports.

## 9. Implementation Order

1. Define generic `HasSchur`.
2. Define optional `HasUnitarySchur` separately.
3. Define `SchurTailIdx`, tail cardinality decrease, and tail slice.
4. Prove base cases and block upper-triangular lift.
5. Prove generic similarity transport.
6. Build the square descent strategy with invertible similarity.
7. Add conditional framework theorem through the square driver.
8. Discharge the step oracle using algebraically closed field eigenvectors.
9. Expose `exists_schur`.
10. Add `RCLike`/unitary corollary only after the generic theorem is stable.

## 10. Relation to Hessenberg

Hessenberg reduction is useful algorithmic preprocessing, but Schur existence can
be proved directly by eigenvector descent. Share transport and block lemmas, but
keep algebraic assumptions explicit and layered.

## 11. Verification

```bash
lake build MatDecompFormal.Instances.Schur
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Schur -S
```

Before marking implementation complete, also check:

```bash
printf 'import MatDecompFormal.Instances.Schur\n#check MatDecompFormal.Instances.exists_schur\n' | lake env lean --stdin
rg -n "exists_schur.*:= by|prove_for_matrix|exists_schur_framework" MatDecompFormal/Instances/Schur -S
```

The second search should show the final theorem routed through the framework
chain, not a direct-only proof.

## 12. Current Status

Completed implementation-facing milestones:

- File skeleton is present:
  `Schur.lean`, `Schur/Details.lean`, `Schur/Strategy.lean`,
  `Schur/Direct.lean`, and `Schur/Existence.lean`.
- Matrix-level target predicate is defined:
  `InvertibleMatrix`, `HasSchur`, `Schur_P`, and zero-dimensional/subsingleton
  base cases.
- Strategy-side descent skeleton is implemented through the square driver:
  `SchurTailIdx`, `SchurDescentReady`, `SchurStepOracle`,
  `schurSimilarityTransform`, `schurHeadTailReduction`, and
  `schur_strategy_core`.
- Framework theorem chain exists and is routed through
  `SquareSubtypeInductionInstance.prove_for_matrix`:
  `exists_schur_framework` and `exists_schur_framework_oracle`.
- Similarity transport is concrete:
  `schur_transport_similarity` and `schur_transport_hook`.
- Block lift is concrete:
  `schur_lift_from_ready`, `schur_lift_hook`, and `schur_descent_hooks`.
- `exists_schur_framework_oracle` now depends only on the one-step
  `SchurStepOracle`; the lift hook is supplied internally by
  `schur_descent_hooks`.
- The algebraically closed field oracle is discharged in `Schur/Spectral.lean`:
  `schurEigenvectorData`, `schurBasisWithHeadVector`,
  `schurHeadColumnData`, and `schur_step_oracle_of_isAlgClosed`.
- Public `exists_schur` is exposed in `Schur/Existence.lean` and calls
  `exists_schur_framework_oracle (schur_step_oracle_of_isAlgClosed K)`, so the
  proof path remains routed through the square descent driver.
- `Schur.lean` publicly imports `Details`, `Strategy`, `Direct`, `Existence`,
  and `Spectral`.

Remaining implementation work:

- None for the generic algebraically closed field Schur theorem currently
  exposed as `exists_schur`.

Latest verification:

```bash
lake build MatDecompFormal.Instances.Schur
lake build MatDecompFormal.Instances
printf 'import MatDecompFormal.Instances.Schur\n#check MatDecompFormal.Instances.exists_schur\n#check MatDecompFormal.Instances.schur_step_oracle_of_isAlgClosed\n#check MatDecompFormal.Instances.schurHeadColumnData\n' | lake env lean --stdin
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Schur --glob '!PLAN.md' -S
rg -n "exists_schur|prove_for_matrix|exists_schur_framework|schur_step_oracle_of_isAlgClosed|schurHeadColumnData" MatDecompFormal/Instances/Schur MatDecompFormal/Instances/Schur.lean -S
```

The placeholder scan has no Lean-file hits.
