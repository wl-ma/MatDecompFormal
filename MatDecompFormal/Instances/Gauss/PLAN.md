# Gauss Rank Normal Form via the Descent Framework

This plan describes Gauss normal form, also called rank normal form, using the
project descent-template style.

The theorem is algebraic and should not depend on `ℝ` or `ℂ`. The natural main
setting is matrices over a division ring or field, because Gaussian elimination
requires nonzero pivots to be invertible.

## 1. Target Theorems

Compatibility theorem, conditional on a one-step Gauss elimination oracle:

```lean
theorem exists_gauss_rank_normal_form_oracle
    {R m n : Type*} [Semiring R]
    (oracle :
      ∀ {p q : Type*} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        GaussRankStepOracle R p q)
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasGaussRankNormalForm A
```

Primary theorem over a division ring, obtained by discharging
`GaussRankStepOracle` with concrete elementary row/column operations:

```lean
theorem exists_gauss_rank_normal_form
    {R m n : Type*} [DivisionRing R]
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n R) :
    HasGaussRankNormalForm A
```

For commutative fields, add rank-identification corollaries:

```lean
theorem gauss_rank_normal_form_rank_eq
    {K m n : Type*} [Field K] ...
    (hG : IsGaussRankNormalForm G) :
    Matrix.rank G = numberOfRankPivots G
```

## 2. Normal-Form Predicate

Rank normal form should be a rectangular matrix with an identity block in the
upper-left corner and zeros elsewhere:

```lean
def IsGaussRankNormalForm
    {R m n : Type*} [Zero R] [One R]
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (G : Matrix m n R) : Prop :=
  ∃ r : Type*, ∃ _ : Fintype r,
    GaussRankBlockData G r
```

A first implementation can use a data-oriented block witness:

```lean
structure GaussRankBlockData (G : Matrix m n R) where
  r : Type*
  fintype_r : Fintype r
  row : r → m
  col : r → n
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  entry_one : ∀ k, G (row k) (col k) = 1
  entry_zero : ∀ i j, (∀ k, row k ≠ i ∨ col k ≠ j) → G i j = 0
```

Later, once rank-index APIs are stable, add a prettier `Fin rank` upper-left
identity-block predicate.

## 3. Descent Template Instantiation

### Universe

Rectangular matrices over `R`:

```lean
RectUniverse R
```

### Measure

Use the rectangular size measure:

```lean
μ A = min (Fintype.card m) (Fintype.card n)
```

The slice removes one row and one column after a nonzero pivot is isolated.

### Predicate

`P A := HasGaussRankNormalForm A`, where:

```lean
def HasGaussRankNormalForm (A : Matrix m n R) : Prop :=
  ∃ P Q G,
    InvertibleMatrix P ∧
    InvertibleMatrix Q ∧
    IsGaussRankNormalForm G ∧
    G = P * A * Q
```

### Base

If either row or column type is empty, the matrix is zero and already in rank
normal form with rank `0`.

If the active matrix is zero, it is also in rank normal form with rank `0`.

### Transform

Allowed transformations are two-sided invertible row and column operations:

```lean
B = P * A * Q
```

where `P` and `Q` are explicitly invertible matrices. The current API uses
`GaussInvertibleMatrix P := ∃ Pinv, Pinv * P = 1 ∧ P * Pinv = 1`; the intended
oracle implementation will provide these matrices as products of swaps,
scalings, and shear/addition elementary matrices.

### Readiness

A matrix is Gauss-ready if either:

1. it is the zero matrix; or
2. the head/head entry is `1`, all other entries in the head row and head column
   are zero, and the lower-right block is the remaining subproblem.

Sketch:

```lean
def GaussRankDescentReady (A : Matrix m n R) : Prop :=
  A = 0 ∨
  let A' := Matrix.reindex rowHeadTail colHeadTail A
  A'.toBlocks₁₁ = 1 ∧ A'.toBlocks₁₂ = 0 ∧ A'.toBlocks₂₁ = 0
```

### Slice

For the pivot-ready branch, slice the lower-right block:

```lean
slice A = A'.toBlocks₂₂
```

For the zero branch, no recursive slice is needed; it closes immediately in the
lift/base branch.

### Reach

If the active matrix is nonzero, choose a nonzero entry, move it to the head/head
position by row and column swaps, scale it to `1`, then use elementary row and
column operations to clear the rest of the head column and head row.

This is currently isolated as an oracle:

```lean
structure GaussRankStepOracle
    (R m n : Type*) [Semiring R]
    [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] where
  P : Matrix m n R → Matrix m m R
  Q : Matrix m n R → Matrix n n R
  invertible_P : ∀ A, GaussInvertibleMatrix (P A)
  invertible_Q : ∀ A, GaussInvertibleMatrix (Q A)
  ready : ∀ A, GaussRankDescentReady (P A * A * Q A)
```

The oracle is discharged by `gaussRankStepOracle` over `[DivisionRing R]`.

### Transport

If `B = P * A * Q`, with `P` and `Q` invertible, and `B` has rank normal form,
then `A` has rank normal form by multiplying the outer invertible factors.

### Lift

If the ready matrix has isolated head identity pivot and the tail has rank normal
form, prepend one rank pivot to the tail normal-form data and block-diagonally
extend the tail transformations.

If the ready matrix is zero, close with the zero rank normal form.

### Driver

Use the rectangular decomposition driver:

```lean
RectStrategyData
mkRectSubtypeInductionInstanceFromStrategy
RectSubtypeInductionInstance.prove_for_matrix
```

If the zero branch does not fit the existing reduction API cleanly, define a
small Gauss-specific proof-data wrapper but keep the same driver fields.

## 4. Algebraic Assumptions

- Shape predicates can be defined over `[Zero R] [One R]`.
- Matrix multiplication and transformations need `[Semiring R]`.
- Pivot normalization and elimination need `[DivisionRing R]`.
- Rank-number corollaries may use `[Field K]` if mathlib rank APIs require
  commutativity.

Do not specialize the main theorem to `ℝ` or `ℂ`.

## 5. Relation to Other Instances

- PLU gives row-pivoted triangular decomposition for square matrices.
- LU is no-pivot triangular decomposition and requires pivot hypotheses.
- Gauss/rank normal form uses both row and column operations and works for
  rectangular matrices over division rings.
- Smith normal form generalizes rank normal form from fields to PID-like rings;
  over a field, Smith normal form collapses to rank normal form with diagonal
  entries `1` followed by `0`.

Dependency direction can be either:

```text
Gauss rank normal form -> field case of Smith normal form
```

or:

```text
Smith normal form over a field -> Gauss rank normal form
```

Prefer the direct Gauss descent first because it is simpler than the full PID
Smith step.

## 6. File Layout

```text
MatDecompFormal/Instances/Gauss/PLAN.md
MatDecompFormal/Instances/Gauss.lean
MatDecompFormal/Instances/Gauss/Details.lean
MatDecompFormal/Instances/Gauss/Strategy.lean
MatDecompFormal/Instances/Gauss/Direct.lean
MatDecompFormal/Instances/Gauss/Elementary.lean
MatDecompFormal/Instances/Gauss/Existence.lean
```

## 7. Implementation Order

1. Define `IsGaussRankNormalForm` and `HasGaussRankNormalForm`.
2. Prove zero/empty base cases.
3. Define two-sided invertible transformation data.
4. Define `GaussRankDescentReady`.
5. Build the rectangular strategy core with `GaussRankStepOracle`. Done.
6. Prove two-sided invertible transport. Done.
7. Prove block lift for one isolated pivot plus tail rank normal form. Done.
8. Discharge the step oracle using elementary row/column operations over a
   division ring. Done:
   - Done: in head-tail coordinates, when the head/head entry is nonzero,
     `gaussPlainHeadLeft` and `gaussPlainHeadRight` are explicit invertible
     factors whose two-sided action normalizes the head pivot to `1` and clears
     the rest of the head column and head row.
   - Done: for an arbitrary nonzero matrix, `gaussPivotRow`/`gaussPivotCol`
     choose a nonzero entry, and `gaussSwapToHeadLeft`/`gaussSwapToHeadRight`
     move it to the head/head position with explicit invertible swap factors.
   - Done: the swap factors are composed with the head-pivot factors after
     head-tail reindexing; `gaussConcreteStepP` and `gaussConcreteStepQ` are
     explicitly invertible and their two-sided action satisfies
     `GaussRankDescentReady`.
   - Done: `gaussRankStepOracle` packages the concrete step as a
     `GaussRankStepOracle` over `[DivisionRing R]`.
9. Add field-specific rank corollaries. Remaining.

## Descent Template Contract

This plan is required to use the project descent template. The implementation
must explicitly instantiate these components rather than only giving a direct
standalone proof:

1. `Universe`: the object being recursively decomposed.
2. `μ`: a natural-number or well-founded measure.
3. `P`: the target predicate on the universe.
4. `base`: proof for objects at the base measure.
5. `transform`: an allowed invertible row/column operation step.
6. `readiness`: the predicate saying the transformed object can be sliced or
   closed as zero.
7. `slice`: the smaller recursive subproblem.
8. `reach`: proof that every non-base object can reach a ready form.
9. `transport`: proof that `P` moves backward across `transform`.
10. `lift`: proof that `P (slice x)` implies `P x` for ready objects.
11. `driver`: assembly through the rectangular decomposition driver.
12. `final theorem`: obtained from the driver, not from a direct-only proof.

## 8. Verification

```bash
lake build MatDecompFormal.Instances.Gauss
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Gauss -S
```
