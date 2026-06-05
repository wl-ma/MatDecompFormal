# Bidiagonalization via the Descent Framework

This plan describes a strict descent-template implementation of matrix
bidiagonalization.  The intended theorem is the two-sided orthogonal/unitary
reduction used before SVD: every rectangular matrix is unitarily equivalent to
an upper bidiagonal matrix.

The public theorem must be assembled through the project descent framework, not
by a standalone induction proof.

## 1. Target Theorems

Real orthogonal bidiagonalization:

```lean
theorem exists_orthogonal_bidiagonalization
    {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℝ) :
    ∃ U : Matrix m m ℝ, ∃ V : Matrix n n ℝ, ∃ B : Matrix m n ℝ,
      IsOrthogonalMatrix U ∧
      IsOrthogonalMatrix V ∧
      IsUpperBidiagonal B ∧
      A = U * B * Vᵀ
```

Unitary version:

```lean
theorem exists_unitary_bidiagonalization
    {𝕜 m n : Type*} [RCLike 𝕜]
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) :
    ∃ U : Matrix m m 𝕜, ∃ V : Matrix n n 𝕜, ∃ B : Matrix m n 𝕜,
      IsUnitaryMatrix U ∧
      IsUnitaryMatrix V ∧
      IsUpperBidiagonal B ∧
      A = U * B * Vᴴ
```

The unitary theorem should be the main theorem if the conjugate-transpose API is
cleaner.  The real theorem can be a specialization.

## 2. Predicate Layer

Define upper bidiagonal using finite order ranks.  The only allowed nonzero
entries are on the main diagonal and first superdiagonal.

```lean
def IsUpperBidiagonal
    {m n R : Type*}
    [Fintype m] [LinearOrder m]
    [Fintype n] [LinearOrder n] [Zero R]
    (B : Matrix m n R) : Prop :=
  ∀ i j,
    finiteOrderRank n j < finiteOrderRank m i ∨
      finiteOrderRank m i + 1 < finiteOrderRank n j →
    B i j = 0
```

Target predicate:

```lean
def HasUnitaryBidiagonalization
    {𝕜 m n : Type*} [RCLike 𝕜]
    [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) : Prop :=
  ∃ U : Matrix m m 𝕜, ∃ V : Matrix n n 𝕜, ∃ B : Matrix m n 𝕜,
    IsUnitaryMatrix U ∧
    IsUnitaryMatrix V ∧
    IsUpperBidiagonal B ∧
    A = U * B * Vᴴ
```

The ordinary algebraic version, if needed later, should be a separate predicate
using invertible left/right factors.  This plan focuses on the unitary theorem.

## 3. Strict Descent-Template Contract

Every item in this section must appear as a concrete Lean definition, theorem,
or strategy field in the final implementation.

### 3.1 Universe

Use the rectangular universe, not `SquareUniverse`.

```lean
RectUniverse 𝕜
```

The universe stores row and column index types:

```lean
x.row
x.col
x.A : Matrix x.row x.col 𝕜
```

Framework predicate:

```lean
def Bidiagonalization_P (x : RectUniverse 𝕜) : Prop :=
  HasUnitaryBidiagonalization x.A
```

Positive/subtype universes should be chosen so that the recursive step only runs
when both row and column dimensions are positive.  If either dimension is zero,
the matrix is already bidiagonal.

### 3.2 Measure

Use the rectangular size measure that strictly decreases after removing one row
head and one column head.

Preferred measure:

```lean
μ x = Nat.min (Fintype.card x.row) (Fintype.card x.col)
μ_base = 0
```

The recursive slice removes both heads:

```lean
abbrev BidiagonalRowTail
    (m : Type*) [Fintype m] [LinearOrder m] [Nonempty m] :=
  { i : m // i ≠ headElem (α := m) }

abbrev BidiagonalColTail
    (n : Type*) [Fintype n] [LinearOrder n] [Nonempty n] :=
  { j : n // j ≠ headElem (α := n) }
```

Required progress lemma:

```lean
theorem bidiagonal_tail_min_card_lt
    {m n : Type*}
    [Fintype m] [LinearOrder m] [Nonempty m]
    [Fintype n] [LinearOrder n] [Nonempty n]
    (hm : 0 < Fintype.card m) (hn : 0 < Fintype.card n) :
    Nat.min
      (Fintype.card (BidiagonalRowTail m))
      (Fintype.card (BidiagonalColTail n)) <
    Nat.min (Fintype.card m) (Fintype.card n)
```

If the existing framework only supports a sum measure for rectangular problems,
use:

```lean
μ x = Fintype.card x.row + Fintype.card x.col
```

but the step must still remove both heads, so the sum decreases by two in the
non-base case.

### 3.3 Base

Base theorem:

```lean
theorem bidiagonalization_base_univ
    (x : RectUniverse 𝕜) :
    base-condition x →
      Bidiagonalization_P x
```

Base cases:

1. zero rows;
2. zero columns;
3. one row;
4. one column.

For one row or one column, every matrix is upper bidiagonal under the rank
predicate.  Use `U = 1`, `V = 1`, `B = A`.

### 3.4 Transformation

The transformation is two-sided unitary equivalence:

```lean
B = Uᴴ * A * V
```

Token:

```lean
structure BidiagonalizationToken (𝕜 m n : Type*) where
  U : Matrix m m 𝕜
  V : Matrix n n 𝕜
  unitary_U : IsUnitaryMatrix U
  unitary_V : IsUnitaryMatrix V
```

Transform:

```lean
transform A token = token.Uᴴ * A * token.V
```

Transport hook:

If `B = Uᴴ * A * V` and `B = S * C * Tᴴ`, then

```lean
A = (U * S) * C * (V * T)ᴴ
```

Required theorem:

```lean
theorem bidiagonalization_transport_equivalence
    (hU : IsUnitaryMatrix U)
    (hV : IsUnitaryMatrix V)
    (hB : B = Uᴴ * A * V)
    (hBi : HasUnitaryBidiagonalization B) :
    HasUnitaryBidiagonalization A
```

Use unitary closure under multiplication and conjugate-transpose reversal.

### 3.5 Readiness

After one two-sided unitary step, the transformed matrix must have the first row
and first column in upper-bidiagonal boundary form.

Head-tail block shape:

```lean
B =
  fromBlocks
    B₁₁  B₁₂
    B₂₁  B₂₂
```

where `B₁₁ : Matrix Unit Unit 𝕜`,
`B₁₂ : Matrix Unit ColTail 𝕜`,
`B₂₁ : Matrix RowTail Unit 𝕜`.

Readiness:

```lean
def BidiagonalizationReady (B : Matrix m n 𝕜) : Prop :=
  (∀ i : RowTail, B₂₁ i () = 0) ∧
  (∀ j : ColTail, j ≠ headElem → B₁₂ () j = 0)
```

Meaning:

1. first column has zeros below the diagonal;
2. first row has zeros beyond the first superdiagonal.

The remaining lower-right block `B₂₂` is the recursive slice.

### 3.6 Slice

Recursive slice:

```lean
slice B = B₂₂
```

Index types:

```lean
Matrix (BidiagonalRowTail m) (BidiagonalColTail n) 𝕜
```

The slice removes one row and one column.  This is why the rectangular driver is
required.

### 3.7 Lift

Lift hook:

```lean
theorem bidiagonalization_lift
    (hReady : BidiagonalizationReady B)
    (hTail : HasUnitaryBidiagonalization (bidiagonalTailSlice B)) :
    HasUnitaryBidiagonalization B
```

Given tail witness:

```lean
B₂₂ = S * C * Tᴴ
```

lift both sides block-diagonally:

```lean
Sblk = fromBlocks 1 0 0 S
Tblk = fromBlocks 1 0 0 T
```

Construct the parent bidiagonal matrix:

```lean
Bparent = Sblkᴴ * B * Tblk
```

or assemble it by blocks:

```lean
fromBlocks B₁₁ readyFirstRow readyFirstColumn C
```

Prove:

1. `Sblk` and `Tblk` are unitary.
2. `IsUpperBidiagonal Bparent`.
3. `B = Sblk * Bparent * Tblkᴴ`.

The bidiagonal zero proof uses:

1. `hReady.1` for the first column below the diagonal.
2. `hReady.2` for the first row beyond the first superdiagonal.
3. recursive `IsUpperBidiagonal C` for the tail-tail block.

## 4. One-Step Oracle

The strict template should first be implemented with an oracle, then discharged
with Householder or Givens transformations.

```lean
structure BidiagonalizationStepOracle (𝕜 : Type*) where
  U :
    ∀ {m n} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
      [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
      Matrix m n 𝕜 → Matrix m m 𝕜
  V :
    ∀ {m n} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
      [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
      Matrix m n 𝕜 → Matrix n n 𝕜
  unitary_U :
    ∀ A, IsUnitaryMatrix (U A)
  unitary_V :
    ∀ A, IsUnitaryMatrix (V A)
  ready :
    ∀ A, BidiagonalizationReady ((U A)ᴴ * A * V A)
```

Concrete step:

1. use a left Householder/Givens transformation to zero the first column below
   the first row;
2. use a right Householder/Givens transformation on the tail columns to zero the
   first row beyond the first superdiagonal;
3. package the product as `Ustep`, `Vstep`.

The right transformation must leave the first column readiness intact; this is
automatic because it acts on columns, but the block proof must state it.

## 5. Householder Route

Left reflector:

```lean
Ustepᴴ * A
```

maps the first column to a scalar multiple of `e₀`.

Right reflector:

```lean
(Ustepᴴ * A) * Vstep
```

acts only on the column tail so the first row tail is mapped to a scalar
multiple of its first coordinate.

Required lemmas:

```lean
theorem householder_unitary :
    IsUnitaryMatrix (householder x)

theorem householder_maps_column_to_axis :
    ...

theorem blockDiag_one_householder_unitary :
    IsUnitaryMatrix (fromBlocks 1 0 0 (householder x))
```

Degenerate vectors use identity reflectors.

## 6. Givens Fallback

Use finite products of Givens rotations:

1. left rotations zero entries in the first column from bottom to top;
2. right rotations zero entries in the first row tail from right to left.

Required lemmas:

```lean
theorem givens_unitary :
    IsUnitaryMatrix (givens i j a b)

theorem left_givens_preserves_prior_column_zeroes :
    ...

theorem right_givens_preserves_first_column_ready :
    ...

theorem givens_products_ready :
    BidiagonalizationReady (Uᴴ * A * V)
```

This route has more finite-order bookkeeping but avoids global norm/vector
normalization details.

## 7. Framework Assembly

Files should be introduced in this order:

1. `Details.lean`: `IsUpperBidiagonal`, target predicate, base cases, two-sided
   unitary transport lemmas.
2. `Strategy.lean`: rectangular tail indices, transform token, strategy core,
   measure proof, readiness, slice.
3. `Direct.lean`: transport and lift hooks.
4. `Existence.lean`: strict framework instantiation and oracle-routed public
   theorem.
5. `Householder.lean` or `Givens.lean`: concrete oracle.
6. `Bidiagonalization.lean`: aggregate imports.

The final public theorem must be routed as:

```lean
noncomputable def bidiagonalization_strategy_data :
    RectStrategyData 𝕜 Bidiagonalization_P := ...

noncomputable def bidiagonalization_framework_inst :
    RectSubtypeInductionInstance 𝕜 := ...

theorem exists_unitary_bidiagonalization ... :=
  RectSubtypeInductionInstance.prove_for_matrix
    (inst := bidiagonalization_framework_inst) A
```

If the current project does not yet expose rectangular strategy names with
exactly these identifiers, first add the corresponding rectangular analogue of
the square driver, then instantiate it here.  Do not replace this with direct
induction.

Current implemented public framework theorem:

```lean
theorem exists_unitary_bidiagonalization_framework
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationStepOracle 𝕜 m n)
    (hooks : BidiagonalizationDescentHooks oracle)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) :
    HasUnitaryBidiagonalization A
```

and the hook-built oracle interface:

```lean
theorem exists_unitary_bidiagonalization_oracle
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        BidiagonalizationStepOracle 𝕜 m n)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n 𝕜) :
    HasUnitaryBidiagonalization A
```

Both are obtained via
`RectSubtypeInductionInstance.prove_for_matrix`.

The current unconditional complex theorem is:

```lean
theorem exists_unitary_bidiagonalization
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasUnitaryBidiagonalization A
```

It is still routed through the bidiagonalization framework theorem.  Its
one-step oracle is supplied by the already formalized SVD spectral
`SVDBlockReadyOracle`, which is stronger than the current bidiagonalization
readiness invariant.  It is not derived by applying the final SVD theorem
directly to `A`.

## 8. Relation to Existing Instances

Bidiagonalization is the rectangular two-sided analogue of tridiagonalization:

1. tridiagonalization uses one unitary similarity on square Hermitian matrices;
2. bidiagonalization uses independent left and right unitary factors on
   rectangular matrices.

The implementation may reuse:

1. finite-order rank machinery from Hessenberg;
2. head-tail block infrastructure from the framework;
3. unitary step ideas from `OrthogonalHessenberg/PLAN.md`;
4. SVD target conventions if the SVD instance already defines compatible
   orthogonal/unitary matrix predicates.

## 9. Non-Goals

This plan does not prove SVD.  Bidiagonalization is a preprocessing reduction;
diagonalizing the bidiagonal matrix belongs to the SVD instance.

This plan does not modify LU, Hessenberg, orthogonal Hessenberg, or
tridiagonalization instances.

## 10. Current Status

Completed framework milestones:

- File skeleton is present:
  `Bidiagonalization.lean`, `Bidiagonalization/Details.lean`,
  `Bidiagonalization/Strategy.lean`, `Bidiagonalization/Direct.lean`, and
  `Bidiagonalization/Existence.lean`.
- Matrix-level target predicate is defined:
  `IsUpperBidiagonal`, `HasUnitaryBidiagonalization`, and
  universe-level `Bidiagonalization_P`.
- Base cases are implemented for empty row and empty column types.
- Strategy-side rectangular descent is implemented:
  `BidiagonalRowTail`, `BidiagonalColTail`,
  `BidiagonalizationReady`, `BidiagonalizationStepOracle`,
  `bidiagonalizationTwoSidedUnitaryTransform`,
  `bidiagonalizationHeadTailReduction`, and
  `bidiagonalization_strategy_core`.
- The measure is `Nat.min (Fintype.card m) (Fintype.card n)`, and
  `bidiagonal_tail_min_card_lt` proves strict progress after removing both
  heads.
- Transport and lift hooks are concrete:
  `bidiagonalization_transport_hook`, `bidiagonalization_lift_hook`,
  `bidiagonalization_descent_hooks`, and
  `bidiagonalization_strategy_proof`.
- The framework theorem chain is routed through
  `RectSubtypeInductionInstance.prove_for_matrix`:
  `exists_unitary_bidiagonalization_framework` and
  `exists_unitary_bidiagonalization_oracle`.
- A concrete complex theorem is available:
  `exists_unitary_bidiagonalization`, obtained by feeding the framework theorem
  the SVD spectral block-ready one-step bridge
  `bidiagonalizationStepOracleOfSVDBlockReady` /
  `bidiagonalizationStepOracle`.

Current oracle scope:

- `BidiagonalizationReady` is intentionally strong for the current block lift:
  after head-tail reindexing, both `toBlocks₂₁` and the full `toBlocks₁₂` are
  zero.  This is stronger than classical bidiagonal step readiness, but it is
  the invariant consumed by the verified block-diagonal lift.
- A standalone Householder or Givens bidiagonalization oracle has not yet been
  discharged.  The current concrete theorem uses the SVD spectral one-step
  block-ready construction instead.

## 11. Verification

Local completion checks:

```bash
lake build MatDecompFormal.Instances.Bidiagonalization
rg -n "sorry|admit|axiom|unsafe|undefined" \
  MatDecompFormal/Instances/Bidiagonalization \
  MatDecompFormal/Instances/Bidiagonalization.lean \
  --glob '!PLAN.md' -S
printf 'import MatDecompFormal.Instances.Bidiagonalization
#check MatDecompFormal.Instances.exists_unitary_bidiagonalization_framework
#check MatDecompFormal.Instances.exists_unitary_bidiagonalization_oracle
#check MatDecompFormal.Instances.exists_unitary_bidiagonalization
#check MatDecompFormal.Instances.BidiagonalizationStepOracle
#check MatDecompFormal.Instances.bidiagonalizationStepOracleOfSVDBlockReady
#check MatDecompFormal.Instances.bidiagonalizationStepOracle
#check MatDecompFormal.Instances.bidiagonalization_framework_inst
' | lake env lean --stdin
rg -n "prove_for_matrix|exists_unitary_bidiagonalization_framework|exists_unitary_bidiagonalization_oracle|exists_unitary_bidiagonalization|BidiagonalizationStepOracle|bidiagonalizationStepOracle" \
  MatDecompFormal/Instances/Bidiagonalization \
  MatDecompFormal/Instances/Bidiagonalization.lean -S
```

The broader command

```bash
lake build MatDecompFormal.Instances
```

is useful as an integration check, but it is not a Bidiagonalization-local
completion gate if unrelated instance directories fail independently.
