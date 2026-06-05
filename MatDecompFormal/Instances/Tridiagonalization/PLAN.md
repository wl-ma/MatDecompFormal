# Tridiagonalization via the Descent Framework

This plan describes a strict descent-template implementation of matrix
tridiagonalization.  The intended theorem is the symmetric/Hermitian analogue of
orthogonal Hessenberg reduction: a symmetric or Hermitian matrix is orthogonally
or unitarily similar to a tridiagonal matrix.

The public theorem must be assembled through the project descent framework, not
by a standalone induction proof.

## 1. Target Theorems

Real symmetric tridiagonalization:

```lean
theorem exists_orthogonal_tridiagonalization
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ)
    (hA : Aᵀ = A) :
    ∃ Q : Matrix ι ι ℝ, ∃ T : Matrix ι ι ℝ,
      IsOrthogonalMatrix Q ∧
      IsTridiagonal T ∧
      Tᵀ = T ∧
      A = Q * T * Qᵀ
```

Hermitian unitary version:

```lean
theorem exists_unitary_tridiagonalization
    {𝕜 ι : Type*} [RCLike 𝕜]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι 𝕜)
    (hA : Aᴴ = A) :
    ∃ Q : Matrix ι ι 𝕜, ∃ T : Matrix ι ι 𝕜,
      IsUnitaryMatrix Q ∧
      IsTridiagonal T ∧
      Tᴴ = T ∧
      A = Q * T * Qᴴ
```

The Hermitian theorem should be the main theorem if mathlib's star/conjugate
transpose API is stronger than the real transpose API.  The real theorem can be
a specialization.

## 2. Predicate Layer

Define a local tridiagonal predicate using finite order rank, matching the
existing `IsUpperHessenberg` style.

```lean
def IsTridiagonal
    {ι R : Type*} [Fintype ι] [LinearOrder ι] [Zero R]
    (T : Matrix ι ι R) : Prop :=
  ∀ i j,
    finiteOrderRank ι j + 1 < finiteOrderRank ι i ∨
      finiteOrderRank ι i + 1 < finiteOrderRank ι j →
    T i j = 0
```

For Hermitian matrices, upper Hessenberg plus Hermitian implies tridiagonal.
This bridge should be proved and reused:

```lean
theorem isTridiagonal_of_isUpperHessenberg_of_hermitian
    (hHess : IsUpperHessenberg T)
    (hHerm : Tᴴ = T) :
    IsTridiagonal T
```

Target predicate:

```lean
def HasUnitaryTridiagonalization
    {𝕜 ι : Type*} [RCLike 𝕜]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι 𝕜) : Prop :=
  Aᴴ = A →
    ∃ Q : Matrix ι ι 𝕜, ∃ T : Matrix ι ι 𝕜,
      IsUnitaryMatrix Q ∧
      IsTridiagonal T ∧
      Tᴴ = T ∧
      A = Q * T * Qᴴ
```

Use the implication form for the framework predicate so base, transport, and
lift can be stated uniformly over all square matrices.

## 3. Strict Descent-Template Contract

Every item in this section must appear as a concrete Lean definition, theorem,
or strategy field in the final implementation.

### 3.1 Universe

Use the existing square universe:

```lean
SquareUniverse 𝕜
```

Framework predicate:

```lean
def Tridiagonalization_P (x : SquareUniverse 𝕜) : Prop :=
  HasUnitaryTridiagonalization x.A
```

Positive universes use `PosSquareUniverse 𝕜`; nonempty index instances come
from `posSquareUniverse_nonempty`.

### 3.2 Measure

Use the standard square-subtype measure:

```lean
μ x = squareSubtypeμ x = Fintype.card x.ι
μ_base = squareSubtypeμBase = 0
```

The slice removes the current head index:

```lean
abbrev TridiagonalTailIdx
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { i : ι // i ≠ headElem (α := ι) }
```

Required progress lemma:

```lean
theorem tridiagonal_tail_card_lt
    {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] :
    Fintype.card (TridiagonalTailIdx ι) < Fintype.card ι
```

The proof is the standard `Fintype.card_subtype_lt` argument used in LU,
Hessenberg, and Schur plans.

### 3.3 Base

Base theorem:

```lean
theorem tridiagonalization_base_univ
    (x : SquareUniverse 𝕜) :
    ((∀ x_sub : PosSquareUniverse 𝕜,
        (x_sub : SquareUniverse 𝕜) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      Tridiagonalization_P x
```

The proof obtains `Fintype.card x.ι = 0`, gives the trivial witness
`Q = 1`, `T = x.A`, and proves `IsTridiagonal` by subsingleton/empty index
reasoning.  The Hermitian assumption supplies `Tᴴ = T`.

### 3.4 Transformation

The transformation is unitary similarity:

```lean
B = Qᴴ * A * Q
```

Token:

```lean
structure TridiagonalizationToken (𝕜 ι : Type*) where
  Q : Matrix ι ι 𝕜
  unitary_Q : IsUnitaryMatrix Q
```

Transform field:

```lean
transform A token = token.Qᴴ * A * token.Q
```

Transport hook:

If `B = Qᴴ * A * Q` and `B` has a unitary tridiagonal witness, then `A` has one:

```lean
theorem tridiagonalization_transport_similarity
    (hQ : IsUnitaryMatrix Q)
    (hB : B = Qᴴ * A * Q)
    (hTri : HasUnitaryTridiagonalization B) :
    HasUnitaryTridiagonalization A
```

For an input Hermitian proof `Aᴴ = A`, first prove `Bᴴ = B`; then use the
witness for `B`; finally compose unitary factors:

```lean
A = (Q * S) * T * (Q * S)ᴴ
```

### 3.5 Readiness

After one unitary step, the transformed matrix must have a protected first
column and row:

```lean
def TridiagonalizationReady
    (A : Matrix ι ι 𝕜) : Prop :=
  ∀ i,
    i ≠ headElem →
    i ≠ secondElem →
      (headTailPlain A).toBlocks₂₁ i () = 0
```

This should be phrased in the project head-tail index type.  The mathematical
meaning is: below the first subdiagonal, the first column is zero.  Hermitian
symmetry then gives the matching first row zeros.

The concrete step oracle must produce a unitary `Qtail`, lifted as
`diag(1, Qtail)`, that makes this readiness condition true.

### 3.6 Slice

The recursive slice is the lower-right tail block of the transformed matrix:

```lean
slice B = B.toBlocks₂₂
```

Because unitary similarity preserves Hermitian structure, the lift hook receives
the recursive witness for a Hermitian tail matrix.

Required lemma:

```lean
theorem tail_hermitian_of_parent_hermitian
    (hA : Aᴴ = A) :
    (tailSlice A)ᴴ = tailSlice A
```

### 3.7 Lift

Lift hook:

```lean
theorem tridiagonalization_lift
    (hReady : TridiagonalizationReady B)
    (hTail : HasUnitaryTridiagonalization (tailSlice B)) :
    HasUnitaryTridiagonalization B
```

Given `hB : Bᴴ = B`, apply `hTail` to the tail Hermitian proof and obtain:

```lean
tailSlice B = S * Ttail * Sᴴ
```

Lift `S` block-diagonally:

```lean
Sblk = fromBlocks 1 0 0 S
```

Then build:

```lean
T = Sblkᴴ * B * Sblk
```

or equivalently assemble the block matrix whose lower-right block is `Ttail`.
Prove:

1. `Sblk` is unitary.
2. `Tᴴ = T`.
3. `IsTridiagonal T`.
4. `B = Sblk * T * Sblkᴴ`.

The tridiagonal zero proof uses:

1. `hReady` for the first column below the subdiagonal.
2. Hermitian symmetry for the first row beyond the superdiagonal.
3. recursive `IsTridiagonal Ttail` for the tail-tail block.

## 4. One-Step Oracle

The strict template should first be implemented with an oracle, then discharged
with Householder or Givens.

```lean
structure TridiagonalizationStepOracle (𝕜 : Type*) where
  Q :
    ∀ {ι} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
      Matrix ι ι 𝕜 → Matrix ι ι 𝕜
  unitary_Q :
    ∀ A, IsUnitaryMatrix (Q A)
  ready :
    ∀ A, TridiagonalizationReady ((Q A)ᴴ * A * Q A)
```

For correctness, the oracle should only be required on index types with at least
two elements.  For dimension `0` or `1`, the base/lift path is trivial.

## 5. Concrete Step: Householder

For a Hermitian matrix, take the tail of the first column below the first
subdiagonal and use a Householder reflector on the tail index to map it to the
first tail coordinate.

Block structure:

```lean
Qstep = fromBlocks 1 0 0 Qtail
B = Qstepᴴ * A * Qstep
```

Required Householder lemmas:

```lean
theorem householder_unitary :
    IsUnitaryMatrix (householder x)

theorem householder_column_ready :
    ∀ i, i ≠ headElem →
      ((householder x)ᴴ * x) i () = 0
```

Degenerate case: if the vector below the first subdiagonal is already zero, use
`Qtail = 1`.

## 6. Concrete Step: Givens Fallback

If Householder is too expensive, use finite products of Givens rotations to zero
the entries below the first tail coordinate one by one.

Required lemmas:

```lean
theorem givens_unitary :
    IsUnitaryMatrix (givens i j a b)

theorem givens_preserves_existing_zeroes :
    ...

theorem givens_product_ready :
    TridiagonalizationReady (Qᴴ * A * Q)
```

This route has easier scalar formulas but more finite-order bookkeeping.

## 7. Framework Assembly

Files should be introduced in this order:

1. `Details.lean`: `IsTridiagonal`, target predicates, base cases, unitary
   similarity transport lemmas.
2. `Strategy.lean`: tail index, transform token, strategy core, measure proof,
   slice definition, readiness predicate.
3. `Direct.lean`: transport and lift hooks.
4. `Existence.lean`: strict framework instantiation and oracle-routed public
   theorem.
5. `Householder.lean` or `Givens.lean`: concrete oracle.
6. `Tridiagonalization.lean`: aggregate imports.

The public theorem must be routed as:

```lean
noncomputable def tridiagonalization_strategy_data :
    SquareStrategyData 𝕜 Tridiagonalization_P := ...

noncomputable def tridiagonalization_framework_inst :
    SquareSubtypeInductionInstance 𝕜 := ...

theorem exists_unitary_tridiagonalization ... :=
  SquareSubtypeInductionInstance.prove_for_matrix
    (inst := tridiagonalization_framework_inst) A
```

No direct standalone induction theorem should be the final public theorem.

## 8. Relation to Existing Instances

Orthogonal Hessenberg proves `Hermitian A` can be unitarily reduced to upper
Hessenberg.  This tridiagonalization plan specializes that idea and uses the
Hermitian invariant to strengthen the output zero pattern from Hessenberg to
tridiagonal.

The implementation may reuse:

1. `IsUpperHessenberg` and rank lemmas from `Hessenberg/Details.lean`.
2. head-tail reindexing from the framework.
3. boundary-column ideas from `Hessenberg/Boundary.lean`.
4. unitary step design from `OrthogonalHessenberg/PLAN.md`.

## 9. Non-Goals

This plan does not prove eigenvalue existence, Schur form, or diagonalization.
It only proves unitary similarity to tridiagonal form for Hermitian inputs.

This plan does not modify the existing ordinary Hessenberg theorem.
