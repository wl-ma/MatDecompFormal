# Jordan Form via the Descent Framework

This plan describes Jordan form using the project descent-template style.

The main theorem should not be specialized to `ℂ`, and it should not require an
algebraically closed field when only one operator is being reduced. Use a field
`K` together with a splitting hypothesis for the specific characteristic
polynomial. Algebraically closed fields and `ℂ` are convenience corollaries.

## 1. Target Theorems

Primary public matrix theorem:

```lean
theorem exists_jordan_matrix_of_splits
    {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    ∃ P : Matrix ι ι K, ∃ J : Matrix ι ι K,
      InvertibleMatrix P ∧
      IsJordanMatrix J ∧
      A = P * J * P⁻¹
```

This is the final public matrix target. The first Lean implementation target is
the same theorem shape routed through an explicit one-step `JordanStepOracle`;
the unsuffixed public theorem must not be used for an oracle-conditional result
unless the oracle has already been discharged.

Primary public linear-map theorem:

```lean
theorem exists_jordan_form_of_splits
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (T : V →ₗ[K] V)
    (hsplit : (LinearMap.charpoly T).Splits (RingHom.id K)) :
    ∃ b : Basis (Fin (FiniteDimensional.finrank K V)) K V,
      IsJordanMatrix (LinearMap.toMatrix b b T)
```

If `LinearMap.charpoly` is not the available mathlib spelling, define this
theorem by choosing an initial finite basis, applying the matrix theorem to
`LinearMap.toMatrix b₀ b₀ T`, and transporting the resulting matrix similarity
back to a basis statement. Do not block the matrix theorem on the exact
linear-map charpoly API.

Algebraically closed corollaries:

```lean
theorem exists_jordan_matrix_algClosed
    {K ι : Type*} [Field K] [IsAlgClosed K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    ...

theorem exists_jordan_form_algClosed
    {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : V →ₗ[K] V) :
    ...
```

Complex corollaries:

```lean
theorem exists_jordan_matrix_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    ...

theorem exists_jordan_form_complex
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) :
    ...
```

### Public API Invariant

- `exists_jordan_matrix_of_splits` and `exists_jordan_form_of_splits` are the
  main theorems.
- The main theorems must expose `[Field K]` and a split-characteristic-polynomial
  hypothesis for the specific matrix/operator.
- `[IsAlgClosed K]` theorems must use an explicit suffix such as `_algClosed`.
- `ℂ` theorems must use an explicit suffix such as `_complex`.
- Do not use the unsuffixed public theorem name for a theorem specialized to
  `ℂ`.
- Do not strengthen the main theorem to `[IsAlgClosed K]` unless there is also a
  split-polynomial theorem with the stronger public name above.

## 2. Algebraic Route

Two acceptable routes:

1. Rational canonical form plus splitting of invariant factors into powers of
   linear factors, then convert companion blocks into Jordan blocks.
2. Primary decomposition plus nilpotent Jordan-chain descent on each generalized
   eigenspace.

Preferred dependency direction:

```text
ModuleStructure -> RationalCanonical -> Jordan
```

but the nilpotent chain descent can be developed directly if it better matches
mathlib APIs.

Recommended implementation order:

1. Matrix-level split theorem through a `JordanStepOracle`.
2. Matrix-level algebraically closed and complex corollaries.
3. Basis/linear-map theorem by transporting the matrix theorem through an
   initial basis.
4. Remove the explicit oracle by discharging it through rational canonical form
   or primary decomposition.

## 3. Strict Descent-Template Contract

This section is a hard implementation contract. The Jordan development must use
the same recursive descent template as the other decomposition plans. Every item
below must appear as a concrete definition, theorem, structure field, or driver
argument in the implementation.

### 3.1 Universe

The first implementation uses the existing square matrix universe:

```lean
SquareUniverse K
```

The theorem-level assumptions are not stored in the universe object. Instead,
the splitting hypothesis is an input to the predicate:

```lean
def Jordan_P (x : SquareUniverse K) : Prop :=
  x.A.charpoly.Splits (RingHom.id K) → HasJordanMatrix x.A
```

This keeps the driver square-matrix compatible while preserving the final
split-polynomial public theorem over `[Field K]`.

The linear-map theorem is a bridge theorem after the matrix theorem. It may
choose a finite basis, apply the matrix theorem, and transport the resulting
similarity data back to a basis statement.

### 3.2 Measure

Use the standard square-subtype measure:

```lean
squareSubtypeμ x = Fintype.card x.ι
squareSubtypeμBase = 0
```

The recursive index removes the distinguished head element:

```lean
abbrev JordanTailIdx
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] :=
  { i : ι // i ≠ headElem (α := ι) }
```

Required progress lemma:

```lean
theorem jordan_tail_card_lt
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] :
    Fintype.card (JordanTailIdx ι) < Fintype.card ι
```

### 3.3 Predicate `P`

Define the matrix predicate without specializing scalars:

```lean
def IsJordanMatrix
    {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (J : Matrix ι ι K) : Prop := ...

def HasJordanMatrix
    {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ P : Matrix ι ι K, ∃ J : Matrix ι ι K,
    InvertibleMatrix P ∧ IsJordanMatrix J ∧ A = P * J * P⁻¹

def Jordan_P (x : SquareUniverse K) : Prop :=
  x.A.charpoly.Splits (RingHom.id K) → HasJordanMatrix x.A
```

`IsJordanMatrix` should be a data-bearing predicate, not a placeholder. It
should record a finite family of Jordan blocks, block sizes, eigenvalues, an
index equivalence, and the block-diagonal matrix equation.

### 3.4 Base

The universe-level base theorem must have the framework shape:

```lean
theorem jordan_base_univ
    (x : SquareUniverse K) :
    ((∀ x_sub : PosSquareUniverse K, (x_sub : SquareUniverse K) ≠ x) ∨
      squareSubtypeμ x ≤ squareSubtypeμBase) →
      Jordan_P x
```

The proof obtains `Fintype.card x.ι = 0` from
`squareSubtypeBaseDimEqZero`. For an empty index type, use:

```lean
P = 1
J = x.A
```

and prove the empty matrix is a Jordan matrix via an empty block family.

### 3.5 Transform

The transform is invertible similarity:

```lean
structure JordanSimilarityToken
    (K ι : Type*) [Field K] [Fintype ι] [DecidableEq ι] where
  P : Matrix ι ι K
  invP : InvertibleMatrix P

transform A token = token.P⁻¹ * A * token.P
```

The strategy relation records the equality
`B = token.P⁻¹ * A * token.P`.

Transport must also preserve the split hypothesis. Use characteristic-polynomial
similarity invariance to turn

```lean
A.charpoly.Splits (RingHom.id K)
```

into the corresponding splitting hypothesis for `B`.

### 3.6 Readiness

Readiness is not merely “the lower-left block is zero”. For Jordan form, the
one-step state must contain exactly the algebra needed to lift a recursive tail
Jordan form to the whole matrix.

The framework-facing predicate should have this shape:

```lean
def JordanLiftReady
    (K ι : Type*) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K) : Prop :=
  A.charpoly.Splits (RingHom.id K) →
    Jordan_P (SquareUniverse.ofMatrix (jordanTailSlice ι A)) →
      HasJordanMatrix A

def JordanDescentReady ... := JordanLiftReady ...
```

The concrete oracle should produce a stronger structured readiness object, for
example:

- one isolated Jordan block, generalized eigenspace component, or split
  companion block;
- a tail matrix indexed by `JordanTailIdx ι` or by the complement after removing
  the chosen block;
- the block/similarity equation needed by the lift lemma.

The current square driver removes one head index at a time. If the algebraic
construction removes a whole Jordan block or primary component at once, add a
block-indexed algebraic driver with the same template fields rather than hiding
that change in an ad hoc induction.

### 3.7 Slice

For the first square-driver version, use the lower-right head-tail slice:

```lean
def jordanTailSlice
    (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (A : Matrix ι ι K) :
    Matrix (JordanTailIdx ι) (JordanTailIdx ι) K := ...

def jordanHeadTailReduction :
    ReductionMethod ι ι (JordanTailIdx ι) (JordanTailIdx ι) K
```

The slice must be exactly the matrix passed to the recursive `Jordan_P` call.

### 3.8 Reach

Reach is initially provided by an explicit one-step oracle:

```lean
structure JordanStepOracle
    (K ι : Type*) [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] where
  P : Matrix ι ι K → Matrix ι ι K
  invertible_P : ∀ A, InvertibleMatrix (P A)
  ready :
    ∀ A, JordanDescentReady K ι ((P A)⁻¹ * A * (P A))
```

This oracle is a real mathematical dependency, not a cosmetic wrapper. The
oracle-free theorem is allowed only after constructing this oracle from
rational canonical form, primary decomposition, or nilpotent Jordan chains.

The conditional theorem must be named with an explicit suffix:

```lean
theorem exists_jordan_matrix_framework_oracle
    (oracle :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι],
        JordanStepOracle K ι)
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A
```

### 3.9 Transport

Transport moves a Jordan witness backward across invertible similarity.

If:

```lean
B = P⁻¹ * A * P
B = S * J * S⁻¹
```

then:

```lean
A = (P * S) * J * (P * S)⁻¹
```

Required theorem:

```lean
theorem jordan_transport_similarity
    (h : B = P⁻¹ * A * P)
    (hP : InvertibleMatrix P)
    (hB : HasJordanMatrix B) :
    HasJordanMatrix A
```

The proof hook for `Jordan_P` additionally supplies the transported split
hypothesis for `B`.

### 3.10 Lift

Lift converts structured readiness and a recursive tail Jordan witness into a
whole-matrix Jordan witness.

For the square-driver version:

```lean
theorem jordan_lift_from_ready
    (A : Matrix ι ι K)
    (hready : JordanDescentReady K ι A)
    (htail : Jordan_P (SquareUniverse.ofMatrix (jordanTailSlice ι A))) :
    Jordan_P (SquareUniverse.ofMatrix A)
```

Concrete lift lemmas should assemble block diagonal Jordan matrices. If a
one-dimensional head is already part of an existing Jordan chain, the readiness
data must include the off-diagonal `1` link needed to extend that chain.

### 3.11 Driver

The matrix implementation must be assembled through:

```lean
SquareStrategyData
mkSquareSubtypeInductionInstanceFromStrategy
SquareSubtypeInductionInstance.prove_for_matrix
```

Expected theorem chain:

```lean
noncomputable def jordan_strategy_core
    (oracle : ...) : SquareStrategyCore K

noncomputable def jordan_strategy_data
    (oracle : ...)
    (hooks : JordanDescentHooks oracle) :
    SquareStrategyData K Jordan_P

noncomputable def jordan_framework_inst
    (oracle : ...)
    (hooks : JordanDescentHooks oracle) :
    SquareSubtypeInductionInstance K

theorem exists_jordan_matrix_framework
    (oracle : ...)
    (hooks : JordanDescentHooks oracle)
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A

theorem exists_jordan_matrix_framework_oracle
    (oracle : ...)
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A
```

Only after the oracle is discharged may the final public theorem be introduced:

```lean
theorem exists_jordan_matrix_of_splits
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A
```

This theorem must call the framework theorem; it must not be proved by a
separate direct induction.

## 4. Required Lemmas

- Similarity transport for Jordan form.
- Block diagonal lift of Jordan matrices.
- Splitting of primary components under `charpoly.Splits`.
- Nilpotent operator has a Jordan chain decomposition.
- Companion block for `(X - λ)^k` is similar to a Jordan block.
- Basis/direct-sum to block-matrix bridge.

## 5. File Layout

```text
MatDecompFormal/Instances/Jordan/PLAN.md
MatDecompFormal/Instances/Jordan.lean
MatDecompFormal/Instances/Jordan/Details.lean
MatDecompFormal/Instances/Jordan/Strategy.lean
MatDecompFormal/Instances/Jordan/Direct.lean
MatDecompFormal/Instances/Jordan/Existence.lean
```

## 6. Verification

```bash
lake build MatDecompFormal.Instances.Jordan
lake build MatDecompFormal.Instances
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Jordan -S
```

## 7. Current Lean Status

Implemented:

- `jordanBlock`
- `JordanMatrixData`
- `IsJordanMatrix`
- `HasJordanMatrix`
- `Jordan_P`
- `Jordan_P_sub`
- `jordan_P_compat`
- `isJordanMatrix_reindex`
- `isJordanMatrix_empty`
- `base_jordan_empty`
- `jordan_transport_similarity`
- `jordan_similarity_charpoly`
- `JordanTailIdx`
- `jordanTailSlice`
- `JordanLiftReady`
- `JordanDescentReady`
- `JordanStepOracle`
- `jordanSimilarityTransform`
- `jordanHeadTailReduction`
- `jordan_strategy_core`
- `jordan_transport_hook`
- `jordan_lift_hook`
- `jordan_strategy_proof`
- `jordan_base_univ`
- `jordan_strategy_data`
- `jordan_framework_inst`
- `exists_jordan_matrix_framework`
- `exists_jordan_matrix_framework_oracle`

The current Lean theorem is intentionally oracle-conditional:

```lean
theorem exists_jordan_matrix_framework_oracle
    {K : Type u} [Field K]
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        JordanStepOracle K κ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A
```

Remaining work before introducing the final unsuffixed public theorem
`exists_jordan_matrix_of_splits`:

1. Construct `JordanStepOracle` from rational canonical form plus splitting of
   invariant factors, or from primary decomposition plus nilpotent Jordan-chain
   descent.
2. Prove the structured block lift that combines an isolated Jordan block or
   chain extension with the recursive tail witness.
3. Add algebraically closed and complex corollaries only as explicit-suffix
   corollaries after the split-polynomial theorem is available.
4. Add the linear-map/basis bridge theorem after the matrix theorem.
