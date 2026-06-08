# Normal Matrix Decomposition via the Descent Framework

This plan describes how to prove the normal matrix decomposition theorem using
the existing descent framework:

```lean
Transformation
ReductionMethod
ReductionStrategy
SquareStrategyData
SquareSubtypeInductionInstance
```

The intended direction is to make the final theorem use the same proof pipeline
as PLU, QR, Householder QR, Givens QR, and Cholesky.

## 1. Target theorem

Initial target over complex square matrices:

```lean
theorem exists_normal_spectral_decomposition
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormal A) :
    ∃ U D : Matrix ι ι ℂ,
      IsUnitaryMatrix U ∧
      D.IsDiag ∧
      A = U * D * Uᴴ
```

The exact predicate should be packaged as:

```lean
def NormalSpectral_P (x : SquareUniverse ℂ) : Prop :=
  IsNormal x.A →
    ∃ U D : Matrix x.ι x.ι ℂ,
      IsUnitaryMatrix U ∧ D.IsDiag ∧ x.A = U * D * Uᴴ
```

This mirrors Cholesky: the framework proves a proposition on every square
universe, and the normality assumption is consumed only at the final property
level.

## 2. Descent shape

The recursive step should follow the current head-tail template.

For nontrivial `ι`:

1. Find an eigenvector `v : ι → ℂ` of `A`.
2. Normalize it.
3. Build a unitary transformation `Q` whose first column is `v`.
4. Conjugate:

```lean
B = Qᴴ * A * Q
```

5. Use normality of `A` and eigenvector-head construction to prove:

```lean
B = fromBlocks λ 0 0 B_tail
```

or equivalently that the off-diagonal head-tail blocks vanish.

6. Recurse on `B_tail`.
7. Lift the tail decomposition to the original matrix by block diagonal
   extension and conjugation by `Q`.

The key difference from QR/PLU is that the transformation is a unitary
similarity, not just left multiplication.

## 3. Framework mapping

### Transformation

Add a transformation family for unitary similarity:

```lean
UnitarySimilarityTransform
```

Expected relation:

```lean
B = Qᴴ * A * Q
```

with `IsUnitaryMatrix Q`.

This should become a concrete `Transformation` instance whose `Goal` records the
unitary data and whose `apply` returns the conjugated matrix.

### ReductionMethod

Add a head-tail reduction for normal matrices:

```lean
normalHeadTailReduction
```

The slice should be the lower-right tail block after unitary similarity:

```lean
slice B = B.submatrix tail tail
```

The `IsSliceable` condition should include:

```lean
IsNormal A
```

plus the existence of a normalized eigenvector/unitary basis step, or a separate
ready predicate:

```lean
NormalEigenReady ι A
```

### ReductionStrategy

The strategy should combine:

```lean
UnitarySimilarityTransform
normalHeadTailReduction
```

into a `SquareStrategyCore ℂ`.

The measure is still cardinality of the square index type, so the existing
`SquareStrategyData` machinery should apply directly.

## 4. Required mathematical lemmas

### Eigenvector existence

For complex finite-dimensional matrices:

```lean
IsNormal A → Nontrivial ι → ∃ μ v, v ≠ 0 ∧ A.mulVec v = μ • v
```

This may come from mathlib spectral/eigenvalue APIs, but the exact API must be
audited before implementation.

### Unitary completion

Given a nonzero vector `v`, construct a unitary matrix `Q` with first column
`v / ‖v‖`.

Possible approaches:

1. Use an orthonormal basis extension theorem if mathlib exposes one.
2. Introduce this as a component lemma first, then discharge it via mathlib.
3. Temporarily isolate it as the only high-level hook, while keeping the
   framework proof real.

### Normal block diagonalization

If `A` is normal and `e₀` is an eigenvector after conjugation, prove the first
row/column decouple:

```lean
IsNormal B →
B e₀ j = 0 for tail j →
B i e₀ = 0 for tail i
```

The useful theorem is that for normal matrices, eigenvectors of `A` are also
eigenvectors of `Aᴴ` with conjugate eigenvalue. This gives the vanishing of both
off-diagonal blocks.

### Tail normality

If `B` is normal and block diagonal as:

```lean
fromBlocks λ 0 0 B_tail
```

then:

```lean
IsNormal B_tail
```

### Lift

From tail decomposition:

```lean
B_tail = U_tail * D_tail * U_tailᴴ
```

construct:

```lean
U_B = blockDiag 1 U_tail
D_B = blockDiag λ D_tail
```

then:

```lean
B = U_B * D_B * U_Bᴴ
```

Finally transport across the unitary similarity:

```lean
A = Q * B * Qᴴ
  = (Q * U_B) * D_B * (Q * U_B)ᴴ
```

and prove `Q * U_B` is unitary.

## 5. File layout

Proposed Lean files:

```text
MatDecompFormal/Instances/Normal.lean
MatDecompFormal/Instances/Normal/Details.lean
MatDecompFormal/Instances/Normal/Strategy.lean
MatDecompFormal/Instances/Normal/Direct.lean
MatDecompFormal/Instances/Normal/Existence.lean
```

Roles:

- `Details.lean`: predicates, unitary/spectral helper lemmas, block lemmas.
- `Strategy.lean`: `NormalEigenReady`, unitary similarity transform, reduction
  core, strategy proof data.
- `Direct.lean`: concrete lift from tail decomposition to full decomposition.
- `Existence.lean`: final theorem routed through
  `SquareSubtypeInductionInstance.prove_for_matrix`.
- `Normal.lean`: public imports.

## 6. Implementation order

1. Define `HasNormalSpectral` and `NormalSpectral_P`.
2. Add a stub-free base case for `Subsingleton ι`.
3. Add block diagonal lift lemmas independent of eigenvectors.
4. Add unitary similarity transport lemmas.
5. Define the strategy core with a high-level `NormalEigenReady` predicate.
6. Prove the lift assuming the ready predicate and block diagonalization lemmas.
7. Assemble `SquareStrategyData`.
8. Assemble `SquareSubtypeInductionInstance`.
9. Prove the final theorem via `prove_for_matrix`.
10. Only after the framework route compiles, discharge the remaining high-level
    eigenvector/unitary-completion hooks.

## 7. Success criteria

The final audit should show:

```bash
rg -n '<unsupported proof placeholder patterns>' MatDecompFormal/Instances/Normal -S
rg -n 'prove_for_matrix|mkSquareSubtypeInductionInstanceFromStrategy' \
  MatDecompFormal/Instances/Normal -S
lake build MatDecompFormal
```

Expected proof route:

```text
exists_normal_spectral_decomposition
  -> normal_framework_inst
  -> mkSquareSubtypeInductionInstanceFromStrategy
  -> normal_strategy_data
  -> normal_strategy_core
  -> unitary similarity + head-tail reduction
```

## 8. Main risk

The framework part should be straightforward. The hard part is mathlib API
alignment for:

1. eigenvector existence over `ℂ`,
2. orthonormal/unitary completion,
3. normal matrix eigenvector behavior under adjoint.

These should be isolated behind small component lemmas so that the recursive
framework proof can be developed independently and kept clean.

## 9. Current implementation status

Implemented files:

```text
MatDecompFormal/Instances/Normal.lean
MatDecompFormal/Instances/Normal/Details.lean
MatDecompFormal/Instances/Normal/Strategy.lean
MatDecompFormal/Instances/Normal/Direct.lean
MatDecompFormal/Instances/Normal/Existence.lean
```

Current compiled theorem:

```lean
theorem exists_normal_spectral_decomposition_framework
    (oracle :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Nonempty κ],
        NormalSimilarityOracle κ)
    (hooks : NormalDescentHooks oracle)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : IsNormalMatrix A) :
    HasNormalSpectral A
```

This theorem already follows the intended framework route:

```text
exists_normal_spectral_decomposition_framework
  -> normal_framework_inst
  -> mkSquareSubtypeInductionInstanceFromStrategy
  -> normal_strategy_data
  -> normal_strategy_core
  -> SquareSubtypeInductionInstance.prove_for_matrix
```

The remaining work is not hidden behind unsupported proof placeholders; it is exposed as two
explicit parameters:

- `NormalSimilarityOracle`: constructs a unitary similarity putting a matrix into
  head-tail block-ready form.
- `NormalDescentHooks`: proves transport and lift for `NormalSpectral_P` along
  the strategy core.

Next implementation step: construct `NormalDescentHooks.lift` from block diagonal
lift lemmas, then construct `NormalSimilarityOracle` from eigenvector existence
and unitary basis completion.
