# Jordan Form via the Descent Framework

Status: completed and verified.

This file records the completed Jordan-form route.  The hard requirement was
that the final arbitrary-matrix theorem be assembled through the project square
descent framework, with algebraic payloads feeding the framework rather than
replacing it by a standalone whole-matrix induction.

## Public API

The split-polynomial matrix theorem is:

```lean
theorem exists_jordan_matrix_of_splits
    {K : Type u} {ι : Type v} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A
```

The proof runs the concrete descent theorem on the same-universe
`ULift (Fin (Fintype.card ι))` model and transports the result back to the
user's index type using:

- `isJordanMatrix_reindex_universe`
- `hasJordanMatrix_reindex_universe`

The algebraically closed and complex matrix corollaries are:

```lean
theorem exists_jordan_matrix_algClosed
    {K : Type u} {ι : Type v} [Field K] [IsAlgClosed K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasJordanMatrix A

theorem exists_jordan_matrix_complex
    {ι : Type v} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    HasJordanMatrix A
```

The finite-dimensional linear-map theorem follows the existing
rational-canonical API convention in this repository and returns an
`ULift (Fin (Module.finrank K V))` basis:

```lean
theorem exists_jordan_form_of_splits
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [Module.Free K V] [Module.Finite K V]
    (T : V →ₗ[K] V)
    (hsplit : T.charpoly.Splits (RingHom.id K)) :
    ∃ b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V,
      IsJordanMatrix (LinearMap.toMatrix b b T)
```

The algebraically closed and complex linear-map corollaries are:

```lean
theorem exists_jordan_form_algClosed
    {K : Type u} {V : Type v} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]
    (T : V →ₗ[K] V) :
    ∃ b : Module.Basis (ULift.{u, 0} (Fin (Module.finrank K V))) K V,
      IsJordanMatrix (LinearMap.toMatrix b b T)

theorem exists_jordan_form_complex
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    [Module.Free ℂ V] [Module.Finite ℂ V]
    (T : V →ₗ[ℂ] V) :
    ∃ b : Module.Basis (ULift.{0, 0} (Fin (Module.finrank ℂ V))) ℂ V,
      IsJordanMatrix (LinearMap.toMatrix b b T)
```

## Proof Route

The completed route is:

```text
RCF elementary-factor data
-> companion prime-power generalized-Jordan witness
-> generalized-Jordan block-driver step data
-> SquareSubtypeInductionInstance.prove_for_matrix
-> exists_generalized_jordan_matrix
-> split specialization from generalized Jordan blocks to ordinary Jordan blocks
-> exists_jordan_matrix_of_splits
```

The concrete generalized theorem is:

```lean
theorem exists_generalized_jordan_matrix
    {K : Type u} [Field K]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι K) :
    HasGeneralizedJordanMatrix A
```

It is proved by `exists_generalized_jordan_matrix_framework_bridge` with the
concrete `generalizedJordanRCFBlockDriverBridge K`; that framework theorem calls
`SquareSubtypeInductionInstance.prove_for_matrix`.

The companion prime-power algebraic payload is:

```lean
theorem companion_power_hasGeneralizedJordan
    {K : Type u} {ι : Type v} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {C : Matrix ι ι K} {p : K[X]} (k : Nat)
    (hp_monic : p.Monic)
    (hp_irred : Irreducible p)
    (hk : 0 < k)
    (hC : SingleCompanionBlockForm C (p ^ k)) :
    HasGeneralizedJordanMatrix C
```

The ordinary split specialization is:

```lean
theorem hasJordanMatrix_of_hasGeneralizedJordanMatrix_of_splits
    {K ι : Type u} [Field K]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι K}
    (hA : HasGeneralizedJordanMatrix A)
    (hsplit : A.charpoly.Splits (RingHom.id K)) :
    HasJordanMatrix A
```

## Verification

Verified command:

```text
lake build MatDecompFormal.Instances.Jordan
```

Result: build completed successfully.

Audit scans:

```text
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Jordan -S
rg -n "GeneralizedJordanElementaryBlockBridge|companion_power_hasGeneralizedJordan_bridge|exists_generalized_jordan_matrix_framework_companion_bridge" MatDecompFormal/Instances/Jordan -S
```

The placeholder scan has no Lean-source hits.  The removed bridge-name scan has
no Lean-source hits.
