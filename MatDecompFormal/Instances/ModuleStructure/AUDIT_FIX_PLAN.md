# Module Structure Audit Fix Plan

This plan describes the code changes needed after the Instances decomposition
audit. It supplements `PLAN.md`; do not overwrite the original plan.

## Audit Finding

The current module-structure instance only packages equivalence of a
presentation matrix to a Smith-like matrix. It does not yet state the usual PID
module structure theorem as a decomposition into a free part plus cyclic torsion
summands. It also inherits the current weakness of `IsSmithNormalForm`.

## Goal

Layer the API so the matrix-level presentation result is explicit, and add a
stronger module-level classification target when the quotient-module
infrastructure is available.

Keep this theorem as presentation-level:

```lean
theorem exists_presented_pid_module_structure
    (A : Matrix rel gen R) :
    HasPresentedPIDModuleStructure A
```

Add or plan a stronger theorem:

```lean
theorem exists_pid_module_structure
    {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ freeRank torsionData,
      PIDModuleDecomposition R M freeRank torsionData
```

The torsion data should refer to invariant factors from the strengthened Smith
normal form predicate.

## Required Changes

1. First fix `SmithNormalFormData`; this instance should depend on the
   strengthened Smith predicate.
2. Rename or document the current `HasPIDModuleStructure` as presentation-level
   data if it remains only matrix equivalence.
3. Introduce a new structure for actual module decomposition:
   - free rank;
   - finite ordered invariant-factor list;
   - cyclic summand modules `R / (d_i)`;
   - divisibility chain `d_i ∣ d_{i+1}`;
   - an isomorphism from `M` or the presented module to the direct sum.
4. For presentation matrices, prove a bridge from strengthened Smith normal form
   to the direct-sum decomposition of the cokernel presentation.
5. For abstract finitely generated modules, either:
   - reduce to a finite presentation and use the presentation theorem; or
   - expose an oracle/bridge parameter if mathlib APIs are not yet ready.
6. Add forgetful lemmas from module decomposition to the current
   presentation-matrix normal-form payload.

## Non-Goals

- Do not advertise the current matrix-equivalence wrapper as the full PID module
  classification theorem.
- Do not duplicate Smith pivot-reduction proof in this instance.
- Do not proceed with the full classification theorem until Smith's divisibility
  chain has been strengthened.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.Smith
lake build MatDecompFormal.Instances.ModuleStructure
lake build MatDecompFormal.Instances
rg -n "HasPIDModuleStructure|HasPresentedPIDModuleStructure|PIDModuleDecomposition|cyclic|freeRank|Smith" MatDecompFormal/Instances/ModuleStructure -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/ModuleStructure -S
```

Manual review criterion: names must clearly distinguish presentation normal form
from the full abstract PID module structure theorem.
