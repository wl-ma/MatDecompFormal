# Rational Canonical Audit Fix Plan

This plan describes the code changes needed after the Instances decomposition
audit. It supplements `PLAN.md`; do not overwrite the original plan.

## Audit Finding

The rational canonical form instance has a strong public theorem surface and a
rich block framework. The proof is necessarily bridge-heavy and nonconstructive:
it depends on module-theoretic structure rather than a local executable
algorithm trace.

This is not a mathematical error. The repair is to make the API and comments
identify which theorems are framework/block proofs and which parts are algebraic
bridges.

## Goal

Expose a clean separation:

1. block/descent framework theorem with an explicit oracle or ready data;
2. module-theory bridge that constructs the oracle or directly supplies the
   canonical block data;
3. public existence theorem.

The public theorem can remain:

```lean
theorem exists_rational_canonical_matrix ...
```

but supporting names/comments should not suggest an executable rational
canonical algorithm unless a step trace is explicitly recorded.

## Required Changes

1. Inspect `Strategy.lean`, `BlockStrategy.lean`, `ModuleBridge.lean`, and
   `Existence.lean`.
2. Identify the exact route from public theorem to bridge-heavy module facts.
3. Add or improve theorem aliases/comments so the route is visible:

   ```text
   framework/block oracle theorem
   module bridge theorem
   public existence theorem
   ```

4. If algorithmic trace support is desired, define a separate trace record for
   cyclic-summand isolation and companion-block assembly. Do not retrofit this
   into the ordinary existence theorem.
5. Ensure any dependency on `ModuleStructure` uses the strengthened Smith/module
   predicates once those are repaired.

## Non-Goals

- Do not remove valid bridge-based existence theorems.
- Do not claim executable rational canonical form computation from
  `Classical.choose` or module bridge data.
- Do not specialize the main theorem to algebraically closed fields; rational
  canonical form should stay over `[Field K]`.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.RationalCanonical
lake build MatDecompFormal.Instances
rg -n "Oracle|Bridge|Block|exists_rational_canonical|trace|Classical.choose" MatDecompFormal/Instances/RationalCanonical -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/RationalCanonical -S
```

Manual review criterion: comments and theorem names should support the paper
claim "existence via framework plus algebraic bridge", not "executable
rational-canonical algorithm".
