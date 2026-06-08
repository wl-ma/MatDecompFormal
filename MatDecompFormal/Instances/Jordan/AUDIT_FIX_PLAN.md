# Jordan Audit Fix Plan

This plan describes the code changes needed after the Instances decomposition
audit. It supplements `PLAN.md`; do not overwrite the original plan.

## Audit Finding

The ordinary and generalized Jordan theorem surface is broad and useful. Like
rational canonical form, correctness depends on substantial bridge
infrastructure, not on a short local elimination algorithm. This is acceptable
for existence theorems, but the API and comments should not overstate
algorithmic trace content.

## Goal

Separate:

1. split-field Jordan existence;
2. algebraically closed and complex corollaries;
3. generalized Jordan/rational-canonical-style block statements;
4. optional trace-level Jordan-chain construction.

Only the fourth item should be used to claim that the proof records explicit
Jordan-chain construction steps.

## Required Changes

1. Inspect:
   - `Strategy.lean`
   - `Existence.lean`
   - `SplitSpecialization.lean`
   - `Generalized.lean`
   - `GeneralizedExistence.lean`
2. Check that split hypotheses are visible on theorems that need ordinary
   Jordan form over a non-algebraically-closed field.
3. Add comments or aliases identifying bridge-heavy theorems versus
   framework/block theorems.
4. If a trace-level theorem is desired, define a Jordan-chain data record:
   - eigenvalue;
   - chain length;
   - chain vectors;
   - linear independence/spanning data;
   - block assembly into the final Jordan matrix.
5. Add forgetful lemmas from chain-level data to existing `HasJordan` or
   `HasGeneralizedJordan` predicates.
6. Recheck dependencies on RationalCanonical and ModuleStructure after Smith and
   ModuleStructure are strengthened.

## Non-Goals

- Do not remove valid generalized Jordan/rational-canonical-style statements.
- Do not claim ordinary Jordan form without a splitting or algebraically closed
  hypothesis.
- Do not claim explicit chain construction when the proof uses bridge data or
  `Classical.choose` without exposing chains.

## Acceptance Checks

```bash
lake build MatDecompFormal.Instances.Jordan
lake build MatDecompFormal.Instances
rg -n "Jordan|Generalized|Split|Bridge|trace|chain|Classical.choose" MatDecompFormal/Instances/Jordan -S
rg -n "sorry|admit|axiom|unsafe|undefined" MatDecompFormal/Instances/Jordan -S
```

Manual review criterion: theorem names and comments should clearly separate
ordinary split Jordan form, generalized Jordan form, and any future
chain-trajectory theorem.
