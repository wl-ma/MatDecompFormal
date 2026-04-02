import MatDecompFormal.Components.BlockAlgebra
import MatDecompFormal.Components.Lifting.LowLevel
import MatDecompFormal.Components.Lifting.Generic
import MatDecompFormal.Components.Lifting.PermutationUnitLowerUpper

/-!
# Block Lifting

Stable aggregate entry point for block-lifting-related component modules.

Import order follows the intended layering:
1. pure block algebra
2. low-level transport / lifting tools
3. generic lifting core
4. instance-oriented wrappers
-/
