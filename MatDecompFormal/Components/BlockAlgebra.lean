import Mathlib.Data.Sum.Order
import Mathlib.LinearAlgebra.Matrix.Block

namespace MatDecompFormal.Components

open Matrix

/-!
# Block Algebra

This file collects the component-level block matrix algebra lemmas used by
lifting constructions. It stays at the pure algebra / block-reindex layer and
does not contain generic lifting cores or instance-oriented wrappers.
-/

section BlockAlgebra

variable {ι₁ ι₂ κ₁ κ₂ : Type*} {R : Type*} [Semiring R]

/-- Block multiplication by a block-diagonal left factor. -/
lemma block_P_mul_A
    [Fintype ι₁] [Fintype ι₂] [Fintype κ₁] [Fintype κ₂]
    [DecidableEq ι₁]
    (A₁₁ : Matrix ι₁ κ₁ R) (A₁₂ : Matrix ι₁ κ₂ R)
    (A₂₁ : Matrix ι₂ κ₁ R) (A₂₂ : Matrix ι₂ κ₂ R)
    (P' : Matrix ι₂ ι₂ R) :
    (fromBlocks (1 : Matrix ι₁ ι₁ R) 0 0 P') *
        (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) =
      fromBlocks A₁₁ A₁₂ (P' * A₂₁) (P' * A₂₂) := by
  simp [fromBlocks_multiply]

/-- Block multiplication of the standard lower/upper lifting pattern. -/
lemma block_L_mul_U
    [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁]
    (L₂₁ : Matrix ι₂ ι₁ R) (L' : Matrix ι₂ ι₂ R)
    (U₁₁ : Matrix ι₁ ι₁ R) (U₁₂ : Matrix ι₁ ι₂ R)
    (U' : Matrix ι₂ ι₂ R) :
    (fromBlocks (1 : Matrix ι₁ ι₁ R) 0 L₂₁ L') *
        (fromBlocks U₁₁ U₁₂ (0 : Matrix ι₂ ι₁ R) U') =
      fromBlocks U₁₁ U₁₂ (L₂₁ * U₁₁) (L₂₁ * U₁₂ + L' * U') := by
  simp [fromBlocks_multiply]

/-- Block multiplication when the left factor is block diagonal. -/
lemma block_diag_L_mul_block_U
    [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁]
    (L' : Matrix ι₂ ι₂ R)
    (U₁₂ : Matrix ι₁ ι₂ R)
    (U' : Matrix ι₂ ι₂ R) :
    (fromBlocks (1 : Matrix ι₁ ι₁ R) 0
                (0 : Matrix ι₂ ι₁ R) L') *
        (fromBlocks (0 : Matrix ι₁ ι₁ R) U₁₂
                    (0 : Matrix ι₂ ι₁ R) U') =
      fromBlocks (0 : Matrix ι₁ ι₁ R) U₁₂
                 (0 : Matrix ι₂ ι₁ R) (L' * U') := by
  simp [fromBlocks_multiply]

end BlockAlgebra

end MatDecompFormal.Components
