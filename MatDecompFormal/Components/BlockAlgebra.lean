import Mathlib.Data.Sum.Order
import Mathlib.LinearAlgebra.Matrix.Block
import MatDecompFormal.Framework.Fin

namespace MatDecompFormal.Components

open Matrix
open MatDecompFormal.Framework

/-!
# Block Algebra

This file collects the component-level block matrix algebra lemmas used by
lifting constructions. It stays at the pure algebra / block-reindex layer and
does not contain generic lifting cores or instance-oriented wrappers.
-/

section BlockAlgebra

variable {n₁ n₂ m₁ m₂ : ℕ} {R : Type*} [CommRing R]

/-- Block multiplication by a block-diagonal left factor. -/
lemma block_P_mul_A
    (A₁₁ : Matrix (Fin n₁) (Fin m₁) R) (A₁₂ : Matrix (Fin n₁) (Fin m₂) R)
    (A₂₁ : Matrix (Fin n₂) (Fin m₁) R) (A₂₂ : Matrix (Fin n₂) (Fin m₂) R)
    (P' : Matrix (Fin n₂) (Fin n₂) R) :
    (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 0 P') *
        (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) =
      fromBlocks A₁₁ A₁₂ (P' * A₂₁) (P' * A₂₂) := by
  simp [fromBlocks_multiply]

/-- Block multiplication of the standard lower/upper lifting pattern. -/
lemma block_L_mul_U
    (L₂₁ : Matrix (Fin n₂) (Fin n₁) R) (L' : Matrix (Fin n₂) (Fin n₂) R)
    (U₁₁ : Matrix (Fin n₁) (Fin n₁) R) (U₁₂ : Matrix (Fin n₁) (Fin n₂) R)
    (U' : Matrix (Fin n₂) (Fin n₂) R) :
    (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 L₂₁ L') *
        (fromBlocks U₁₁ U₁₂ (0 : Matrix (Fin n₂) (Fin n₁) R) U') =
      fromBlocks U₁₁ U₁₂ (L₂₁ * U₁₁) (L₂₁ * U₁₂ + L' * U') := by
  simp [fromBlocks_multiply]

/-- Block multiplication when the left factor is block diagonal. -/
lemma block_diag_L_mul_block_U
    (L' : Matrix (Fin n₂) (Fin n₂) R)
    (U₁₂ : Matrix (Fin n₁) (Fin n₂) R)
    (U' : Matrix (Fin n₂) (Fin n₂) R) :
    (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0
                (0 : Matrix (Fin n₂) (Fin n₁) R) L') *
        (fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) U₁₂
                    (0 : Matrix (Fin n₂) (Fin n₁) R) U') =
      fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) U₁₂
                 (0 : Matrix (Fin n₂) (Fin n₁) R) (L' * U') := by
  simp [fromBlocks_multiply]

end BlockAlgebra

section ReindexAndBlocks

variable {k m : ℕ} {R : Type*}

lemma toBlocks₁₁_reindex_finSuccEquivSum
    (A : Matrix (Fin (k + 1)) (Fin (m + 1)) R) :
    (Matrix.reindex (finSuccEquivSum k) (finSuccEquivSum m) A).toBlocks₁₁ = !![A 0 0] := by
  classical
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.reindex_apply, finSuccEquivSum]

lemma toBlocks_left_zero_of_first_col_zero [Zero R]
    (A : Matrix (Fin (k + 1)) (Fin (m + 1)) R)
    (h_zero_col : ∀ i, A i 0 = 0) :
    (Matrix.reindex (finSuccEquivSum k) (finSuccEquivSum m) A).toBlocks₁₁ = 0 ∧
    (Matrix.reindex (finSuccEquivSum k) (finSuccEquivSum m) A).toBlocks₂₁ = 0 := by
  classical
  constructor
  · ext i j
    simp [Matrix.toBlocks₁₁, Matrix.reindex_apply, finSuccEquivSum, h_zero_col]
  · ext i j
    simp [Matrix.toBlocks₂₁, Matrix.reindex_apply, finSuccEquivSum, h_zero_col]

end ReindexAndBlocks

end MatDecompFormal.Components
