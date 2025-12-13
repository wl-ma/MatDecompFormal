import Mathlib.LinearAlgebra.Matrix.Block

namespace MatDecompFormal.Components

open Matrix

/-!
# 分块矩阵代数库 (Block Matrix Algebra Library)

本文件提供了一些**纯代数**的分块矩阵运算引理，全部在
`Matrix (Sum (Fin n₁) (Fin n₂)) (Sum (Fin m₁) (Fin m₂)) R` 的
具体世界中工作。

这些引理是后续 `Instances` 中 `lift_from_slice` 证明的“代数积木”，
主要用于把矩阵方程拆成对块的等式。
-/

section BlockAlgebra

variable {n₁ n₂ m₁ m₂ : ℕ} {R : Type*} [CommRing R]

/-!
## fromBlocks 与矩阵乘法

这一节给出几条常用的分块乘法公式，形式都类似：

* `(fromBlocks ...) * (fromBlocks ...) = fromBlocks (...) (...) (...) (...)`
-/

/--
**代数积木 1**: `(P_block * A_block)` 的分块形式。

左边的 `P_block` 是
\[
\begin{pmatrix}
  I & 0 \\
  0 & P'
\end{pmatrix},
\]
右边是一般分块矩阵
\[
\begin{pmatrix}
  A₁₁ & A₁₂ \\
  A₂₁ & A₂₂
\end{pmatrix}.
\]
结果是把右下两块左乘 `P'`。
-/
lemma block_P_mul_A
    (A₁₁ : Matrix (Fin n₁) (Fin m₁) R) (A₁₂ : Matrix (Fin n₁) (Fin m₂) R)
    (A₂₁ : Matrix (Fin n₂) (Fin m₁) R) (A₂₂ : Matrix (Fin n₂) (Fin m₂) R)
    (P' : Matrix (Fin n₂) (Fin n₂) R) :
    (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 0 P') *
        (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) =
      fromBlocks A₁₁ A₁₂ (P' * A₂₁) (P' * A₂₂) := by
  -- 直接套用通用的 fromBlocks 乘法公式
  simp [fromBlocks_multiply]

/--
**代数积木 2**: `(L_block * U_block)` 的分块形式。

左边的 `L_block` 是
\[
\begin{pmatrix}
  I   & 0 \\
  L₂₁ & L'
\end{pmatrix},
\]
右边的 `U_block` 是
\[
\begin{pmatrix}
  U₁₁ & U₁₂ \\
  0   & U'
\end{pmatrix}.
\]
结果是
\[
\begin{pmatrix}
  U₁₁             & U₁₂ \\
  L₂₁ U₁₁        & L₂₁ U₁₂ + L' U'
\end{pmatrix}.
\]
-/
lemma block_L_mul_U
    (L₂₁ : Matrix (Fin n₂) (Fin n₁) R) (L' : Matrix (Fin n₂) (Fin n₂) R)
    (U₁₁ : Matrix (Fin n₁) (Fin n₁) R) (U₁₂ : Matrix (Fin n₁) (Fin n₂) R)
    (U' : Matrix (Fin n₂) (Fin n₂) R) :
    (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 L₂₁ L') *
        (fromBlocks U₁₁ U₁₂ (0 : Matrix (Fin n₂) (Fin n₁) R) U') =
      fromBlocks U₁₁ U₁₂ (L₂₁ * U₁₁) (L₂₁ * U₁₂ + L' * U') := by
  -- 再次利用通用的 fromBlocks_multiply，交给 `simp` 处理 1 和 0 块
  simp [fromBlocks_multiply]

/--
**代数积木 3**: `(L_diag_block * U_block)` 的分块形式。

左边的 `L_diag_block` 是块对角矩阵
\[
\begin{pmatrix}
  I & 0 \\
  0 & L'
\end{pmatrix},
\]
右边的 `U_block` 是
\[
\begin{pmatrix}
  0 & U₁₂ \\
  0 & U'
\end{pmatrix}.
\]
结果是
\[
\begin{pmatrix}
  0 & U₁₂ \\
  0 & L' U'
\end{pmatrix}.
\]
-/
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

end MatDecompFormal.Components




-- import MatDecompFormal.Components.Properties.Triangular
-- import MatDecompFormal.Components.Properties.Permutation
-- import Mathlib.LinearAlgebra.Matrix.Block

-- namespace MatDecompFormal.Components

-- open Matrix MatDecompFormal.Components.Properties

-- /-!
-- # 分块矩阵代数库 (Block Matrix Algebra Library)

-- 本文件提供了一些**纯代数**的分块矩阵运算引理，全部在
-- `Matrix (Sum (Fin n₁) (Fin n₂)) (Sum (Fin m₁) (Fin m₂)) R` 的
-- 具体世界中工作。

-- 这些引理是后续 `Instances` 中 `lift_from_slice` 证明的“代数积木”，
-- 主要用于把矩阵方程拆成对块的等式。
-- -/

-- section BlockAlgebra

-- variable {n₁ n₂ m₁ m₂ : ℕ} {R : Type*} [CommRing R]

-- /-!
-- ## fromBlocks 与矩阵乘法

-- 这一节给出几条常用的分块乘法公式，形式都类似：

-- * `(fromBlocks ...) * (fromBlocks ...) = fromBlocks (...) (...) (...) (...)`
-- -/

-- /--
-- **代数积木 1**: `(P_block * A_block)` 的分块形式。

-- 左边的 `P_block` 是
-- \[
-- \begin{pmatrix}
--   I & 0 \\
--   0 & P'
-- \end{pmatrix},
-- \]
-- 右边是一般分块矩阵
-- \[
-- \begin{pmatrix}
--   A₁₁ & A₁₂ \\
--   A₂₁ & A₂₂
-- \end{pmatrix}.
-- \]
-- 结果是把右下两块左乘 `P'`。
-- -/
-- lemma block_P_mul_A
--     (A₁₁ : Matrix (Fin n₁) (Fin m₁) R) (A₁₂ : Matrix (Fin n₁) (Fin m₂) R)
--     (A₂₁ : Matrix (Fin n₂) (Fin m₁) R) (A₂₂ : Matrix (Fin n₂) (Fin m₂) R)
--     (P' : Matrix (Fin n₂) (Fin n₂) R) :
--     (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 0 P') *
--         (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) =
--       fromBlocks A₁₁ A₁₂ (P' * A₂₁) (P' * A₂₂) := by
--   -- 逐块证明：对 `i j` 分类讨论。
--   ext i j
--   cases i using Sum.rec <;>
--   cases j using Sum.rec <;>
--   simp [Matrix.fromBlocks, Matrix.mul_apply]
--   <;> rw [← Matrix.mul_apply]
--   <;> simp [Matrix.one_mul]

-- /--
-- **代数积木 2**: `(L_block * U_block)` 的分块形式。

-- 左边的 `L_block` 是
-- \[
-- \begin{pmatrix}
--   I   & 0 \\
--   L₂₁ & L'
-- \end{pmatrix},
-- \]
-- 右边的 `U_block` 是
-- \[
-- \begin{pmatrix}
--   U₁₁ & U₁₂ \\
--   0   & U'
-- \end{pmatrix}.
-- \]
-- 结果是
-- \[
-- \begin{pmatrix}
--   U₁₁             & U₁₂ \\
--   L₂₁ U₁₁        & L₂₁ U₁₂ + L' U'
-- \end{pmatrix}.
-- \]
-- -/
-- lemma block_L_mul_U
--     (L₂₁ : Matrix (Fin n₂) (Fin n₁) R) (L' : Matrix (Fin n₂) (Fin n₂) R)
--     (U₁₁ : Matrix (Fin n₁) (Fin n₁) R) (U₁₂ : Matrix (Fin n₁) (Fin n₂) R)
--     (U' : Matrix (Fin n₂) (Fin n₂) R) :
--     (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 L₂₁ L') *
--         (fromBlocks U₁₁ U₁₂ (0 : Matrix (Fin n₂) (Fin n₁) R) U') =
--       fromBlocks U₁₁ U₁₂ (L₂₁ * U₁₁) (L₂₁ * U₁₂ + L' * U') := by
--   -- 仍然对四种块情况逐一计算。
--   ext i j
--   cases i using Sum.rec <;>
--   cases j using Sum.rec <;>
--   simp [Matrix.fromBlocks, Matrix.mul_apply]
--   <;> rw [← Matrix.mul_apply]
--   <;> simp [Matrix.one_mul]

-- /--
-- **代数积木 3**: `(L_diag_block * U_block)` 的分块形式。

-- 左边的 `L_diag_block` 是块对角矩阵
-- \[
-- \begin{pmatrix}
--   I & 0 \\
--   0 & L'
-- \end{pmatrix},
-- \]
-- 右边的 `U_block` 是
-- \[
-- \begin{pmatrix}
--   0 & U₁₂ \\
--   0 & U'
-- \end{pmatrix}.
-- \]
-- 结果是
-- \[
-- \begin{pmatrix}
--   0 & U₁₂ \\
--   0 & L' U'
-- \end{pmatrix}.
-- \]
-- -/
-- lemma block_diag_L_mul_block_U
--     (L' : Matrix (Fin n₂) (Fin n₂) R)
--     (U₁₂ : Matrix (Fin n₁) (Fin n₂) R)
--     (U' : Matrix (Fin n₂) (Fin n₂) R) :
--     (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0
--                 (0 : Matrix (Fin n₂) (Fin n₁) R) L') *
--         (fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) U₁₂
--                     (0 : Matrix (Fin n₂) (Fin n₁) R) U') =
--       fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) U₁₂
--                  (0 : Matrix (Fin n₂) (Fin n₁) R) (L' * U') := by
--   -- 同样对四块分别计算。
--   ext i j
--   cases i using Sum.rec <;>
--   cases j using Sum.rec <;>
--   simp [Matrix.fromBlocks, Matrix.mul_apply]
--   rw [← Matrix.mul_apply]
--   simp [Matrix.one_mul]


-- end BlockAlgebra

-- end MatDecompFormal.Components







-- import MatDecompFormal.Components.Properties.Triangular
-- import MatDecompFormal.Components.Properties.Permutation
-- import Mathlib.Data.Sum.Order
-- import Mathlib.LinearAlgebra.Matrix.Block
-- import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

-- namespace MatDecompFormal.Components

-- open Matrix MatDecompFormal.Components.Properties

-- /-!
-- # 分块矩阵代数库 (Block Matrix Algebra Library)

-- 本文件提供了一套纯粹的代数引理，用于处理已被分块的矩阵
-- （即索引为 `Sum (Fin n₁) (Fin n₂)` 类型的矩阵）。

-- 这些引理是所有 `lift_from_slice` 证明的“代数积木”，它们被设计为
-- 在具体的 `Fin n` 世界中工作，以获得最大的简洁性和效率。
-- -/

-- -- ==================================================================
-- -- Section 1: Property-Preserving Lemmas for `fromBlocks`
-- -- ==================================================================

-- variable {n₁ n₂ m₁ m₂ : ℕ} {R : Type*} [CommRing R] [DecidableEq R]

-- /--
-- `fromBlocks` 构造的单位下三角矩阵的性质。
-- -/
-- lemma fromBlocks_isUnitLowerTriangular
--     (L₂₁ : Matrix (Fin n₂) (Fin n₁) R)
--     (L' : Matrix (Fin n₂) (Fin n₂) R) (hL' : IsUnitLowerTriangular L') :
--     IsUnitLowerTriangular (fromBlocks 1 0 L₂₁ L') := by
--   constructor
--   · -- 证明下三角性
--     dsimp [IsLowerTriangular, IsUpperTriangular]
--     rw [fromBlocks_transpose, BlockTriangular.fromBlocks_iff]
--     simp [hL'.1]
--   · -- 证明对角线为1
--     funext i
--     rcases i with (i₁ | i₂)
--     · simp [diag_apply, fromBlocks_apply₁₁, diag_one]
--     · simp [diag_apply, fromBlocks_apply₂₂, hL'.2]

-- /-- `fromBlocks` 构造的块对角置换矩阵的性质。 -/
-- lemma fromBlocks_isPermutation_iff_of_block_diag
--     (P₁₁ : Matrix (Fin n₁) (Fin n₁) R) (P₂₂ : Matrix (Fin n₂) (Fin n₂) R) :
--     IsPermutation (fromBlocks P₁₁ 0 0 P₂₂) ↔ IsPermutation P₁₁ ∧ IsPermutation P₂₂ := by
--   simp [IsPermutation, toMatrix_fromBlocks_diagonal]
--   constructor
--   · rintro ⟨σ, hσ⟩
--     have h_σ_maps_inl_to_inl : ∀ i, (σ (Sum.inl i)).isLeft := by
--       intro i; by_contra h_not_left
--       have h_inr : (σ (Sum.inl i)).isRight := Sum.isRight_iff_not_isLeft.mpr h_not_left
--       rcases Sum.isRight_iff.mp h_inr with ⟨i', hi'⟩; rw [hi'] at hσ
--       simp [fromBlocks_apply₂₁] at hσ
--     have h_σ_maps_inr_to_inr : ∀ i, (σ (Sum.inr i)).isRight := by
--       intro i; by_contra h_not_right
--       have h_inl : (σ (Sum.inr i)).isLeft := Sum.isLeft_iff_not_isRight.mpr h_not_right
--       rcases Sum.isLeft_iff.mp h_inl with ⟨i', hi'⟩; rw [hi'] at hσ
--       simp [fromBlocks_apply₁₂] at hσ
--     exact ⟨⟨Equiv.Perm.ofSumCompl σ h_σ_maps_inl_to_inl, by
--       ext i j; specialize hσ (Sum.inl i) (Sum.inl j); simpa using hσ⟩,
--       ⟨Equiv.Perm.ofSumCompl σ h_σ_maps_inr_to_inr, by
--       ext i j; specialize hσ (Sum.inr i) (Sum.inr j); simpa using hσ⟩⟩
--   · rintro ⟨⟨σ₁, h₁⟩, ⟨σ₂, h₂⟩⟩
--     use Equiv.Perm.sumCongr σ₁ σ₂
--     rw [h₁, h₂]

-- -- ==================================================================
-- -- Section 2: Algebraic Computation Lemmas for `fromBlocks`
-- -- ==================================================================

-- /--
-- **代数积木**: `(P_block * A_block)` 的分块形式。
-- -/
-- lemma block_P_mul_A
--     (A₁₁ : Matrix (Fin n₁) (Fin m₁) R) (A₁₂ : Matrix (Fin n₁) (Fin m₂) R)
--     (A₂₁ : Matrix (Fin n₂) (Fin m₁) R) (A₂₂ : Matrix (Fin n₂) (Fin m₂) R)
--     (P' : Matrix (Fin n₂) (Fin n₂) R) :
--     (fromBlocks 1 0 0 P') * (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) =
--     fromBlocks A₁₁ A₁₂ (P' * A₂₁) (P' * A₂₂) := by
--   simp [fromBlocks_multiply]

-- /--
-- **代数积木**: `(L_block * U_block)` 的分块形式。
-- -/
-- lemma block_L_mul_U
--     (L₂₁ : Matrix (Fin n₂) (Fin n₁) R) (L' : Matrix (Fin n₂) (Fin n₂) R)
--     (U₁₁ : Matrix (Fin n₁) (Fin n₁) R) (U₁₂ : Matrix (Fin n₁) (Fin n₂) R)
--     (U' : Matrix (Fin n₂) (Fin n₂) R) :
--     (fromBlocks 1 0 L₂₁ L') * (fromBlocks U₁₁ U₁₂ 0 U') =
--     fromBlocks U₁₁ U₁₂ (L₂₁ * U₁₁) (L₂₁ * U₁₂ + L' * U') := by
--   simp [fromBlocks_multiply]

-- /--
-- **代数积木**: `(L_diag_block * U_block)` 的分块形式。
-- -/
-- lemma block_diag_L_mul_block_U
--     (L' : Matrix (Fin n₂) (Fin n₂) R)
--     (U₁₂ : Matrix (Fin n₁) (Fin n₂) R)
--     (U' : Matrix (Fin n₂) (Fin n₂) R) :
--     (fromBlocks (1 : Matrix (Fin n₁) (Fin n₁) R) 0 0 L') *
--         (fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) U₁₂ (0 : Matrix (Fin n₂) (Fin n₁) R) U') =
--     fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) U₁₂ (0 : Matrix (Fin n₂) (Fin n₁) R) (L' * U') := by
--   simp [fromBlocks_multiply]

-- end MatDecompFormal.Components
