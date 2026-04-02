import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Swap
import MatDecompFormal.Abstractions.MatrixProperty

namespace MatDecompFormal.Components.Properties

open Matrix
open MatDecompFormal.Abstractions

/-!
# 置换矩阵属性 (Permutation Matrix Property)

本文件定义了 `IsPermutation` 属性，并证明了其基本性质。
一个矩阵是置换矩阵，如果它等价于某个 `Equiv.Perm` 的矩阵表示。

设计要点：
- 核心性质仅依赖于 `[Fintype ι]` 和 `[DecidableEq ι]`，以获得最大的通用性
  并避免类型类实例冲突。
-/

section IsPermutation

variable {ι R : Type*} [CommRing R] [DecidableEq ι]

/--
`IsPermutation A` 是一个谓词，判断矩阵 `A` 是否为一个置换矩阵。
-/
def IsPermutation (A : Matrix ι ι R) : Prop :=
  ∃ (σ : Equiv.Perm ι), A = (Equiv.toPEquiv σ).toMatrix

/--
由 `Equiv.swap` 构造的行（列）交换矩阵是一个置换矩阵。
-/
lemma isPermutation_swap (i j : ι) : IsPermutation (swap R i j) := by
  dsimp [IsPermutation]
  use (Equiv.swap i j)
  -- `swap R i j` is definitionally equal to `(Equiv.toPEquiv (Equiv.swap i j)).toMatrix`
  -- in Mathlib.LinearAlgebra.Matrix.Swap
  rfl

/--
置换矩阵的集合在矩阵乘法下是封闭的。
约束从 `FinEnum` 放宽到了 `Fintype`，以避免实例钻石问题。
-/
@[simp]
lemma isPermutation_mul {A B : Matrix ι ι R} [Fintype ι]
    (hA : IsPermutation A) (hB : IsPermutation B) : IsPermutation (A * B) := by
  rcases hA with ⟨σA, rfl⟩
  rcases hB with ⟨σB, rfl⟩
  dsimp [IsPermutation]
  -- The permutation corresponding to A * B is σB * σA (note the order).
  refine ⟨σB * σA, ?_⟩
  have hmul :
      ((Equiv.toPEquiv σA).toMatrix : Matrix ι ι R) *
          (Equiv.toPEquiv σB).toMatrix =
        (Equiv.toPEquiv (σA.trans σB)).toMatrix := by
    simpa [Equiv.toPEquiv_trans] using
      (PEquiv.toMatrix_trans (Equiv.toPEquiv σA) (Equiv.toPEquiv σB)).symm
  have hcomp : σA.trans σB = σB * σA := by
    ext i
    simp [Equiv.trans_apply, Equiv.Perm.mul_def]
  simpa [hcomp] using hmul


end IsPermutation


-- ==================================================================
-- 为 IsPermutation 提供 MatrixGroup 实例
-- ==================================================================
section MatrixGroupInstance

variable {n : ℕ} {R : Type*} [CommRing R]

/--
`IsPermutation` 构成一个矩阵群。
-/
noncomputable instance : MatrixGroup (IsPermutation (R := R) (ι := Fin n)) where
  mul_closed := isPermutation_mul
  one_mem := by
    dsimp [IsPermutation]
    use Equiv.refl (Fin n)
    -- `1` is definitionally `(Equiv.toPEquiv (Equiv.refl _)).toMatrix`
    simp [PEquiv.toMatrix_refl]
  inv_closed := by
    intro A hA
    rcases hA with ⟨σ, rfl⟩
    dsimp [IsPermutation]
    use σ.symm
    refine inv_eq_left_inv ?_
    simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  invertible := by
    intro A hA
    rcases hA with ⟨σ, rfl⟩
    -- Any permutation matrix is a unit.
    refine
      ⟨⟨(Equiv.toPEquiv σ).toMatrix, (Equiv.toPEquiv σ.symm).toMatrix, ?_, ?_⟩, rfl⟩
    <;> simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]

end MatrixGroupInstance
-- ==================================================================


/-!
## `fromBlocks` 与置换矩阵结构

这一小节刻画 **块对角矩阵** 何时是置换矩阵：

\[
  \begin{pmatrix}
    P₁₁ & 0 \\
    0   & P₂₂
  \end{pmatrix}
\]
是置换矩阵，当且仅当 `P₁₁` 与 `P₂₂` 分别都是置换矩阵。
-/

section BlockFromBlocks

variable {n₁ n₂ : ℕ} {R : Type*} [CommRing R] [NeZero (1 : R)]
-- The index type is a sum type, which is Fintype and DecidableEq.
local notation "ι" => Fin n₁ ⊕ Fin n₂

/--
块对角矩阵 `fromBlocks P₁₁ 0 0 P₂₂` 是置换矩阵，
当且仅当两个对角块 `P₁₁` 和 `P₂₂` 都是置换矩阵。

索引类型是 `Sum (Fin n₁) (Fin n₂)`。
-/
lemma isPermutation_fromBlocks_blockDiag_iff
    (P₁₁ : Matrix (Fin n₁) (Fin n₁) R)
    (P₂₂ : Matrix (Fin n₂) (Fin n₂) R) :
    IsPermutation (fromBlocks P₁₁ 0 0 P₂₂) ↔
      IsPermutation P₁₁ ∧ IsPermutation P₂₂ := by
  classical
  -- `IsPermutation` is “there exists a permutation σ such that P = toMatrix σ”.
  -- We leverage the block-diagonal shape to force σ to preserve the blocks,
  -- and then recover the permutations on each block.
  constructor
  · -- → Direction: If the block matrix is a permutation, then each block is.
    intro h
    rcases h with ⟨σ, hσ⟩
    -- ① σ must map indices from the left block back to the left block.
    -- Otherwise, a 1 would appear in the off-diagonal blocks, contradicting the zeros.
    have h_σ_maps_inl_to_inl :
        ∀ i : Fin n₁, ∃ j, σ (Sum.inl i) = Sum.inl j := by
      intro i
      cases hσimage : σ (Sum.inl i) with
      | inl j => exact ⟨j, rfl⟩
      | inr j =>
          -- At entry (inl i, inr j), `toMatrix σ` is 1, while `fromBlocks` is 0.
          have hentry :=
            congrArg (fun M => M (Sum.inl i) (Sum.inr j)) hσ
          simp [Matrix.fromBlocks, PEquiv.toMatrix_apply, hσimage] at hentry
    have h_σ_maps_inr_to_inr :
        ∀ i : Fin n₂, ∃ j, σ (Sum.inr i) = Sum.inr j := by
      intro i
      cases hσimage : σ (Sum.inr i) with
      | inl j =>
          have hentry := congr_fun (congr_fun hσ (Sum.inr i)) (Sum.inl j)
          simp [Matrix.fromBlocks, PEquiv.toMatrix_apply, hσimage] at hentry
      | inr j => exact ⟨j, rfl⟩

    -- ② Thus, σ is in the range of `sumCongrHom`. We can extract the block permutations.
    have hMapsTo : Set.MapsTo (fun x : ι => σ x) (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro _ ⟨i, rfl⟩
      rcases h_σ_maps_inl_to_inl i with ⟨j, hj⟩
      exact ⟨j, hj.symm⟩
    have hRange :
        σ ∈ (Equiv.Perm.sumCongrHom (Fin n₁) (Fin n₂)).range :=
      Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hMapsTo
    rcases
        (Equiv.Perm.sumCongrHom (Fin n₁) (Fin n₂)).mem_range.mp hRange with
        ⟨⟨σ₁, σ₂⟩, hσsum⟩

    -- ③ Read the matrix equations from the diagonal blocks.
    refine ⟨?hP₁₁, ?hP₂₂⟩
    · -- Left block
      use σ₁
      have hσ' :
          fromBlocks P₁₁ 0 0 P₂₂ =
            (Equiv.toPEquiv ((Equiv.Perm.sumCongrHom (Fin n₁) (Fin n₂)) (σ₁, σ₂))).toMatrix := by
        simpa [hσsum] using hσ
      have hσ'' :
          fromBlocks P₁₁ 0 0 P₂₂ =
            (Equiv.toPEquiv (Equiv.sumCongr σ₁ σ₂)).toMatrix := by
        simpa [Equiv.Perm.sumCongrHom] using hσ'
      ext i j
      have hentry := congr_fun (congr_fun hσ'' (Sum.inl i)) (Sum.inl j)
      simpa [Matrix.fromBlocks, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply] using hentry
    · -- Right block
      use σ₂
      have hσ' :
          fromBlocks P₁₁ 0 0 P₂₂ =
            (Equiv.toPEquiv ((Equiv.Perm.sumCongrHom (Fin n₁) (Fin n₂)) (σ₁, σ₂))).toMatrix := by
        simpa [hσsum] using hσ
      have hσ'' :
          fromBlocks P₁₁ 0 0 P₂₂ =
            (Equiv.toPEquiv (Equiv.sumCongr σ₁ σ₂)).toMatrix := by
        simpa [Equiv.Perm.sumCongrHom] using hσ'
      ext i j
      have hentry := congr_fun (congr_fun hσ'' (Sum.inr i)) (Sum.inr j)
      simpa [Matrix.fromBlocks, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply] using hentry

  · -- ← Direction: If both blocks are permutations, the block-diagonal matrix is.
    rintro ⟨⟨σ₁, h₁⟩, ⟨σ₂, h₂⟩⟩
    -- Combine them using the sum of permutations.
    use (Equiv.Perm.sumCongr σ₁ σ₂)
    -- Verify the equality block by block.
    ext i j
    all_goals
      cases i using Sum.rec <;>
      cases j using Sum.rec <;>
      simp [Matrix.fromBlocks, h₁, h₂, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply,
        eq_comm]

end BlockFromBlocks


end MatDecompFormal.Components.Properties
