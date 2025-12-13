import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Swap

namespace MatDecompFormal.Components.Properties

open Matrix

/-!
# 置换矩阵属性 (Permutation Matrix Property)

本文件定义了 `IsPermutation` 属性，并证明了其基本性质。
一个矩阵是置换矩阵，如果它等价于某个 `Equiv.Perm` 的矩阵表示。
-/

section IsPermutation

variable {ι R : Type*} [CommRing R]

/--
`IsPermutation A` 是一个谓词，判断矩阵 `A` 是否为一个置换矩阵。
-/
def IsPermutation [DecidableEq ι] (A : Matrix ι ι R) : Prop :=
  ∃ (σ : Equiv.Perm ι), A = (Equiv.toPEquiv σ).toMatrix

/--
由 `Equiv.swap` 构造的行（列）交换矩阵是一个置换矩阵。
-/
lemma isPermutation_swap [DecidableEq ι] (i j : ι) : IsPermutation (swap R i j) := by
  dsimp [IsPermutation]
  use (Equiv.swap i j)
  rfl

/--
置换矩阵的集合在矩阵乘法下是封闭的。
-/
@[simp]
lemma isPermutation_mul {A B : Matrix ι ι R} [FinEnum ι]
    (hA : IsPermutation A) (hB : IsPermutation B) : IsPermutation (A * B) := by
  rcases hA with ⟨σA, rfl⟩
  rcases hB with ⟨σB, rfl⟩
  dsimp [IsPermutation]
  use (σB * σA)
  rw [← PEquiv.toMatrix_trans, Equiv.Perm.mul_def, Equiv.toPEquiv_trans]


end IsPermutation



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
  -- `IsPermutation` 是“存在一个置换 σ，使得 P = toMatrix σ”
  -- 我们利用 block-diag 的形状强迫 σ 保持左右块不交叉，
  -- 然后在各自块上恢复出置换。
  constructor
  · -- → 方向：块对角是置换 ⇒ 两个块都是置换
    intro h
    rcases h with ⟨σ, hσ⟩
    -- ① σ 必须把左块的索引映射回左块，否则上右或下左块会出现 1，与 0 冲突
    have h_σ_maps_inl_to_inl :
        ∀ i : Fin n₁, ∃ j, σ (Sum.inl i) = Sum.inl j := by
      intro i
      cases hσimage : σ (Sum.inl i) with
      | inl j => exact ⟨j, rfl⟩
      | inr j =>
          -- 在 (inl i, inr j) 处，`toMatrix σ` 给出 1，而 fromBlocks 给出 0
          have hentry := congrArg (fun M => M (Sum.inl i) (Sum.inr j)) hσ
          have h01 : (0 : R) = 1 := by
            simp [Matrix.fromBlocks, hσimage] at hentry
          exact (one_ne_zero h01.symm).elim
    have h_σ_maps_inr_to_inr :
        ∀ i : Fin n₂, ∃ j, σ (Sum.inr i) = Sum.inr j := by
      intro i
      cases hσimage : σ (Sum.inr i) with
      | inl j =>
          have hentry := congrArg (fun M => M (Sum.inr i) (Sum.inl j)) hσ
          have h01 : (0 : R) = 1 := by
            simp [Matrix.fromBlocks, hσimage] at hentry
          exact (one_ne_zero h01.symm).elim
      | inr j => exact ⟨j, rfl⟩

    -- ② 于是 σ 属于 `sumCongrHom` 的像，提取左右块的置换
    have hMapsTo : Set.MapsTo (fun x : ι => σ x) (Set.range Sum.inl) (Set.range Sum.inl) := by
      intro x hx
      rcases hx with ⟨i, rfl⟩
      rcases h_σ_maps_inl_to_inl i with ⟨j, hj⟩
      exact ⟨j, hj.symm⟩
    have hRange :
        σ ∈ (Equiv.Perm.sumCongrHom (Fin n₁) (Fin n₂)).range :=
      Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl (σ := σ) hMapsTo
    rcases
        (Equiv.Perm.sumCongrHom (Fin n₁) (Fin n₂)).mem_range.mp hRange with
        ⟨⟨σ₁, σ₂⟩, hσsum⟩

    -- ③ 分别从左上、右下块读取矩阵等式
    refine ⟨?hP₁₁, ?hP₂₂⟩
    · -- 左块
      refine ⟨σ₁, ?_⟩
      have hσ' :
          fromBlocks P₁₁ 0 0 P₂₂ =
            (Equiv.toPEquiv (Equiv.sumCongr σ₁ σ₂)).toMatrix := by
        simpa [hσsum.symm] using hσ
      ext i j
      have hentry := congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hσ'
      simpa [Matrix.fromBlocks, PEquiv.toMatrix_toPEquiv_apply] using hentry
    · -- 右块
      refine ⟨σ₂, ?_⟩
      have hσ' :
          fromBlocks P₁₁ 0 0 P₂₂ =
            (Equiv.toPEquiv (Equiv.sumCongr σ₁ σ₂)).toMatrix := by
        simpa [hσsum.symm] using hσ
      ext i j
      have hentry := congrArg (fun M => M (Sum.inr i) (Sum.inr j)) hσ'
      simpa [Matrix.fromBlocks, PEquiv.toMatrix_toPEquiv_apply] using hentry

  · -- ← 方向：两个块都是置换 ⇒ 块对角是置换
    rintro ⟨⟨σ₁, h₁⟩, ⟨σ₂, h₂⟩⟩
    -- 用和式上的积置换来拼起来
    refine ⟨Equiv.Perm.sumCongr σ₁ σ₂, ?_⟩
    -- 逐块比对等式即可
    ext i j
    all_goals
      cases i using Sum.rec <;>
      cases j using Sum.rec <;>
      simp [Matrix.fromBlocks, h₁, h₂, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply,
        eq_comm]

end BlockFromBlocks

end MatDecompFormal.Components.Properties
