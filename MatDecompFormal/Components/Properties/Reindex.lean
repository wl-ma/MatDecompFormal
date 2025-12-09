import MatDecompFormal.Framework.FinEnum -- 假设 IsUpperTriangular 等定义已移入或可从此导入
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular

namespace MatDecompFormal.Components.Properties

open Matrix FinEnum MatDecompFormal.Framework

-- 我们将引理分为两部分：一部分只需要 Equiv，另一部分需要更强的 OrderIso

section EquivBased

variable {ι ι' R : Type*} [CommRing R] [DecidableEq ι] [DecidableEq ι']

lemma toMatrix_reindex_permCongr (e : ι ≃ ι') (σ : Equiv.Perm ι) :
    ((Equiv.toPEquiv σ).toMatrix : Matrix ι ι R).reindex e e =
      (Equiv.toPEquiv (e.permCongr σ)).toMatrix := by
  classical
  ext i j
  simp [Matrix.reindex_apply, PEquiv.toMatrix_apply, Equiv.permCongr_apply,
    Equiv.eq_symm_apply]

lemma isPermutation_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
    IsPermutation A ↔ IsPermutation (A.reindex e e) := by
  classical
  constructor
  · -- (→)
    intro hA; rcases hA with ⟨σ, rfl⟩
    dsimp [IsPermutation]
    refine ⟨e.permCongr σ, ?_⟩
    simpa [Matrix.reindex_apply] using toMatrix_reindex_permCongr (e:=e) (σ:=σ)
  · -- (←)
    intro hA_reindexed
    rcases hA_reindexed with ⟨σ, hσ⟩
    refine ⟨e.symm.permCongr σ, ?_⟩
    have h := congrArg (Matrix.reindex e.symm e.symm) hσ
    simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix,
      toMatrix_reindex_permCongr (e:=e.symm) σ] using h

end EquivBased

section

variable {ι ι' R : Type*}

lemma diag_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
    (A.reindex e e).diag = A.diag ∘ e.symm := by
  funext i'
  -- 展开两边 diag 的定义
  simp [diag, reindex_apply]

end


section OrderIsoBased

-- 对于序相关的性质，我们需要更强的 OrderIso 约束
variable {ι ι' R : Type*} [FinEnum ι] [FinEnum ι'] [Field R]

lemma isUpperTriangular_reindex (e : ι ≃o ι') (A : Matrix ι ι R) :
    IsUpperTriangular A ↔ IsUpperTriangular (A.reindex e.toEquiv e.toEquiv) := by
  simp [IsUpperTriangular]
  refine ⟨fun h i j h_lt ↦ ?_, fun h i j h_lt ↦ ?_⟩
  · -- (→)
    -- h_lt 是 j < i (在 ι' 中)
    -- 我们需要证明 (A.reindex e e) j i = 0
    -- reindex 后的值是 A (e.symm j) (e.symm i)
    -- 因为 e 是 OrderIso，e.symm 也是，所以 e.symm j < e.symm i
    have h_preimage_lt : e.symm j < e.symm i := (e.symm.lt_iff_lt).mpr h_lt
    -- 应用原始假设 h
    simpa using h h_preimage_lt
  · -- (←)
    -- h_lt 是 j < i (在 ι 中)
    -- 我们需要证明 A j i = 0
    -- A j i 可以写成 reindex 形式来应用新假设 h
    -- A j i = (A.reindex e e) (e j) (e i)
    -- 因为 e 是 OrderIso，所以 e j < e i
    have h_image_lt : e j < e i := (e.lt_iff_lt).mpr h_lt
    -- 应用新假设 h
    simpa [e.apply_symm_apply] using h h_image_lt

lemma isLowerTriangular_reindex (e : ι ≃o ι') (A : Matrix ι ι R) :
    IsLowerTriangular A ↔ IsLowerTriangular (A.reindex e.toEquiv e.toEquiv) := by
  dsimp [IsLowerTriangular]
  constructor
  · intro h
    have h' := (isUpperTriangular_reindex (e:=e) (A:=Aᵀ)).1 h
    simpa [Matrix.transpose_reindex] using h'
  · intro h
    have h' : IsUpperTriangular ((Aᵀ).reindex e.toEquiv e.toEquiv) := by
      simpa [Matrix.transpose_reindex] using h
    exact (isUpperTriangular_reindex (e:=e) (A:=Aᵀ)).2 h'

lemma isUnitLowerTriangular_reindex (e : ι ≃o ι') (A : Matrix ι ι R) :
    IsUnitLowerTriangular A ↔ IsUnitLowerTriangular (A.reindex e.toEquiv e.toEquiv) := by
  dsimp [IsUnitLowerTriangular]
  -- 分别处理 IsLowerTriangular 和 diag = 1 两个条件
  constructor
  · rintro ⟨hLT, hdiag⟩
    refine ⟨(isLowerTriangular_reindex (e:=e) (A:=A)).1 hLT, ?_⟩
    -- 主对角线上的值保持为 1
    ext i
    have := congrArg (fun f => f (e.symm i)) hdiag
    simpa [Matrix.diag] using this
  · rintro ⟨hLT, hdiag⟩
    refine ⟨(isLowerTriangular_reindex (e:=e) (A:=A)).2 hLT, ?_⟩
    ext i
    have := congrArg (fun f => f (e i)) hdiag
    simpa [Matrix.diag, Matrix.submatrix_apply] using this

end OrderIsoBased

end MatDecompFormal.Components.Properties
