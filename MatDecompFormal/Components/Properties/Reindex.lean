import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Abstractions.Schema


open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties
open Matrix FinEnum

namespace MatDecompFormal.Components.Properties

variable {ι ι' R : Type*} [FinEnum ι] [FinEnum ι'] [Field R] [DecidableEq R]

-- ------------------------------------------------------------------
-- 步骤 1: 证明基础性质在 reindex 下保持不变
-- ------------------------------------------------------------------

lemma isPermutation_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
    IsPermutation A ↔ IsPermutation (A.reindex e e) := by
  constructor
  · intro hA; rcases hA with ⟨σ, rfl⟩
    -- simp [IsPermutation]
    use e.permCongr σ
    simp [reindex_apply]
    ext i j
    simp [PEquiv.toMatrix_apply, Equiv.permCongr_apply]
    simp [Equiv.eq_symm_apply]
  · simp
    intro hA_reindexed
    sorry
    -- rcases hA_reindexed with ⟨σ', rfl⟩
    -- let σ := e.permCongr (σ'.permCongr e.symm)
    -- use σ
    -- rw [← reindex_inj e.injective e.injective, reindex_reindex]
    -- simp

lemma isUpperTriangular_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
    IsUpperTriangular A ↔ IsUpperTriangular (A.reindex e e) := by
  -- 关键：e 是一个 OrderIso，它保持序关系
  dsimp [IsUpperTriangular]
  sorry
  -- rw [reindex_blockTriangular_iff e]

lemma isLowerTriangular_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
    IsLowerTriangular A ↔ IsLowerTriangular (A.reindex e e) := by
  dsimp [IsLowerTriangular]
  sorry
  -- rw [transpose_reindex, isUpperTriangular_reindex e]

lemma diag_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
    (A.reindex e e).diag = A.diag ∘ e.symm := by
  funext i'; sorry--rw [diag_apply, reindex_apply, e.apply_symm_apply, diag_apply]

lemma isUnitLowerTriangular_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
    IsUnitLowerTriangular A ↔ IsUnitLowerTriangular (A.reindex e e) := by
  dsimp [IsUnitLowerTriangular]
  rw [isLowerTriangular_reindex e]
  -- 处理对角线
  constructor
  · intro h; sorry--rw [diag_reindex, h.2, Function.comp_const_right]
  · intro h; rw [← Function.comp_id (A.diag), ← e.symm_comp_self]
    sorry
    -- rw [Function.comp.assoc, diag_reindex.symm, h.2, Function.comp_const_right]


end MatDecompFormal.Components.Properties
