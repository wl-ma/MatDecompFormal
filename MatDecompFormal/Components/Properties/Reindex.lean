import MatDecompFormal.Framework.FinEnum
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Diagonal

namespace MatDecompFormal.Components.Properties

open Matrix FinEnum --MatDecompFormal.Framework

/-!
# Reindex 与矩阵性质

本文件收集各种关于 `Matrix.reindex` 的“性质保持”引理，包括：

* 置换矩阵 (`IsPermutation`)
* 对角线 (`diag`)
* 上三角 / 下三角 / 单位下三角 (`IsUpperTriangular`, `IsLowerTriangular`,
  `IsUnitLowerTriangular`)

并且在 `FinEnum` 场景下，给出了新版 `IsUpperTriangular` 与旧式
`BlockTriangular A (@equiv ι _)` 定义之间的等价关系。
-/


-- 我们将引理分为两部分：一部分只需要 Equiv，另一部分需要更强的 OrderIso

section EquivBased

variable {ι ι' R : Type*} [CommRing R] [DecidableEq ι] [DecidableEq ι']

/--
对置换矩阵 `(Equiv.toPEquiv σ).toMatrix` 做 `reindex e e`，
等价于对置换做 `permCongr` 后再取矩阵。
-/
lemma toMatrix_reindex_permCongr (e : ι ≃ ι') (σ : Equiv.Perm ι) :
    ((Equiv.toPEquiv σ).toMatrix : Matrix ι ι R).reindex e e =
      (Equiv.toPEquiv (e.permCongr σ)).toMatrix := by
  classical
  ext i j
  simp [Matrix.reindex_apply, PEquiv.toMatrix_apply,
    Equiv.permCongr_apply, Equiv.eq_symm_apply]

/--
`IsPermutation` 在 `reindex e e` 下保持。
-/
lemma isPermutation_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
    IsPermutation A ↔ IsPermutation (A.reindex e e) := by
  classical
  constructor
  · -- (→)
    intro hA; rcases hA with ⟨σ, rfl⟩
    dsimp [IsPermutation]
    refine ⟨e.permCongr σ, ?_⟩
    simpa using
      toMatrix_reindex_permCongr (e := e) (σ := σ)
  · -- (←)
    intro hA_reindexed
    rcases hA_reindexed with ⟨σ, hσ⟩
    refine ⟨e.symm.permCongr σ, ?_⟩
    -- 对等式两边再 reindex 回来
    have h := congrArg (Matrix.reindex e.symm e.symm) hσ
    -- 左边收缩为 A，右边用前一个引理（此时等价是 e.symm）
    -- `Matrix.reindex_apply` + `Equiv.symm_apply_apply` 保证 reindex 再 reindex 回原矩阵。
    simpa [Matrix.reindex_apply,
      toMatrix_reindex_permCongr (e := e.symm) (σ := σ)] using h

end EquivBased



/-!
## 对角线与 reindex
-/

section

variable {ι ι' R : Type*}

/--
`reindex` 后的对角线是“原对角线复合 `e.symm`”。
-/
lemma diag_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
    (A.reindex e e).diag = A.diag ∘ e.symm := by
  funext i'
  -- 展开 diag 和 reindex
  simp [Matrix.diag, Matrix.reindex_apply, Function.comp]

end



/-!
## 上/下三角与 OrderIso 下的 reindex
-/

section OrderPropertyBased

-- 对于序相关的性质，我们分离 Equiv 和序保持的假设
variable {ι ι' R : Type*} [LinearOrder ι] [Preorder ι'] [Zero R]

/--
在一个保持严格单调的 `Equiv` 诱导的基变换下，上三角性保持。
-/
lemma isUpperTriangular_reindex (e : ι ≃ ι') (h_mono : StrictMono e) (A : Matrix ι ι R) :
    IsUpperTriangular A ↔ IsUpperTriangular (A.reindex e e) := by
  dsimp [IsUpperTriangular, BlockTriangular]
  constructor
  · intro h i' j' h_lt
    -- `StrictMono` implies `Monotone`; use it to reflect the order through `e.symm`.
    have h_preimage_lt : e.symm j' < e.symm i' := by
      -- `StrictMono.lt_iff_lt` lets us pull back `<` along `e`.
      have h_lt' : e (e.symm j') < e (e.symm i') := by
        simpa using h_lt
      exact (h_mono.lt_iff_lt).1 h_lt'
    simpa [Matrix.reindex_apply] using h h_preimage_lt
  · intro h i j h_lt
    have h_image_lt : e j < e i := h_mono h_lt
    simpa [Matrix.reindex_apply] using h h_image_lt

/--
在一个保持严格单调的 `Equiv` 诱导的基变换下，下三角性保持。
-/
lemma isLowerTriangular_reindex (e : ι ≃ ι') (h_mono : StrictMono e) (A : Matrix ι ι R) :
    IsLowerTriangular A ↔ IsLowerTriangular (A.reindex e e) := by
  dsimp [IsLowerTriangular]
  have h := isUpperTriangular_reindex (e := e) (h_mono := h_mono) (A := Aᵀ)
  simpa [IsLowerTriangular, Matrix.transpose_reindex] using h

/--
在一个保持严格单调的 `Equiv` 诱导的基变换下，单位下三角性保持。
-/
lemma isUnitLowerTriangular_reindex (e : ι ≃ ι') (h_mono : StrictMono e)
    (A : Matrix ι ι R) [One R] : --[DecidableEq ι] [DecidableEq ι'] :
    IsUnitLowerTriangular A ↔ IsUnitLowerTriangular (A.reindex e e) := by
  dsimp [IsUnitLowerTriangular]
  -- We need to prove `IsLowerTriangular` and `diag` properties are preserved.
  constructor
  · rintro ⟨hLT, hdiag⟩
    refine ⟨(isLowerTriangular_reindex (e := e) (h_mono := h_mono) (A := A)).1 hLT, ?_⟩
    -- diagonal entries remain `1` after reindexing
    funext i
    have hdiag_eval : A.diag (e.symm i) = 1 := by
      have := congrArg (fun f => f (e.symm i)) hdiag
      simpa using this
    simpa [diag_reindex, Function.comp] using hdiag_eval
  · rintro ⟨hLT, hdiag⟩
    refine ⟨(isLowerTriangular_reindex (e := e) (h_mono := h_mono) (A := A)).2 hLT, ?_⟩
    funext i
    have h := congrArg (fun f => f (e i)) hdiag
    -- unfold the diagonal of the reindexed matrix
    simpa [diag_reindex, Function.comp] using h

end OrderPropertyBased



/-!
## 在 FinEnum 场景下，新旧上三角定义的等价性

旧设计中，上三角性被定义为 `BlockTriangular A (@equiv ι _)`，其中
`equiv : ι ≃ Fin (card ι)` 是 `FinEnum` 提供的规范枚举；新设计直接在
索引类型自身的 `LinearOrder` 上使用 `BlockTriangular A id`。

下面的引理说明两者在 `FinEnum` 场景下是等价的。
-/

section FinEnumCompat

variable {ι R : Type*} [FinEnum ι] [Zero R]

/--
在 `FinEnum` 场景下，新定义的 `IsUpperTriangular` 等价于旧式
`BlockTriangular A (@equiv ι _)`（使用 `FinEnum.equiv` 作为分块函数）。
-/
lemma isUpperTriangular_iff_blockTriangular_equiv (A : Matrix ι ι R) :
    IsUpperTriangular A ↔ BlockTriangular A (@equiv ι _) := by
  classical
  -- e : ι ≃o Fin (card ι)
  let e := MatDecompFormal.Framework.orderIsoOfFinEnum ι
  -- 新定义：IsUpperTriangular A = BlockTriangular A (fun i => i)
  dsimp [IsUpperTriangular]
  -- 先证明：用 id 和用 e 的结果等价
  have h :
      BlockTriangular A (fun i : ι => i) ↔
        BlockTriangular A (fun i : ι => e i) := by
    constructor
    · intro hBT i j hlt
      -- e.lt_iff_lt 把 e j < e i 转成 j < i
      have hlt' : j < i := (e.lt_iff_lt).mp hlt
      exact hBT hlt'
    · intro hBT i j hlt
      -- 反向同理
      have hlt' : e j < e i := (e.lt_iff_lt).mpr hlt
      exact hBT hlt'
  -- 再注意：e.toEquiv = equiv（在 Framework.FinEnum 中就是这么定义的）
  have heq : (fun i : ι => e i) = (fun i : ι => (@equiv ι _) i) := by
    funext i; rfl
  -- 用 heq 把 BlockTriangular 的分块函数改写成 (@equiv ι _)
  simpa [heq] using h

end FinEnumCompat

end MatDecompFormal.Components.Properties







-- import MatDecompFormal.Framework.FinEnum -- 假设 IsUpperTriangular 等定义已移入或可从此导入
-- import MatDecompFormal.Components.Properties.Permutation
-- import MatDecompFormal.Components.Properties.Triangular

-- namespace MatDecompFormal.Components.Properties

-- open Matrix FinEnum MatDecompFormal.Framework

-- -- 我们将引理分为两部分：一部分只需要 Equiv，另一部分需要更强的 OrderIso

-- section EquivBased

-- variable {ι ι' R : Type*} [CommRing R] [DecidableEq ι] [DecidableEq ι']

-- lemma toMatrix_reindex_permCongr (e : ι ≃ ι') (σ : Equiv.Perm ι) :
--     ((Equiv.toPEquiv σ).toMatrix : Matrix ι ι R).reindex e e =
--       (Equiv.toPEquiv (e.permCongr σ)).toMatrix := by
--   classical
--   ext i j
--   simp [Matrix.reindex_apply, PEquiv.toMatrix_apply, Equiv.permCongr_apply,
--     Equiv.eq_symm_apply]

-- lemma isPermutation_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
--     IsPermutation A ↔ IsPermutation (A.reindex e e) := by
--   classical
--   constructor
--   · -- (→)
--     intro hA; rcases hA with ⟨σ, rfl⟩
--     dsimp [IsPermutation]
--     refine ⟨e.permCongr σ, ?_⟩
--     simpa [Matrix.reindex_apply] using toMatrix_reindex_permCongr (e:=e) (σ:=σ)
--   · -- (←)
--     intro hA_reindexed
--     rcases hA_reindexed with ⟨σ, hσ⟩
--     refine ⟨e.symm.permCongr σ, ?_⟩
--     have h := congrArg (Matrix.reindex e.symm e.symm) hσ
--     simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix,
--       toMatrix_reindex_permCongr (e:=e.symm) σ] using h

-- end EquivBased

-- section

-- variable {ι ι' R : Type*}

-- lemma diag_reindex (e : ι ≃ ι') (A : Matrix ι ι R) :
--     (A.reindex e e).diag = A.diag ∘ e.symm := by
--   funext i'
--   -- 展开两边 diag 的定义
--   simp [diag, reindex_apply]

-- end


-- section OrderIsoBased

-- -- 对于序相关的性质，我们需要更强的 OrderIso 约束
-- variable {ι ι' R : Type*} [FinEnum ι] [FinEnum ι'] [Field R]

-- lemma isUpperTriangular_reindex (e : ι ≃o ι') (A : Matrix ι ι R) :
--     IsUpperTriangular A ↔ IsUpperTriangular (A.reindex e.toEquiv e.toEquiv) := by
--   simp [IsUpperTriangular]
--   refine ⟨fun h i j h_lt ↦ ?_, fun h i j h_lt ↦ ?_⟩
--   · -- (→)
--     -- h_lt 是 j < i (在 ι' 中)
--     -- 我们需要证明 (A.reindex e e) j i = 0
--     -- reindex 后的值是 A (e.symm j) (e.symm i)
--     -- 因为 e 是 OrderIso，e.symm 也是，所以 e.symm j < e.symm i
--     have h_preimage_lt : e.symm j < e.symm i := (e.symm.lt_iff_lt).mpr h_lt
--     -- 应用原始假设 h
--     simpa using h h_preimage_lt
--   · -- (←)
--     -- h_lt 是 j < i (在 ι 中)
--     -- 我们需要证明 A j i = 0
--     -- A j i 可以写成 reindex 形式来应用新假设 h
--     -- A j i = (A.reindex e e) (e j) (e i)
--     -- 因为 e 是 OrderIso，所以 e j < e i
--     have h_image_lt : e j < e i := (e.lt_iff_lt).mpr h_lt
--     -- 应用新假设 h
--     simpa [e.apply_symm_apply] using h h_image_lt

-- lemma isLowerTriangular_reindex (e : ι ≃o ι') (A : Matrix ι ι R) :
--     IsLowerTriangular A ↔ IsLowerTriangular (A.reindex e.toEquiv e.toEquiv) := by
--   dsimp [IsLowerTriangular]
--   constructor
--   · intro h
--     have h' := (isUpperTriangular_reindex (e:=e) (A:=Aᵀ)).1 h
--     simpa [Matrix.transpose_reindex] using h'
--   · intro h
--     have h' : IsUpperTriangular ((Aᵀ).reindex e.toEquiv e.toEquiv) := by
--       simpa [Matrix.transpose_reindex] using h
--     exact (isUpperTriangular_reindex (e:=e) (A:=Aᵀ)).2 h'

-- lemma isUnitLowerTriangular_reindex (e : ι ≃o ι') (A : Matrix ι ι R) :
--     IsUnitLowerTriangular A ↔ IsUnitLowerTriangular (A.reindex e.toEquiv e.toEquiv) := by
--   dsimp [IsUnitLowerTriangular]
--   -- 分别处理 IsLowerTriangular 和 diag = 1 两个条件
--   constructor
--   · rintro ⟨hLT, hdiag⟩
--     refine ⟨(isLowerTriangular_reindex (e:=e) (A:=A)).1 hLT, ?_⟩
--     -- 主对角线上的值保持为 1
--     ext i
--     have := congrArg (fun f => f (e.symm i)) hdiag
--     simpa [Matrix.diag] using this
--   · rintro ⟨hLT, hdiag⟩
--     refine ⟨(isLowerTriangular_reindex (e:=e) (A:=A)).2 hLT, ?_⟩
--     ext i
--     have := congrArg (fun f => f (e i)) hdiag
--     simpa [Matrix.diag, Matrix.submatrix_apply] using this

-- end OrderIsoBased

-- end MatDecompFormal.Components.Properties
