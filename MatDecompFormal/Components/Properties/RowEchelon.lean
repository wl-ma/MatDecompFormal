import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Order.Basic
import MatDecompFormal.Framework.FinEnum


namespace MatDecompFormal.Components.Properties

open FinEnum Matrix MatDecompFormal.Framework

/-!
# 行阶梯形属性 (Row Echelon Form Property)

本文件定义了矩阵的“行阶梯形” (`IsRowEchelon`) 属性。这个定义是通用的，
适用于行和列索引为任何可枚举有限类型 (`FinEnum`) 的矩阵。

### 核心概念
1.  **`NonZeroIndex` (主元索引)**:
    这是一个辅助函数，用于查找给定行中第一个非零元素（即主元）的列索引。
    如果某行为全零行，则其主元索引为 `⊤` (无穷大)。

2.  **`IsRowEchelon` (行阶梯形)**:
    一个矩阵被称为行阶梯形，如果它满足以下两个条件：
    a. **主元单调性**: 对于任意两行 `i₁` 和 `i₂`，如果 `i₁` 在 `i₂` 之上，
       那么 `i₁` 的主元必须在 `i₂` 的主元的左侧。
    b. **零行位置**: 所有全零行都必须位于所有非零行的下方。
       (注意：这个条件被我们的主元单调性定义所蕴含，因为 `⊤` 被认为是
       最大的主元索引。)

这个文件专注于**定义**该属性。关于此属性如何在具体分解（如高斯消元）中
保持或被构造的引理，属于 `Instances` 层的证明，而非此处的定义。
-/

section NonZeroIndex

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Zero R] [DecidableEq R]

/--
`NonZeroIndex A i` 计算矩阵 `A` 的第 `i` 行中第一个非零元素的列索引。

为了在通用的 `FinEnum` 类型 `κ` 上实现查找，我们利用 `κ` 与 `Fin (card κ)`
的等价关系，在 `Fin` 类型上执行 `Fin.find`，然后将结果映射回 `κ`。

*   `A`: 输入矩阵。
*   `i`: 行索引。
*   **返回**: `WithTop κ` 类型的值。如果找到主元，则为 `some j`；
    如果该行为全零行，则为 `⊤` (即 `none`)。
-/
noncomputable def NonZeroIndex (A : Matrix ι κ R) (i : ι) : WithTop κ :=
  let finEnum_κ : FinEnum κ := inferInstance
  let eκ : κ ≃ Fin (FinEnum.card κ) := finEnum_κ.equiv
  let row_vec : Fin (card κ) → R := fun j ↦ A i (eκ.symm j)
  let find_result : WithTop (Fin (card κ)) := Fin.find (fun j ↦ row_vec j ≠ 0)
  find_result.map eκ.symm

namespace NonZeroIndex

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Zero R] [DecidableEq R] (A : Matrix ι κ R)

lemma eq_top_iff {i} : NonZeroIndex A i = ⊤ ↔ ∀ j, A i j = 0 := by
  dsimp [NonZeroIndex]
  rw [WithTop.map_eq_top_iff, Fin.find_eq_top_iff]
  exact Equiv.forall_congr' (equiv κ).symm (fun j ↦ by simp)

lemma ne_top_iff {i} : NonZeroIndex A i ≠ ⊤ ↔ ∃ j, NonZeroIndex A i = some j :=
  WithTop.ne_top_iff_exists

lemma eq_some_iff {i} {j₀} :
    NonZeroIndex A i = some j₀ ↔ (∀ j, (@equiv κ) j < (@equiv κ) j₀ → A i j = 0) ∧ A i j₀ ≠ 0 := by
  dsimp [NonZeroIndex]
  rw [WithTop.map_eq_some_iff]
  use (equiv κ j₀)
  simp_rw [Fin.find_eq_some_iff, (equiv κ).apply_symm_apply]
  -- 证明 (∀ j, (equiv κ) j < (equiv κ) j₀ → ...) 等价于 (∀ j', j' < (equiv κ) j₀ → ...)
  apply Iff.intro
  · intro h j' hj'
    exact h.1 ((equiv κ).symm j') (by rwa [← (equiv κ).symm.lt_iff_lt])
  · intro h
    constructor
    · intro j hj
      exact h.1 (equiv κ j) (by rwa [(equiv κ).lt_iff_lt])
    · exact h.2

end NonZeroIndex

end NonZeroIndex

section IsRowEchelon

variable {ι κ R : Type*} [FinEnum ι] [FinEnum κ] [Zero R] [DecidableEq R]

noncomputable local instance : LinearOrder ι := LinearOrder.ofFinEnum ι
noncomputable local instance : LinearOrder κ := LinearOrder.ofFinEnum κ

/--
`IsRowEchelon` 是一个谓词，用于判断一个矩阵是否为行阶梯形。

它要求对于任意两行 `i₁ < i₂`，如果 `i₂` 不是全零行，那么 `i₁` 的主元
必须严格位于 `i₂` 的主元的左侧。这个定义自动蕴含了所有全零行
（其主元为 `⊤`）都位于非零行（其主元为 `some j`）的下方。
-/
@[mk_iff]
structure IsRowEchelon (A : Matrix ι κ R) : Prop where
  /-- 主元索引在 `Fin` 空间中随行索引严格单调增加。 -/
  pivot_strict_mono :
    ∀ {i₁ i₂ : ι}, (@equiv ι) i₁ < (@equiv ι) i₂ → NonZeroIndex A i₂ ≠ ⊤ →
    WithTop.map (@equiv κ) (NonZeroIndex A i₁) < WithTop.map (@equiv κ) (NonZeroIndex A i₂)

end IsRowEchelon

end MatDecompFormal.Components.Properties














-- import Mathlib

-- section Matrix.IsRowEchelon

-- open List

-- variable {m n : ℕ}
-- variable {α} [DecidableEq α] [Zero α] (M : Matrix (Fin n) (Fin m) α)

-- def Matrix.NonZeroIndex : Fin n → WithTop (Fin m) := fun i ↦
--     Fin.find (fun j => M i j ≠ 0)

-- namespace Matrix.NonZeroIndex

-- lemma eq_top {i} : (M.NonZeroIndex i = ⊤) ↔ ∀ j, M i j = 0 := by
--   show (M.NonZeroIndex i = none) ↔ ∀ j, M i j = 0
--   simp [NonZeroIndex]
--   rw [Fin.find_eq_none_iff]
--   simp

-- lemma ne_top_iff (i) : M.NonZeroIndex i ≠ ⊤ ↔
--   ∃ j, M.NonZeroIndex i = some j := by
--   show M.NonZeroIndex i ≠ none ↔ _
--   rw [Option.ne_none_iff_exists']

-- lemma ne_top_iff' (i) : M.NonZeroIndex i ≠ ⊤ ↔
--   ∃ j, M.NonZeroIndex i = WithTop.some j := by
--   show M.NonZeroIndex i ≠ none ↔ ∃ j, M.NonZeroIndex i = some j
--   rw [Option.ne_none_iff_exists']

-- lemma eq_some_iff (i j) : M.NonZeroIndex i = some j ↔ (∀ k < j, M i k = 0) ∧ M i j ≠ 0:= by
--   rw [NonZeroIndex, Fin.find_eq_some_iff]
--   constructor
--   · intro hx
--     refine ⟨?_, hx.1⟩
--     by_contra!
--     rcases this with ⟨k, hk, hm⟩
--     exact Nat.lt_le_asymm hk (hx.2 k hm)
--   intro hx
--   refine ⟨hx.2, ?_⟩
--   by_contra!
--   rcases this with ⟨k, hk, hm⟩
--   exact hk (hx.1 k hm)

-- lemma eq_some_iff' (i j) : M.NonZeroIndex i = WithTop.some j ↔ (∀ k < j, M i k = 0) ∧ M i j ≠ 0:= by
--   show M.NonZeroIndex i = some j ↔ (∀ k < j, M i k = 0) ∧ M i j ≠ 0
--   rw [eq_some_iff]

-- variable {l o p q}

-- /--
-- Auxiliary lemma for `submatrix_nonZeroIndex_map` handling the case where
-- the submatrix has a non-zero index equal to `⊤` (all zeros in the row).
-- -/
-- lemma submatrix_nonZeroIndex_map_top_case {s t} [DecidableEq R] [Zero R]
--     (A : Matrix l o R) (f : Fin m → l) (g : Fin n → o) (i : Fin m)
--     (p : Fin s → l) (q : Fin t → o) (uh : Fin m → Prop) (hi : uh i)
--     (u : {x : Fin m // uh x} → Fin s) (h : Fin t → Fin n)
--     (hjk : (∀ (j : Fin t), A (p (u ⟨i, hi⟩)) (q j) = 0) → ∀ (j : Fin n), A (p (u ⟨i, hi⟩)) (g j) = 0)
--     (hpq : (A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩) = ⊤)
--     (hpu : p (u ⟨i, hi⟩) = f i) :
--     (A.submatrix f g).NonZeroIndex i = WithTop.map h ((A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩)) := by
--   simp [hpq]
--   simp [eq_top] at *
--   rw [← hpu]
--   apply hjk hpq

-- lemma submatrix_nonZeroIndex_map_finite_case {s t} [DecidableEq R] [Zero R]
--     (A : Matrix l o R) (f : Fin m → l) (g : Fin n → o) (i : Fin m)
--     (p : Fin s → l) (q : Fin t → o) (uh : Fin m → Prop) (hi : uh i)
--     (u : {x : Fin m // uh x} → Fin s) (h : Fin t → Fin n)
--     (hpq : (A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩) ≠ ⊤)
--     (hkj : (j : Fin t) → (∀ k < j, A (p (u ⟨i, hi⟩)) (q k) = 0) → ∀ k < h j, A (p (u ⟨i, hi⟩)) (g k) = 0)
--     (hpu : p (u ⟨i, hi⟩) = f i) (hgh : g ∘ h = q) :
--     (A.submatrix f g).NonZeroIndex i = WithTop.map h ((A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩)) := by
--   change _ ≠ ⊤ at hpq
--   rw [ne_top_iff] at hpq
--   rcases hpq with ⟨j, hj⟩
--   simp only [hj]
--   show _ = some (h j)
--   rw [eq_some_iff] at *
--   refine ⟨?_, ?_⟩
--   · simp only [← hpu, submatrix_apply]
--     simp at hj
--     apply hkj j hj.1
--   simp only [← hpu, submatrix_apply]
--   simp at hj
--   show A ((p ∘ u) ⟨i, hi⟩) ((g ∘ h) j) ≠ 0
--   rw [hgh]
--   apply hj.2

-- /--
-- Main theorem relating non-zero indices of submatrices under index mapping.

-- Given a matrix `A`, index mappings `f, g, p, q, u, h` with appropriate conditions,
-- shows that the non-zero index of the submatrix `A.submatrix f g` at row `i`
-- is obtained by mapping the non-zero index of `A.submatrix p q` at row `u ⟨i, hi⟩`
-- through the function `h`.

-- This handles both cases (⊤ and finite indices) by delegating to auxiliary lemmas.
-- -/
-- lemma submatrix_nonZeroIndex_map {s t} [DecidableEq R] [Zero R] (A : Matrix l o R) (f : Fin m → l)
--     (g : Fin n → o) (i : Fin m)
--     (p : Fin s → l) (q : Fin t → o) (uh : Fin m → Prop) (hi : uh i)
--     (u : {x : Fin m // uh x} → Fin s) (h : Fin t → Fin n)
--     (hjk : (∀ (j : Fin t), A (p (u ⟨i, hi⟩)) (q j) = 0) → ∀ (j : Fin n), A (p (u ⟨i, hi⟩)) (g j) = 0)
--     (hkj : (j : Fin t) → (∀ k < j, A (p (u ⟨i, hi⟩)) (q k) = 0) → ∀ k < h j, A (p (u ⟨i, hi⟩)) (g k) = 0)
--     (hpu : p (u ⟨i, hi⟩) = f i) (hgh : g ∘ h = q) :
--     (A.submatrix f g).NonZeroIndex i = WithTop.map h ((A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩)) := by
--   by_cases hpq : (A.submatrix p q).NonZeroIndex (u ⟨i, hi⟩) = ⊤
--   · exact submatrix_nonZeroIndex_map_top_case A f g i p q uh hi u h hjk hpq hpu
--   exact submatrix_nonZeroIndex_map_finite_case A f g i p q uh hi u h hpq hkj hpu hgh

-- /--
-- Simplified version of `submatrix_nonZeroIndex_map` where the predicate `uh`
-- is trivial (always true), making the index mapping `u` simpler to use.
-- -/
-- lemma submatrix_nonZeroIndex_map_simple {s t} [DecidableEq R] [Zero R] (A : Matrix l o R)
--     (f : Fin m → l) (g : Fin n → o) (i : Fin m)
--     (p : Fin s → l) (q : Fin t → o)
--     (u : Fin m → Fin s) (h : Fin t → Fin n)
--     (hjk : (∀ (j : Fin t), A (p (u i)) (q j) = 0) → ∀ (j : Fin n), A (p (u i)) (g j) = 0)
--     (hkj : (j : Fin t) → (∀ k < j, A (p (u i)) (q k) = 0) → ∀ k < h j, A (p (u i)) (g k) = 0)
--     (hpu : p (u i) = f i) (hgh : g ∘ h = q) :
--     (A.submatrix f g).NonZeroIndex i = WithTop.map h ((A.submatrix p q).NonZeroIndex (u i)) := by
--   apply submatrix_nonZeroIndex_map A f  g i p q  (fun _ ↦ True) (by simp) (fun x ↦ ⟨u x, by simp⟩) h hjk hkj hpu hgh

-- lemma submatrix_nonZeroIndex_map_simple_fin {s t} [DecidableEq R] [Zero R]
--     (A : Matrix (Fin s) (Fin t) R) (f : Fin m ≃ Fin s) (g : Fin n ≃ Fin t) (i : Fin m)
--     (hg : ∀ x y, x < y → g x < g y) :
--     (A.submatrix f g).NonZeroIndex i = WithTop.map g.2 (A.NonZeroIndex (f i)) := by
--     apply submatrix_nonZeroIndex_map_simple
--     · intro hj j
--       apply hj (g j)
--     · intro j hkj k hk
--       apply hkj
--       rw [← g.4 j]
--       apply hg _ _ hk
--     · rfl
--     · funext
--       simp

-- lemma fromBlocks_reindex_nonZeroIndex_left {i : Fin (n + o)} (A : Matrix (Fin n) (Fin l) α)
--     (B : Matrix (Fin n) (Fin m) α) (C : Matrix (Fin o) (Fin l) α)
--     (D : Matrix (Fin o) (Fin m) α) (hi : i < n)
--     (ha : A.NonZeroIndex ⟨i, hi⟩ ≠ ⊤) :
--     ((fromBlocks A B C D).reindex finSumFinEquiv finSumFinEquiv).NonZeroIndex i =
--     WithTop.map (Fin.castAdd m) (A.NonZeroIndex ⟨i, hi⟩) := by
--     apply submatrix_nonZeroIndex_map_finite_case  (fromBlocks A B C D) finSumFinEquiv.symm finSumFinEquiv.symm i Sum.inl Sum.inl (fun j ↦ j < n) hi (fun j ↦ ⟨j.1, j.2⟩)
--     · simp only [submatrix, fromBlocks_apply₁₁]
--       show A.NonZeroIndex _ ≠ ⊤
--       apply ha
--     · intro j hkj k hk
--       have hk' : k.1 < l := by
--         rw [← Fin.val_fin_lt] at hk
--         apply lt_trans hk
--         simp only [Fin.coe_castAdd, Fin.is_lt]
--       simp [finSumFinEquiv_symm_apply_left hk', fromBlocks_apply₁₁]
--       apply hkj _   hk
--     · simp [finSumFinEquiv, Fin.addCases, hi, Fin.castLT]
--     · funext i
--       simp

-- lemma fromBlocks_lowerTriangular_reindex_nonZeroIndex {i : Fin (n + o)} (A : Matrix (Fin n) (Fin l) α)
--     (B : Matrix (Fin n) (Fin m) α) (D : Matrix (Fin o) (Fin m) α)
--     (hi : n ≤ i) : ((fromBlocks A B 0 D).reindex finSumFinEquiv finSumFinEquiv).NonZeroIndex i =
--     WithTop.map (Fin.natAdd l) (D.NonZeroIndex (Fin.natSub o i hi)) := by
--     apply submatrix_nonZeroIndex_map (fromBlocks A B 0 D) finSumFinEquiv.symm finSumFinEquiv.symm i Sum.inr Sum.inr
--       (fun j ↦ n ≤ j) hi (fun j ↦ (Fin.natSub o j.1 j.2)) (Fin.natAdd l)
--     · intro hj j
--       match (finSumFinEquiv.symm j) with
--       | Sum.inr u => simp only [hj]
--       | Sum.inl v => simp only [fromBlocks_apply₂₁, zero_apply]
--     · intro j hj k hk
--       match hkf : (finSumFinEquiv.symm k) with
--       | Sum.inr u =>
--         simp at *
--         apply hj
--         simp [finSumFinEquiv, Fin.addCases] at hkf
--         by_cases hkl : k < l
--         · simp [hkl] at hkf
--         simp [hkl, Fin.subNat] at hkf
--         simpa [← hkf] using Fin.mk_lt_of_lt_val <| Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hkl) hk
--       | Sum.inl v => simp only [fromBlocks_apply₂₁, zero_apply]
--     · have : ¬ n > i := Nat.not_lt.mpr hi
--       simp [finSumFinEquiv, Fin.addCases, this, Fin.natSub, Fin.subNat]
--     · funext i
--       simp only [Function.comp_apply, finSumFinEquiv_symm_apply_natAdd]

-- lemma preserved_under_injective_columns {r j}
--   {A : Matrix (Fin m) (Fin n) α} (f : Fin r → Fin m) (g : Fin o ≃ Fin n)
--   (hg : ∀ x y, x < y → g.2 x < g.2 y) (hA : (A.submatrix f g.1).NonZeroIndex j ≠ ⊤) :
--   A.NonZeroIndex (f j) ≠ ⊤ := by
--   simp [ne_top_iff', eq_some_iff'] at *
--   rcases hA with ⟨w, hw⟩
--   use (g w)
--   refine ⟨?_, hw.2⟩
--   intro k hk
--   have : g.invFun k < w := by
--     rw [← g.3 w]
--     apply hg _ _ hk
--   have := (hw.1 (g.2 k) this )
--   simp at this
--   apply this

-- end Matrix.NonZeroIndex

-- open Matrix.NonZeroIndex

-- @[class, mk_iff]
-- structure Matrix.IsRowEchelon : Prop where
--   pivot_right_move :
--     ∀ (i j), i < j → M.NonZeroIndex j ≠ ⊤ → M.NonZeroIndex i < M.NonZeroIndex j

-- lemma Matrix.IsRowEchelon.lt_of_lt (i j : Fin n) (u v : Fin m)
--     (hi : M.NonZeroIndex i = WithTop.some u) (hj : M.NonZeroIndex j = WithTop.some v)
--     (huv : u < v) :
--     M.NonZeroIndex i < M.NonZeroIndex j := by
--   simpa [hi, hj]

-- def Matrix.IsRowEchelonable [CommRing R]
--   (x : Matrix (Fin m) (Fin n) R) : Prop :=
--   ∃ P : GL (Fin m) R , (P.1 * x).IsRowEchelon

-- def MatObj.IsRowEchelonable [CommRing R] (x : MatObj R) : Prop :=
--   x.A.IsRowEchelonable

-- lemma submatrix_eq {m' n'} [Zero R] (x : Matrix (Fin m) (Fin n) R)
--   (hm : m' = m) (hn : n' = n) (i : Fin m') :
--   WithTop.map (finCongr hn.symm) (x.NonZeroIndex ((finCongr hm) i)) =
--     (x.submatrix (finCongr hm) (finCongr hn)).NonZeroIndex i := by
--   by_cases h : x.NonZeroIndex ((finCongr hm) i) = ⊤
--   · simp_rw [h, WithTop.map_top]
--     rw [eq_top] at h
--     symm
--     rw [eq_top]
--     intro j
--     apply h ((finCongr hn) j)
--   have : x.NonZeroIndex ((finCongr hm) i) ≠ ⊤ := h
--   rw [ne_top_iff] at this
--   rcases this with ⟨j, hj⟩
--   simp_rw [hj, WithTop.map, Option.map]
--   rw [eq_some_iff] at hj
--   symm
--   simp_rw [eq_some_iff, submatrix_apply, finCongr_apply,
--     Fin.cast_trans, Fin.cast_eq_self, ne_eq]
--   refine ⟨?_,hj.2⟩
--   have := hj.1
--   simp only [finCongr_apply] at this
--   intro k hk
--   apply this _ hk

-- lemma Matrix.IsRowEchelon.submatrix {m' n'} [Zero R] (x : Matrix (Fin m) (Fin n) R) (hx : x.IsRowEchelon)
--   (hm : m' = m) (hn : n' = n) : (x.submatrix (finCongr hm) (finCongr hn)).IsRowEchelon := by
--   simp [Matrix.isRowEchelon_iff]
--   intro i j hij
--   rw [← submatrix_eq x hm hn i, ← submatrix_eq x hm hn j]
--   intro h
--   show WithTop.map (Fin.castOrderIso hn.symm) _ < WithTop.map (Fin.castOrderIso hn.symm) _
--   apply WithTop.equiv_lt (Fin.castOrderIso hn.symm)
--   apply hx.1 ((finCongr hm) i) ((finCongr hm) j) hij (ne_of_apply_ne _ h)

-- lemma IsRowEchelonable.trans [CommRing R] : Transport (X := MatObj R) MatrixRel.IsRowEquiv MatObj.IsRowEchelonable := by
--   simp [Transport, MatObj.IsRowEchelonable, Matrix.IsRowEchelonable]
--   intro x y hxy P hP
--   have ⟨Q, hQ⟩:= hxy.2
--   use ((GeneralLinearGroup.reindex R (finCongr hxy.1.1)).1 P) * Q
--   simp [Units.val_mul, Matrix.mul_assoc, hQ, Matrix.GeneralLinearGroup.reindex, MatObj.SameSize.reindex]
--   apply Matrix.IsRowEchelon.submatrix _ hP


-- lemma isRowEchelonable_reindex_of_order_preserving {l o} [CommRing R] {A : Matrix (Fin m) (Fin n) R}
--   (hA : A.IsRowEchelonable) (f : Fin m ≃ Fin l) (g : Fin n ≃ Fin o)
--   (hf : ∀ x y, x < y → f.2 x < f.2 y) (hg1 : ∀ x y, x < y → g.1 x < g.1 y)
--   (hg2 : ∀ x y, x < y → g.2 x < g.2 y) :
--   (A.reindex f g).IsRowEchelonable := by
--   have ⟨P, hP⟩ := hA
--   use Matrix.GeneralLinearGroup.reindex R f P
--   simp [GeneralLinearGroup.reindex, Matrix.isRowEchelon_iff]
--   simp [Matrix.isRowEchelon_iff] at hP
--   intro i j hij ht
--   have hgi := Matrix.NonZeroIndex.submatrix_nonZeroIndex_map_simple_fin (P.1 * A) f.symm g.symm i hg2
--   have hgj := Matrix.NonZeroIndex.submatrix_nonZeroIndex_map_simple_fin (P.1 * A) f.symm g.symm j hg2
--   rw [hgi, hgj]
--   apply WithTop.map_lt_of_lt _ hg1
--   apply hP (f.2 i) (f.2 j) (hf _ _ hij)
--   · simp [hgj]at ht
--     exact ht

-- end Matrix.IsRowEchelon
