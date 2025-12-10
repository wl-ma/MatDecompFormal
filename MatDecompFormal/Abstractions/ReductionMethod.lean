import Mathlib.Data.FinEnum
import MatDecompFormal.Framework.Universe -- 假设 Universe.lean 提供了必要的类型

namespace MatDecompFormal.Abstractions

/-!
# 规约方法 (Reduction Method) - v2.1 (Corrected)

本文件定义了 `ReductionMethod` 结构体，它封装了归纳证明中与“问题规约”
相关的纯代数部分。一个规约方法描述了：

1.  **何时可以规约 (`IsSliceable`)**: 一个矩阵需要满足什么条件才能被“切片”。
2.  **如何规约 (`slice`)**: 如何从一个可切片的矩阵中提取出一个“更小”的子问题。
3.  **如何重构 (`reconstruct`)**: 一个纯粹的代数函数，它知道如何从一个子矩阵
    （以及原始矩阵的其余部分）重新组装出完整的矩阵。
4.  **重构的正确性 (`reconstruct_slice_eq`)**: 一个关键的代数恒等式，证明
    `reconstruct` 和 `slice` 在某种意义上是互逆的。

这个结构体是完全“代数的”，它不关心要证明的最终性质 `P` 是什么。它只提供
可复用的、用于分解和重组矩阵的机械装置。
-/

/--
`ReductionMethod` 封装了一种将矩阵问题分解为更小问题并从子问题解重构的代数策略。

*   `ι`, `κ`, `R`: 原始矩阵的索引类型和环类型。
*   `Sliceι`, `Sliceκ`: 子问题（切片）矩阵的索引类型。
*   `IsSliceable`: 描述一个 `Matrix ι κ R` 何时可以被切片。
*   `slice`: 从可切片矩阵中提取 `Matrix Sliceι Sliceκ R` 类型的子问题。
*   `reconstruct`: 一个代数重构函数。它接收原始的可切片矩阵 `A`（用于获取
    除子矩阵外的其他部分，如左上角元素）和一个“已解决的”子矩阵 `slice_sol`，
    然后返回一个重构后的完整矩阵。
*   `reconstruct_slice_eq`: 一个关键的正确性证明，确保如果我们用原始的切片
    去重构，我们能得到原始的矩阵。
-/
structure ReductionMethod (ι κ R : Type*) [FinEnum ι] [FinEnum κ] [CommRing R] where
  /-- 子问题矩阵的行索引类型。 -/
  Sliceι : Type*
  /-- 子问题矩阵的列索引类型。 -/
  Sliceκ : Type*
  [finEnum_slice_ι : FinEnum Sliceι]
  [finEnum_slice_κ : FinEnum Sliceκ]

  /-- 一个谓词，用于判断一个矩阵是否处于可以被“切片”的“标准型”。 -/
  IsSliceable : Matrix ι κ R → Prop

  /-- “切片”算子，从一个可切片的矩阵中提取出更小的子问题。 -/
  slice : (A : Matrix ι κ R) → (hA : IsSliceable A) → Matrix Sliceι Sliceκ R

  /--
  “重构”函数：从原始矩阵的上下文和子矩阵的解来组装一个完整的矩阵。
  -/
  reconstruct : (A : Matrix ι κ R) → (hA : IsSliceable A) →
                (slice_sol : Matrix Sliceι Sliceκ R) → Matrix ι κ R

  /--
  重构的正确性证明：用原始切片进行重构会得到原始矩阵。
  这是 `lift_from_slice` 引理的代数基础。
  -/
  reconstruct_slice_eq : ∀ (A : Matrix ι κ R) (hA : IsSliceable A),
                           reconstruct A hA (slice A hA) = A

-- 自动为 Sliceι 和 Sliceκ 注册 FinEnum 实例
attribute [instance] ReductionMethod.finEnum_slice_ι
attribute [instance] ReductionMethod.finEnum_slice_κ

end MatDecompFormal.Abstractions








-- import Mathlib.Data.FinEnum
-- import Mathlib.LinearAlgebra.Matrix.Basis


-- namespace MatDecompFormal.Abstractions

-- /-!
-- # 规约方法 (Reduction Method)

-- 本文件定义了 `ReductionMethod` 结构体，它封装了归纳证明中与“问题规约”
-- 相关的纯代数部分。一个规约方法描述了：

-- 1.  **何时可以规约 (`IsSliceable`)**: 一个矩阵需要满足什么条件才能被“切片”。
-- 2.  **如何规约 (`slice`)**: 如何从一个可切片的矩阵中提取出一个“更小”的子问题。
-- 3.  **如何重构 (`reconstruct`)**: 一个纯粹的代数函数，它知道如何从一个子矩阵
--     （以及原始矩阵的其余部分）重新组装出完整的矩阵。

-- 这个结构体是完全“代数的”，它不关心要证明的最终性质 `P` 是什么。它只提供
-- 可复用的、用于分解和重组矩阵的机械装置。
-- -/


-- /--
-- `MatrixProperty R` 是一个**类型**，它代表一个“跨尺寸的矩阵性质家族”。

-- 一个 `MatrixProperty` 的实例 `P` 是一个函数，你可以给它提供任意的索引类型
-- `ι` 和 `κ`，它会返回一个针对 `Matrix ι κ R` 的性质（即一个 `Prop`）。
-- 例如，`IsRowEchelon` 就是一个 `MatrixProperty`。

-- 通过将这个概念封装成一个类型，我们避免了在 `ReductionMethod` 的定义中
-- 出现复杂的嵌套多态，从而解决了类型检查器的宇宙变量推断问题。
-- -/
-- def MatrixProperty (R : Type*) :=
--   (ι κ : Type*) → [FinEnum ι] → [FinEnum κ] → Matrix ι κ R → Prop


-- /--
-- `ReductionMethod` 封装了一种将矩阵问题分解为更小问题并从子问题解重构的代数策略。

-- *   `ι`, `κ`, `R`: 原始矩阵的索引类型和环类型。
-- *   `Sliceι`, `Sliceκ`: 子问题（切片）矩阵的索引类型。
-- *   `IsSliceable`: 描述一个 `Matrix ι κ R` 何时可以被切片。
-- *   `slice`: 从可切片矩阵中提取 `Matrix Sliceι Sliceκ R` 类型的子问题。
-- *   `reconstruct`: 一个代数重构函数。它接收原始的可切片矩阵 `A`（用于获取
--     除子矩阵外的其他部分，如左上角元素）和一个“已解决的”子矩阵 `slice_sol`，
--     然后返回一个重构后的完整矩阵。
-- *   `reconstruct_slice_eq`: 一个关键的正确性证明，确保如果我们用原始的切片
--     去重构，我们能得到原始的矩阵。
-- -/
-- structure ReductionMethod (ι κ R : Type*) [FinEnum ι] [FinEnum κ] [CommRing R] where
--   /-- 子问题矩阵的行索引类型。 -/
--   Sliceι : Type*
--   /-- 子问题矩阵的列索引类型。 -/
--   Sliceκ : Type*
--   finEnum_slice_ι : FinEnum Sliceι
--   finEnum_slice_κ : FinEnum Sliceκ

--   /-- 一个谓词，用于判断一个矩阵是否处于可以被“切片”的“标准型”。 -/
--   IsSliceable : Matrix ι κ R → Prop

--   /-- “切片”算子，从一个可切片的矩阵中提取出更小的子问题。 -/
--   slice : (A : Matrix ι κ R) → (hA : IsSliceable A) → Matrix Sliceι Sliceκ R

--   /--
--   “重构”函数：从原始矩阵的上下文和子矩阵的解来组装一个完整的矩阵。
--   -/
--   reconstruct : (A : Matrix ι κ R) → (hA : IsSliceable A) →
--                 (slice_sol : Matrix Sliceι Sliceκ R) → Matrix ι κ R

--   /--
--   重构的正确性证明：用原始切片进行重构会得到原始矩阵。
--   这是 `lift_from_slice` 引理的代数基础。
--   -/
--   reconstruct_slice_eq : ∀ (A : Matrix ι κ R) (hA : IsSliceable A),
--                            reconstruct A hA (slice A hA) = A

-- /--
-- 这个定义告诉 Lean，如何从一个 `ReductionMethod` 的实例中
-- 为它的 `Sliceι` 类型找到一个 `FinEnum` 实例。
-- -/
-- @[instance]
-- def ReductionMethod.instFinEnumSliceI {ι κ R} [FinEnum ι] [FinEnum κ] [CommRing R]
--     (m : ReductionMethod ι κ R) : FinEnum m.Sliceι :=
--   m.finEnum_slice_ι

-- /--
-- 同上，为 `Sliceκ` 类型找到 `FinEnum` 实例。
-- -/
-- @[instance]
-- def ReductionMethod.instFinEnumSliceK {ι κ R} [FinEnum ι] [FinEnum κ] [CommRing R]
--     (m : ReductionMethod ι κ R) : FinEnum m.Sliceκ :=
--   m.finEnum_slice_κ

-- end MatDecompFormal.Abstractions
















-- -- import Mathlib

-- -- variable {R : Type u}

-- -- section S_col_row_one_Ready

-- -- /-- Gauss 风格“可切片谓词”：“首列首行除第一个外为 0”。 -/
-- -- class S_col_row_one_Ready [Zero R] [One R] (x : MatObj R) : Prop where
-- --   hm : NeZero x.m
-- --   hn : NeZero x.n
-- --   hfm : ∀ i : Fin x.m, i.1 > 0 → x.A i 0 = 0
-- --   hfn : ∀ j : Fin x.n, j.1 > 0 → x.A 0 j = 0
-- --   -- h11 : x.A 0 0 = 1

-- -- namespace S_col_row_one_Ready

-- -- instance [Zero R] [One R] {x : MatObj R} [hx : S_col_row_one_Ready x]: NeZero x.m := hx.hm

-- -- instance [Zero R] [One R]{x : MatObj R} [hx :S_col_row_one_Ready x] : NeZero x.n := hx.hn


-- -- lemma S_col1Ready_prog [Zero R] :
-- --     SlicePro (X := MatObj R) MatObj.μ (fun x => MatObj.remove_first_row_and_col x.1) := by
-- --   intro x
-- --   have := x.2
-- --   simp [MatObj.μ] at  *
-- --   exact Nat.mul_lt_mul'' (by simp [this.1]) (by simp [this.2])

-- -- end S_col_row_one_Ready

-- -- end S_col_row_one_Ready

-- -- section lift
-- -- -- lift : Lift G μ slice
-- -- #check Lift

-- -- open MatObj
-- -- variable (R : Type)

-- -- /-- Equivalence between `Fin n` and the direct sum `Fin 1 ⊕ Fin (n-1)` when n > 0 -/
-- -- def finSplitEquiv {n} (hn : n > 0) : Fin n ≃ Fin 1 ⊕ Fin (n - 1) :=
-- --     (finCongr (m := 1 + (n - 1)) (add_sub_of_le hn).symm).trans finSumFinEquiv.symm

-- -- /-- Embed a smaller matrix into a larger one by adding a 1 in top-left corner and zeros elsewhere -/
-- -- @[simp]
-- -- def matrixEmbedding [Zero R]{n} (hn : n > 0)
-- --       (r : Matrix (Fin 1) (Fin 1) R)
-- --       (x : Matrix (Fin (n - 1)) (Fin (n - 1)) R) :
-- --      Matrix (Fin n) (Fin n) R :=
-- --   (fromBlocks r 0 0 x).submatrix (finSplitEquiv hn) (finSplitEquiv hn)

-- -- /-- Lift an invertible (n-1)×(n-1) matrix to an invertible n×n matrix -/
-- -- def invertibleLift [CommRing R] {n} (hn : n > 0)
-- --     (r : GL (Fin 1) R) (x : GL (Fin (n - 1)) R) : GL (Fin n) R where
-- --   val := matrixEmbedding R hn r.1 x.1
-- --   inv := matrixEmbedding R hn r.2 x.2
-- --   val_inv := by
-- --     simp only [matrixEmbedding, Units.inv_eq_val_inv, coe_units_inv, ---inv_subsingleton,
-- --       submatrix_mul_equiv, fromBlocks_multiply, Matrix.mul_zero, add_zero, Matrix.zero_mul,
-- --       isUnits_det_units, mul_nonsing_inv, zero_add, fromBlocks_one, submatrix_one_equiv]
-- --   inv_val := by
-- --     simp only [matrixEmbedding, Units.inv_eq_val_inv, coe_units_inv, ---inv_subsingleton,
-- --       submatrix_mul_equiv, fromBlocks_multiply, Matrix.mul_zero, add_zero, Matrix.zero_mul]
-- --     simp only [isUnits_det_units, nonsing_inv_mul, zero_add]
-- --     simp

-- -- instance [Zero R] {x : { x : MatObj R// MatObj.μ x > 0 }} : NeZero x.1.m := by
-- --   have := x.2
-- --   simp [μ] at this
-- --   exact NeZero.of_pos this.1

-- -- instance [Zero R] {x : { x : MatObj R// MatObj.μ x > 0 }} : NeZero x.1.n := by
-- --   have := x.2
-- --   simp [μ] at this
-- --   exact NeZero.of_pos this.2
-- -- @[simp]
-- -- lemma aux_aux [Ring R] : !![(1 : R)] = 1 := by
-- --   funext i j
-- --   rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
-- --   simp only [Fin.isValue, of_apply, cons_val',
-- --     cons_val_fin_one, one_apply_eq]

-- -- #check IsUnit
-- -- def aux [CommRing R] (r : Units R): GL (Fin 1) R where
-- --   val := !![r.1]
-- --   inv := !![r.2]
-- --   val_inv := by simp;
-- --   inv_val := by simp;

-- -- -- 左上角是0的话还得有一个permutation，保持I_r在左上角
-- -- -- 但是本质上这个是不应该证明的，因为我们做的过程中已经可以保证I_r在左上角
-- -- -- 需要思考

-- -- /-- Gaussian lifting operation that preserves matrix properties -/
-- -- noncomputable def GaussLift [CommRing R]:
-- --   Lift (R := R) (BiGL R) μ (fun x => remove_first_row_and_col x.1) :=
-- --   fun x hx =>
-- --     if hxa : IsUnit (x.1.A 0 0) then
-- --       ⟨invertibleLift R (Nat.pos_of_mul_pos_right x.2) 1 hx.1,
-- --            invertibleLift R (Nat.pos_of_mul_pos_left x.2) (aux R hxa.choose) hx.2⟩
-- --     else
-- --       ⟨invertibleLift R (Nat.pos_of_mul_pos_right x.2) 1 hx.1,
-- --            invertibleLift R (Nat.pos_of_mul_pos_left x.2) 1 hx.2⟩
-- -- end lift

-- -- section LiftSpec
-- -- open MatObj MatObjsize MatObjwithsize
-- -- -- (lspec : LiftSpec f μ Good slice lift)

-- -- variable (R : Type) [CommRing R]
-- -- -- 先构造消元算子！！！

-- -- theorem GaussliftSpec : LiftSpec (fma R) MatObj.μ S_col_row_one_Ready
-- --     (fun x ↦ MatObj.A x = rankStdBlock R (MatObjsize.m x.size) (MatObjsize.n x.size) (MatObj.A x).rank)
-- --     (fun x ↦ x.1.remove_first_row_and_col) (GaussLift R) := by
-- --   -- simp only [LiftSpec]

-- --   intro x g hs hg
-- --   by_cases hxa : IsUnit (x.1.A 0 0)
-- --   · simp [GaussLift, HSMul.hSMul, SMul.smul, hxa] at *
-- --     funext i j
-- --     by_cases hra : i < (A x.1).rank ∧ j < (A x.1).rank ∧ i = j.1
-- --     · simp [rankStdBlock, hra, invertibleLift, finSplitEquiv]
-- --       sorry

-- --     sorry
-- --   sorry


-- --   -- simp [GaussLift, HSMul.hSMul, SMul.smul] at hg


-- -- end LiftSpec
-- -- variable (R : Type) [CommRing R]

-- -- #check MatObj.equivSliceInduction_viaAction_exists_mat (fma R) MatObj.μ S_col_row_one_Ready
-- --   (fun x => MatObj.remove_first_row_and_col x.1)
-- --   (fun x => x.A = rankStdBlock R x.m x.n x.A.rank)
-- --   (GaussLift R) _

-- -- example : (a : Nat) → (b : Nat) → a + b = b + a :=
-- --   fun x y => Nat.add_comm x y
-- -- structure RingI where
-- --   t : Type
-- --   c : Ring t
-- -- noncomputable instance RingI_inst
-- --    {l}[Fintype l] : Ring (Matrix l l ℝ) := by
-- --   exact instRing

-- -- example {α} (a b c : α) [LT α]
-- --   (hab : a < b)(hbc : b < c) : a < c := by
-- --  sorry

-- --  open Matrix.NonZeroIndex MatrixSlice.S_col1Ready

-- -- section

-- -- variable [CommRing R] {x : MatObj R} (hx : S_col1Ready x)

-- -- /-- Given `m ≥ r`, constructs an equivalence between `Fin r ⊕ Fin (m - r)` and `Fin m`. -/
-- -- def finSumFinEquivOfLE {m r} (hm : m ≥ r) :
-- --     Fin r ⊕ Fin (m - r) ≃ Fin m := trans finSumFinEquiv <| finCongr <|  add_sub_of_le hm

-- -- /--
-- -- Given `[NeZero m] [NeZero n]`, constructs an equivalence between matrices indexed by
-- -- `Fin 1 ⊕ Fin (m-1) × Fin 1 ⊕ Fin (n-1)` and matrices indexed by `Fin m × Fin n`.
-- -- This is useful for decomposing matrices into blocks.
-- -- -/
-- -- noncomputable def Matrix.equivSumFin {m} [NeZero m] [NeZero n] :
-- --   Matrix (Fin 1 ⊕ Fin (m - 1)) (Fin 1 ⊕ Fin (n - 1)) R
-- --   ≃ Matrix (Fin m) (Fin n) R :=
-- --   reindex  (finSumFinEquivOfLE NeZero.one_le) (finSumFinEquivOfLE NeZero.one_le)

-- -- @[simp]
-- -- noncomputable def slice_botRight_aux (h : x.A 0 0 ≠ 0) :
-- --   Matrix (Fin 1 ⊕ Fin (slice_botRight hx).m) (Fin 1 ⊕ Fin (slice_botRight hx).n) R
-- --   ≃ Matrix (Fin x.m) (Fin x.n) R :=
-- --   reindex (trans finSumFinEquiv <| finCongr (slice_botRight_m_eq_one_add hx h).symm)
-- --     (trans finSumFinEquiv <| finCongr (one_add_slice_botRight_eq_sub_one hx))

-- -- @[simp]
-- -- noncomputable def MatObj.slice_botRight_upright :
-- --   Matrix (Fin 1) (Fin (slice_botRight hx).n) R :=
-- --   subUpRight <| x.A.submatrix (Fin.cast (add_sub_of_le NeZero.one_le)) (Fin.cast (one_add_slice_botRight_eq_sub_one _))

-- -- noncomputable def MatObj.slice_botRight_upright' :
-- --   Matrix (Fin 1) (Fin (x.n - 1)) R :=
-- --   subUpRight <| submatrix x.A (Fin.cast<|add_sub_of_le NeZero.one_le) (Fin.cast <| add_sub_of_le NeZero.one_le)

-- -- noncomputable def slice_botRight_aux_of_nezero (h : x.A 0 0 ≠ 0) :
-- --   Matrix (Fin (slice_botRight hx).m) (Fin (slice_botRight hx).n) R
-- --   ≃ Matrix (Fin (x.m - 1)) (Fin (x.n - 1)) R :=
-- --   reindex (finCongr (slice_botRight_m_eq_sub_one hx h))
-- --    (finCongr (slice_botRight_eq_sub_one hx))

-- -- lemma slice_botRight_equiv_reconstruction' (h : x.A 0 0 ≠ 0) :
-- --   equivSumFin.2 x.A =
-- --   (fromBlocks !![x.A 0 0] (x.slice_botRight_upright' hx) 0
-- --      ((slice_botRight_aux_of_nezero hx h) (slice_botRight hx).A))  := by
-- --   funext i j
-- --   match i, j with
-- --   | Sum.inl u, Sum.inl v => simp [Fin.fin_one_eq_zero]; rfl
-- --   | Sum.inl u, Sum.inr v => simp; rfl
-- --   | Sum.inr u, Sum.inl v =>
-- --     simp [Fin.fin_one_eq_zero];
-- --     apply hx.3
-- --     simp [finSumFinEquivOfLE]
-- --   | Sum.inr u, Sum.inr v =>
-- --     simp [slice_botRight_def_A_ne_zero hx ⟨h⟩, MatObj.SameSize.reindex]
-- --     rfl

-- -- lemma slice_botRight_equiv_reconstruction (h : x.A 0 0 ≠ 0) :
-- --    x.A = equivSumFin.1
-- --   (fromBlocks !![x.A 0 0] (x.slice_botRight_upright' hx) 0
-- --      ((slice_botRight_aux_of_nezero hx h) (slice_botRight hx).A)) := by
-- --   simp [← slice_botRight_equiv_reconstruction' hx h]

-- -- @[simp]
-- -- noncomputable def Matrix.equivSumFin' {m} [NeZero n] :
-- --   Matrix (Fin 0 ⊕ Fin m) (Fin 1 ⊕ Fin (n - 1)) R
-- --   ≃ Matrix (Fin m) (Fin n) R :=
-- -- reindex (finSumFinEquivOfLE (Nat.zero_le m))  (finSumFinEquivOfLE NeZero.one_le)

-- -- noncomputable def slice_botRight_aux_of_zero (h : x.A 0 0 = 0) :
-- --   Matrix (Fin (slice_botRight hx).m) (Fin (slice_botRight hx).n) R
-- --   ≃ Matrix (Fin x.m) (Fin (x.n - 1)) R :=
-- --   reindex (finCongr (slice_botRight_m_eq_m_zero hx h))
-- --    (finCongr (slice_botRight_eq_sub_one hx))

-- -- lemma equivSumFin'_zero_pivot_decomposition' (h : MatObj.A 0 0 = 0) :
-- --   equivSumFin'.2 x.A = (fromBlocks 0 0 0 (slice_botRight_aux_of_zero hx h (slice_botRight hx).A)) := by
-- --   funext i j
-- --   match hi : i, hj : j with
-- --   | Sum.inl u, _ =>
-- --     exfalso
-- --     exact not_succ_le_zero u.1 u.2
-- --   | Sum.inr u, Sum.inl v =>
-- --     simp [Fin.fin_one_eq_zero];
-- --     by_cases hu : 0 < u
-- --     · apply hx.3
-- --       simpa [finSumFinEquivOfLE]
-- --     simp at hu
-- --     simpa [hu, finSumFinEquivOfLE, Fin.castAdd, Fin.castLE]
-- --   | Sum.inr u, Sum.inr v =>
-- --     simp [finSumFinEquivOfLE, Fin.cast, slice_botRight_aux_of_zero]
-- --     let s : Fin ((slice_botRight hx).m):= ⟨u.1, Fin.cast._proof_1 (Eq.symm (slice_botRight_aux_of_zero._proof_1 hx h)) u ⟩
-- --     let t : Fin ((slice_botRight hx).n):= ⟨v.1, Fin.cast._proof_1 (Eq.symm (slice_botRight_aux_of_nezero._proof_2 hx)) v ⟩
-- --     show x.A ⟨s, Fin.cast._proof_1 (slice_botRight_m_eq_m_zero hx h) s⟩ ⟨1 + t.1, id (Eq.refl (1 + t.1)) ▸ Fin.cast._proof_1 (one_add_slice_botRight_eq_sub_one hx) (Fin.natAdd 1 t)⟩
-- --       = (slice_botRight hx).A s t
-- --     apply slice_botRight_m_eq_m_zero' hx h


-- -- lemma equivSumFin'_zero_pivot_decomposition (h) :
-- --    x.A = equivSumFin'.1
-- --   (fromBlocks 0 0 0 (slice_botRight_aux_of_zero hx h (slice_botRight hx).A)) := by
-- --   simp [← equivSumFin'_zero_pivot_decomposition']


-- -- lemma slice_botRight_aux_of_nezero_preserves_rowEchelonable
-- --   (h) {A} (hA : A.IsRowEchelonable) :
-- --   ((slice_botRight_aux_of_nezero hx h) A).IsRowEchelonable := by
-- --   apply isRowEchelonable_reindex_of_order_preserving hA _ _
-- --   repeat intro _ _ _; simpa


-- -- lemma slice_botRight_aux_of_zero_preserves_rowEchelonable (h) {A} (hA : A.IsRowEchelonable) :
-- --   ((slice_botRight_aux_of_zero hx h) A).IsRowEchelonable := by
-- --   apply isRowEchelonable_reindex_of_order_preserving hA _ _
-- --   repeat intro _ _ _; simpa



-- -- open Matrix.NonZeroIndex

-- -- section Matrix.NonZeroIndex
-- -- lemma submatrix_nonZeroIndex_equiv_cast {m i} [Zero F] [NeZero m] [NeZero n]
-- --     (A : Matrix (Fin 1 ⊕ Fin (m - 1)) (Fin 1 ⊕ Fin (n - 1)) F) :
-- --     (A.submatrix (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm).NonZeroIndex i =
-- --     WithTop.map (Fin.cast (add_sub_of_le NeZero.one_le))
-- --     ((A.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).NonZeroIndex (Fin.cast (add_sub_of_le NeZero.one_le).symm i)) := by
-- --   apply submatrix_nonZeroIndex_map_simple A (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm i
-- --     finSumFinEquiv.symm finSumFinEquiv.symm (Fin.cast (add_sub_of_le NeZero.one_le).symm)
-- --   · exact (fun hj _ ↦ hj _ )
-- --   · exact fun j hkj k hk ↦ hkj _ hk
-- --   · rfl
-- --   · funext i
-- --     simp [finSumFinEquivOfLE]


-- -- lemma fromBlocks_reindex_nonZeroIndex_left_case [Zero α] [NeZero n] [NeZero m]
-- --     {i : Fin m}
-- --     (A : Matrix (Fin 1) (Fin 1) α) (B : Matrix (Fin 1) (Fin (n - 1)) α)
-- --     (C : Matrix (Fin (m - 1)) (Fin 1) α) (D : Matrix (Fin (m - 1)) (Fin (n - 1)) α)
-- --     (hi : i.1 < 1) (ha : A.NonZeroIndex ⟨i, hi⟩ ≠ ⊤) :
-- --     ((fromBlocks A B C D).reindex (finSumFinEquivOfLE NeZero.one_le) (finSumFinEquivOfLE NeZero.one_le)).NonZeroIndex i =
-- --     WithTop.map (fun y => Fin.cast (add_sub_of_le NeZero.one_le) (Fin.castAdd (n - 1) y)) (A.NonZeroIndex ⟨i, hi⟩) := by
-- --   simp only [reindex_apply]
-- --   have : A = (fromBlocks A B C D).submatrix (Sum.inl) (Sum.inl) := rfl
-- --   nth_rw 2 [this]
-- --   apply submatrix_nonZeroIndex_map_finite_case
-- --     (fromBlocks A B C D) (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm
-- --     i Sum.inl Sum.inl (fun j ↦ j.1 < 1) hi (fun j ↦ ⟨j.1, j.2⟩) (fun y => Fin.cast (add_sub_of_le NeZero.one_le) (Fin.castAdd (n - 1) y))
-- --   · simpa
-- --   · intro j hkj k hk
-- --     simp [Fin.cast] at hk
-- --   · have : i = 0 := Fin.val_eq_zero_iff.mp <| lt_one_iff.mp hi
-- --     simp [finSumFinEquivOfLE, finSumFinEquiv, Fin.addCases, this, Fin.castLT]
-- --   · funext i
-- --     have : i = 0 := Fin.fin_one_eq_zero i
-- --     simp [finSumFinEquivOfLE, finSumFinEquiv, Fin.addCases, this, Fin.castAdd, Fin.castLE, Fin.castLT]

-- -- lemma fromBlocks_reindex_nonZeroIndex_left_case_submatrix [Zero α] [NeZero n] [NeZero m]
-- --     {i : Fin m}
-- --     (A : Matrix (Fin 1) (Fin 1) α) (B : Matrix (Fin 1) (Fin (n - 1)) α)
-- --     (C : Matrix (Fin (m - 1)) (Fin 1) α) (D : Matrix (Fin (m - 1)) (Fin (n - 1)) α)
-- --     (hi : i.1 < 1) (ha : A.NonZeroIndex ⟨i, hi⟩ ≠ ⊤) :
-- --     ((fromBlocks A B C D).submatrix (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm).NonZeroIndex i =
-- --     WithTop.map (fun y => Fin.cast (add_sub_of_le NeZero.one_le) (Fin.castAdd (n - 1) y)) (A.NonZeroIndex ⟨i, hi⟩) := by
-- --   apply fromBlocks_reindex_nonZeroIndex_left_case
-- --   apply ha


-- -- lemma fromBlocks_lowerTriangular_reindex_nonZeroIndex_case
-- --     [Zero α] [NeZero n] [NeZero m]
-- --     {i : Fin m}
-- --     (A : Matrix (Fin 1) (Fin 1) α) (B : Matrix (Fin 1) (Fin (n - 1)) α)
-- --     (D : Matrix (Fin (m - 1)) (Fin (n - 1)) α)
-- --     (hi : 1 ≤ i.1) :
-- --     ((fromBlocks A B 0 D).submatrix (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm).NonZeroIndex i =
-- --     WithTop.map (fun y => (Fin.cast (add_sub_of_le NeZero.one_le) (Fin.natAdd 1 y)))
-- --       (D.NonZeroIndex (@Fin.natSub 1 (m - 1) (Fin.cast (add_sub_of_le NeZero.one_le).symm i) hi)) := by
-- --     apply submatrix_nonZeroIndex_map (fromBlocks A B 0 D) (finSumFinEquivOfLE NeZero.one_le).symm (finSumFinEquivOfLE NeZero.one_le).symm
-- --       i Sum.inr Sum.inr (fun j ↦ 1 ≤ j.1) hi
-- --       (fun j ↦ @Fin.natSub 1 (m - 1) (Fin.cast (add_sub_of_le NeZero.one_le).symm j.1) j.2)
-- --     · intro hj j
-- --       match ((finSumFinEquivOfLE NeZero.one_le).symm j) with
-- --       | Sum.inr u => simp only [hj]
-- --       | Sum.inl v => simp only [fromBlocks_apply₂₁, zero_apply]
-- --     · intro j hj k hk
-- --       match hkf : ((finSumFinEquivOfLE NeZero.one_le).symm k) with
-- --       | Sum.inr u =>
-- --         simp at *
-- --         apply hj
-- --         simp [finSumFinEquivOfLE, finSumFinEquiv, Fin.addCases] at hkf
-- --         by_cases hkl : k = 0
-- --         · simp [hkl] at hkf
-- --         simp [hkl, Fin.subNat] at hkf
-- --         simp [← hkf]
-- --         refine Fin.mk_lt_of_lt_val <| Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt ?_) hk
-- --         simpa
-- --       | Sum.inl v => simp only [fromBlocks_apply₂₁, zero_apply]
-- --     · have : ¬ i = 0 := Fin.pos_iff_ne_zero.mp hi
-- --       simp [finSumFinEquivOfLE, finSumFinEquiv, Fin.addCases, this, Fin.natSub, Fin.subNat]
-- --     · funext i
-- --       simp [finSumFinEquivOfLE, finSumFinEquiv, Fin.addCases, Fin.natAdd]

-- -- end Matrix.NonZeroIndex

-- -- /--
-- -- Characterizes when a 1×1 matrix is the zero matrix.

-- -- A matrix with a single entry is zero if and only if its only entry is zero.
-- -- This follows from the fact that `Fin 1` has only one element (index 0).
-- -- -/
-- -- lemma matrix_one_by_one_zero_iff [Zero F] {a : Matrix (Fin 1) (Fin 1) F} :
-- --   a = 0 ↔ a 0 0 = 0 := by
-- --   refine ⟨?_, ?_⟩
-- --   · intro ha
-- --     show a 0 0 = (0: Matrix (Fin 1) (Fin 1) F) 0 0
-- --     rw [ha]
-- --   · intro ha
-- --     funext i j
-- --     simpa [Fin.fin_one_eq_zero]

-- -- lemma matrix_one_by_one_ne_zero_iff [Zero F] {a : Matrix (Fin 1) (Fin 1) F} :
-- --   a ≠ 0 ↔ a 0 0 ≠ 0 := by
-- --   simp [matrix_one_by_one_zero_iff]

-- -- /--
-- -- Characterizes when the square of a 1×1 matrix is zero.

-- -- For a 1×1 matrix over a ring with no zero divisors, `a * a = 0` if and only if
-- -- the single entry `a 0 0 = 0`. This follows from the fact that matrix multiplication
-- -- of 1×1 matrices reduces to ordinary multiplication of their entries.
-- -- -/
-- -- lemma matrix_one_by_one_square_zero_iff [Ring F] [NoZeroDivisors F]
-- --   {a : Matrix (Fin 1) (Fin 1) F} :
-- --   a * a = 0 ↔ a 0 0 = 0 := by
-- --   simp [matrix_one_by_one_zero_iff, HMul.hMul, dotProduct]
-- --   show (a 0 0) * (a 0 0) = 0 ↔ _
-- --   rw [mul_self_eq_zero]

-- -- lemma matrix_one_by_one_square_ne_zero_iff [Ring F] [NoZeroDivisors F]
-- --   {a : Matrix (Fin 1) (Fin 1) F} :
-- --   a * a ≠ 0 ↔ a 0 0 ≠ 0 := by
-- --   simp [matrix_one_by_one_square_zero_iff]

-- -- /--
-- -- Determines the non-zero index of a non-zero 1×1 matrix.

-- -- For a non-zero 1×1 matrix, the non-zero index at row 0 must be column 0,
-- -- since there's only one possible entry position.
-- -- -/
-- -- lemma matrix_one_by_one_nonZeroIndex [Zero F] {a : Matrix (Fin 1) (Fin 1) F} (ha : a ≠ 0) :
-- --   a.NonZeroIndex 0 = some 0 := by
-- --   simp [eq_some_iff]
-- --   show a 0 0 ≠ (0: Matrix (Fin 1) (Fin 1) F) 0 0
-- --   by_contra!
-- --   apply ha
-- --   funext i j
-- --   simp [Fin.fin_one_eq_zero] at *
-- --   exact this

-- -- /--
-- -- A non-zero 1×1 matrix never has a ⊤ (all-zero) non-zero index.

-- -- For any valid row index `⟨i, hi⟩` where `i < 1` in a non-zero 1×1 matrix,
-- -- the non-zero index cannot be ⊤, since the matrix has at least one non-zero entry.
-- -- -/
-- -- lemma matrix_one_by_one_nonZeroIndex_ne_top {i} [Zero F] {a : Matrix (Fin 1) (Fin 1) F}
-- --   (ha : a ≠ 0) (hi : i < 1) :
-- --   a.NonZeroIndex ⟨i, hi⟩ ≠ ⊤ := by
-- --   simp [lt_one_iff.mp hi, matrix_one_by_one_nonZeroIndex ha]

-- -- /--
-- -- The non-zero index of a non-zero 1×1 matrix is always column 0.

-- -- For any valid row index `⟨i, hi⟩` where `i < 1` in a non-zero 1×1 matrix,
-- -- the non-zero index is exactly `some 0`, since there's only one possible column.
-- -- -/
-- -- lemma matrix_one_by_one_nonZeroIndex_eq_some_zero {i} [Zero F] {a : Matrix (Fin 1) (Fin 1) F}
-- --   (ha : a ≠ 0) (hi : i < 1) :
-- --   a.NonZeroIndex ⟨i, hi⟩ = some 0 := by
-- --   simp [lt_one_iff.mp hi, matrix_one_by_one_nonZeroIndex ha]


-- -- lemma isRowEchelonable_fromBlocks_upper_triangular
-- --     [Field F] {m n : ℕ} [NeZero m] [NeZero n]
-- --     (a : Matrix (Fin 1) (Fin 1) F) (ha : a ≠ 0)
-- --     (b : Matrix (Fin 1) (Fin (n - 1)) F)
-- --     (c : Matrix (Fin (m - 1)) (Fin (n - 1)) F)
-- --     (hxr : IsRowEchelonable c) :
-- --     IsRowEchelonable (equivSumFin.1 (fromBlocks a b 0 c)) := by
-- --   rcases hxr with ⟨P, pc⟩
-- --   have haa : a * a ≠ 0 :=
-- --     matrix_one_by_one_square_ne_zero_iff.2 <| matrix_one_by_one_ne_zero_iff.1 ha
-- --   let A : GL (Fin 1) F := Matrix.GeneralLinearGroup.mk' a
-- --     (by simpa using invertibleOfNonzero <| matrix_one_by_one_ne_zero_iff.1 ha)
-- --   let Q : GL (Fin m) F :=
-- --     (Matrix.GeneralLinearGroup.reindex F <| finSumFinEquivOfLE NeZero.one_le).1 (Matrix.GeneralLinearGroup.glDirectSum A P)
-- --   use Q; simp [Q, GeneralLinearGroup.reindex, GeneralLinearGroup.glDirectSum, equivSumFin, reindex_apply, submatrix_mul_equiv,
-- --     fromBlocks_multiply, GeneralLinearGroup.val_mk', A, Matrix.isRowEchelon_iff]
-- --   intro i j hij hnt; change _ ≠ ⊤ at hnt
-- --   have hi1 := fromBlocks_reindex_nonZeroIndex_left_case_submatrix (i := i) (a * a) (a * b) 0 (P.1 * c)
-- --   have hi2 := fromBlocks_lowerTriangular_reindex_nonZeroIndex_case (i := i) (a * a) (a * b) (P.1 * c)
-- --   have hj1 := fromBlocks_reindex_nonZeroIndex_left_case_submatrix (i := j) (a * a) (a * b) 0 (P.1 * c)
-- --   have hj2 := fromBlocks_lowerTriangular_reindex_nonZeroIndex_case (i := j) (a * a) (a * b) (P.1 * c)
-- --   rcases (Nat.lt_or_ge i.1 1) , (Nat.lt_or_ge j.1 1) with ⟨hi | hi, hj | hj⟩
-- --   · simp [Fin.val_eq_zero_iff.mp (lt_one_iff.mp hi),  Fin.val_eq_zero_iff.mp (lt_one_iff.mp hj)] at hij
-- --   · simp [hi1 hi (matrix_one_by_one_nonZeroIndex_ne_top haa _), hj2 hj, matrix_one_by_one_nonZeroIndex_eq_some_zero haa _]
-- --     let yP := (P.1 * c).NonZeroIndex (Fin.natSub (m - 1) (Fin.cast (add_sub_of_le NeZero.one_le).symm j) hj)
-- --     show WithTop.some (Fin.cast (add_sub_of_le NeZero.one_le) (Fin.castAdd (n - 1) 0)) < WithTop.map _ yP
-- --     simp only [Fin.cast, Fin.isValue, Fin.coe_castAdd, Fin.val_eq_zero, Fin.mk_zero',
-- --       WithTop.coe_zero, Fin.coe_natAdd]
-- --     by_cases hyp : yP = ⊤
-- --     · simp [hyp]
-- --     · change yP ≠ ⊤ at hyp
-- --       rw [WithTop.ne_top_iff_exists] at hyp
-- --       rcases hyp with ⟨a, ha⟩
-- --       simp [← ha,  ← Fin.val_fin_lt]
-- --   · exfalso; exact (not_lt.2 <| le_trans (le_of_lt hj) hi) hij
-- --   · simpa [hi2 hi, hj2 hj] using  WithTop.map_lt_of_lt _  (by simp) <| pc.1 _ _ (by simp [Fin.natSub, Nat.sub_lt_sub_right hi hij])
-- --         (by simp [hj2 hj] at hnt; simpa)

-- -- lemma zero_padded_submatrix_nonZeroIndex [CommRing F] {m n : ℕ} [NeZero n]
-- --   (A : Matrix (Fin m) (Fin (n - 1)) F) (i : Fin m) :
-- --   ((fromBlocks 0 0 0 A).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).symm (finSumFinEquivOfLE (@NeZero.one_le n _)).symm).NonZeroIndex i
-- --   = WithTop.map (fun y ↦ Fin.cast (add_sub_of_le NeZero.one_le) (Fin.natAdd 1 y)) (A.NonZeroIndex i) := by
-- --   apply submatrix_nonZeroIndex_map_simple (fromBlocks 0 0 0 A) (finSumFinEquivOfLE (Nat.zero_le m)).symm (finSumFinEquivOfLE (@NeZero.one_le n _)).symm
-- --     i Sum.inr Sum.inr id (fun y ↦ Fin.cast (add_sub_of_le NeZero.one_le) (Fin.natAdd 1 y))
-- --   · intro hj j
-- --     match (finSumFinEquivOfLE (@NeZero.one_le n _)).symm j with
-- --     | Sum.inl u => simp
-- --     | Sum.inr v => simpa using hj _
-- --   · intro j hj k hk
-- --     simp [Fin.cast] at hk
-- --     match h : (finSumFinEquivOfLE (@NeZero.one_le n _)).symm k with
-- --     | Sum.inl u => simp
-- --     | Sum.inr v =>
-- --       simp at *
-- --       apply hj
-- --       by_cases hk0 : k = 0
-- --       · simp [finSumFinEquivOfLE, Fin.cast, finSumFinEquiv, Fin.addCases, hk0] at h
-- --       simp [finSumFinEquivOfLE, Fin.cast, finSumFinEquiv, Fin.addCases, hk0] at h
-- --       simp [← h]
-- --       refine Fin.mk_lt_of_lt_val <| (Nat.sub_lt_iff_lt_add' ?_).mpr hk
-- --       refine one_le_iff_ne_zero.mpr (Fin.val_ne_zero_iff.mpr hk0)
-- --   · simp [finSumFinEquivOfLE, Fin.cast, finSumFinEquiv, Fin.addCases]
-- --   · funext
-- --     simp [finSumFinEquivOfLE, Fin.cast, finSumFinEquiv, Fin.addCases]

-- -- lemma finSumFinEquivOfLE_zero_equiv_eq_inr :
-- --    (finSumFinEquivOfLE (Nat.zero_le m)).2 = Sum.inr := by
-- --     funext i
-- --     simp [finSumFinEquivOfLE, Fin.cast, finSumFinEquiv, Fin.addCases]

-- -- lemma matrix_mul_submatrix_fromBlocks_zero_top_with_equiv [AddCommMonoid F] [Mul F] [NeZero n]
-- --   (a : Matrix (Fin m) (Fin 1) F) (b : Matrix (Fin m) (Fin (n - 1)) F)
-- --   (P : Matrix (Fin m) (Fin m) F) :
-- --   P * ((fromBlocks 0 0 a b : Matrix (Fin 0 ⊕ Fin m) (Fin 1 ⊕ Fin (n - 1)) F).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).2 (finSumFinEquivOfLE (@NeZero.one_le n _)).2) =
-- --   (fromBlocks 0 0 (P * a) (P * b) : Matrix (Fin 0 ⊕ Fin m) (Fin 1 ⊕ Fin (n - 1)) F ).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).2 (finSumFinEquivOfLE (@NeZero.one_le n _)).2 := by
-- --   rw [finSumFinEquivOfLE_zero_equiv_eq_inr]
-- --   apply matrix_mul_distrib_submatrix_fromBlocks_zero_top

-- -- lemma isRowEchelonable_fromBlocks_upper_triangular'
-- --     [CommRing F] {m n : ℕ} [NeZero n]
-- --     (c : Matrix (Fin m) (Fin (n - 1)) F)
-- --     (hxr : IsRowEchelonable c) :
-- --     IsRowEchelonable (equivSumFin'.1 (fromBlocks 0 0 0 c)) := by
-- --   rcases hxr with ⟨P, pc⟩
-- --   use P
-- --   simp [reindex_apply]
-- --   show (P.1 * (fromBlocks 0 0 0 c).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).2 (finSumFinEquivOfLE (@NeZero.one_le n _)).2).IsRowEchelon
-- --   rw [matrix_mul_submatrix_fromBlocks_zero_top_with_equiv]
-- --   simp [Matrix.isRowEchelon_iff] at *
-- --   intro i j hij hnt;
-- --   change ((fromBlocks 0 0 0 (P.1 * c)).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).symm (finSumFinEquivOfLE (@NeZero.one_le n _)).symm).NonZeroIndex j ≠ ⊤ at hnt
-- --   show ((fromBlocks 0 0 0 (P.1 * c)).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).symm (finSumFinEquivOfLE (@NeZero.one_le n _)).symm).NonZeroIndex i <
-- --     ((fromBlocks 0 0 0 (P.1 * c)).submatrix (finSumFinEquivOfLE (Nat.zero_le m)).symm (finSumFinEquivOfLE (@NeZero.one_le n _)).symm).NonZeroIndex j
-- --   rw [zero_padded_submatrix_nonZeroIndex (P.1 * c) i, zero_padded_submatrix_nonZeroIndex (P.1 * c) j] at *
-- --   refine
-- --     WithTop.map_lt_of_lt (fun y ↦ Fin.cast (add_sub_of_le NeZero.one_le) (Fin.natAdd 1 y)) ?_ ?_
-- --   · intro x y hxy
-- --     simpa
-- --   · apply pc
-- --     apply hij
-- --     simp at hnt
-- --     apply hnt

-- -- lemma IsRowEchelonable.bridge [Field F] {x : MatObj F} (hx : S_col1Ready x)
-- --     (hxr : (slice_botRight hx).IsRowEchelonable) :
-- --   x.IsRowEchelonable:= by
-- --   simp [MatObj.IsRowEchelonable]
-- --   by_cases h : x.A 0 0 ≠ 0
-- --   · rw [slice_botRight_equiv_reconstruction hx h]
-- --     apply isRowEchelonable_fromBlocks_upper_triangular
-- --     exact matrix_one_by_one_ne_zero_iff.mpr h
-- --     apply slice_botRight_aux_of_nezero_preserves_rowEchelonable hx h hxr
-- --   simp at h
-- --   rw [equivSumFin'_zero_pivot_decomposition hx h]
-- --   apply isRowEchelonable_fromBlocks_upper_triangular'
-- --   apply slice_botRight_aux_of_zero_preserves_rowEchelonable hx h hxr

-- -- end
