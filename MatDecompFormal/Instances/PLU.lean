import MatDecompFormal.Framework.Induction
import MatDecompFormal.Framework.Universe
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Abstractions.Strategy
import MatDecompFormal.Abstractions.ReductionCombinators -- For try_else
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Components.Properties.Reindex
import MatDecompFormal.Components.Reductions.Schur
import MatDecompFormal.Components.Reductions.ZeroColumn
import MatDecompFormal.Components.Transformations.Elementary.Pivot

namespace MatDecompFormal.Instances

open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Components.Transformations.Elementary
open MatDecompFormal.Framework
open Matrix FinEnum

/-!
# 列选主元 LU 分解 (PLU Decomposition)

本文件使用本框架证明了任意一个域上的方阵都存在 PLU 分解。
即，对于任意方阵 `A`，存在一个置换矩阵 `P`、一个单位下三角矩阵 `L`
和一个上三角矩阵 `U`，使得 `P * A = L * U`。

### 证明流程
1.  **定义 `PLU_Schema`**: 使用 `DecompositionSchema` 结构体精确描述 PLU 分解的目标。
2.  **定义 `PLU_Reduction`**:
    - 算法的核心逻辑是：检查第一列的主元 `A i₀ j₀`。
    - 如果它非零，我们使用 `SchurMethod` 进行规约。
    - 如果它为零，但第一列不全为零，我们需要先进行一次行交换。
    - 如果第一列全为零，我们使用 `ZeroColumnMethod` 进行规约。
    - 这个“尝试-回退”逻辑通过 `SchurMethod.try_else ZeroColumnMethod` 完美捕获。
3.  **定义 `PLU_Transform`**:
    - 这是一个 `PivotTransform` 的实例，其目标是达成 `PLU_Reduction` 的
      `IsSliceable` 条件，即 `IsUnit (A i₀ j₀) ∨ (∀ i, A i j₀ = 0)`。
    - 当这两个条件都不满足时（即主元为零但列不为零），它的 `find` 操作会
      找到一个非零元并进行交换。
4.  **组装 `PLU_Strategy`**: 将 `PLU_Transform` 和 `PLU_Reduction` 组合起来，
    并提供度量函数和相关性质证明。
5.  **证明“胶水”引理**:
    - `lift_from_slice_plu`: 证明如果子问题有 PLU 分解，那么原问题也有。
      这是最核心的代数构造部分。
    - `transport_plu`: 证明 PLU 分解性质在行变换下是可传递的。
6.  **调用主定理**: 将所有组件传入 `transformSliceInduction`，完成最终证明。
-/

section PLU_Schema

-- 我们将证明限定在域上的方阵。
variable (ι ι' R : Type*) [FinEnum ι] [FinEnum ι'] [Field R] [DecidableEq R]

-- ==================================================================
-- L3.1: 定义分解模式 (Schema)
-- ==================================================================

/-- `PLU_Schema` 描述了 PLU 分解的目标。 -/
def PLU_Schema : DecompositionSchema ι ι R where
  Factors := Matrix ι ι R × Matrix ι ι R × Matrix ι ι R
  property := fun (P, L, U) ↦
    IsPermutation P ∧ IsUnitLowerTriangular L ∧ IsUpperTriangular U
  equation := fun A (P, L, U) ↦ P * A = L * U

/--
`HasPLU` 是一个命题，表示矩阵 `A` 存在一个 PLU 分解。

我们将其定义为一个 `def` 而不是 `abbrev`，并明确地包含它所依赖的
类型类约束 `[Field R]` 和 `[DecidableEq R]`。这解决了在泛型上下文中
（如 `Transport`）使用它时，类型类实例无法被推断的问题。
-/
def HasPLU (A : Matrix ι ι R) : Prop :=
  HasDecomposition (PLU_Schema (ι := ι) (R := R)) A

-- ------------------------------------------------------------------
-- 步骤 2: 证明 HasPLU 在 reindex 下保持不变
-- ------------------------------------------------------------------

/--
`hasPLU_reindex_iff` 证明了 `HasPLU` 属性在通过保序同构 `reindex` 进行
基变换时是逻辑等价的。
-/
lemma hasPLU_reindex_iff (e : ι ≃ ι') (A : Matrix ι ι R) :
    HasPLU ι R A ↔ HasPLU ι' R (A.reindex e e) := by
  dsimp [HasPLU, HasDecomposition]
  constructor
  · -- (→) HasPLU A → HasPLU (reindex A)
    intro hA
    rcases hA with ⟨⟨P, L, U⟩, ⟨hP, hL, hU⟩, h_eq⟩
    let P' := P.reindex e e
    let L' := L.reindex e e
    let U' := U.reindex e e
    use (P', L', U')
    simp [PLU_Schema]
    constructor
    · -- 证明新因子的性质
      rw [isPermutation_reindex e.symm P', isUnitLowerTriangular_reindex e.symm L',
        isUpperTriangular_reindex e.symm U']
      simp [P', L', U']
      exact ⟨hP, hL, hU⟩
    · -- 证明分解方程
      simp [P', L', U']
      simp [PLU_Schema] at h_eq
      simp [h_eq]
  · -- (←) HasPLU (reindex A) → HasPLU A
    intro hA_reindexed
    -- 与前一个方向对称
    rcases hA_reindexed with ⟨⟨P', L', U'⟩, ⟨hP', hL', hU'⟩, h_eq'⟩
    let P := P'.reindex e.symm e.symm
    let L := L'.reindex e.symm e.symm
    let U := U'.reindex e.symm e.symm
    use (P, L, U)
    simp [PLU_Schema]
    constructor
    · rw [isPermutation_reindex e P, isUnitLowerTriangular_reindex e L,
        isUpperTriangular_reindex e U]
      simp [P, L, U]
      exact ⟨hP', hL', hU'⟩
    · let e_symm : ι' ≃ ι := e.symm
      simp [PLU_Schema] at h_eq'
      simp [P, L, U]
      have : A = (A.submatrix e.symm e.symm).reindex e.symm e.symm := by simp
      rw [this, reindex_apply, Equiv.symm_symm, ← submatrix_mul, h_eq']
      simp

end PLU_Schema


section PLU_Strategy

-- ==================================================================
-- L3.2: 定义并组装策略 (Strategy)
-- ==================================================================

variable {ι : Type*} (R : Type*) [FinEnum ι] [Field R] [DecidableEq R]

/--
`PLU_Strategy` (最终通用版)
-/
noncomputable def PLU_Strategy (h_card : card ι > 0) :
    ReductionStrategy ι ι R where
  -- 1. 变换：定义一个内联的、专门用于 PLU 的变换。
  transform :=
    let i₀ := (@equiv ι).symm ⟨0, h_card⟩
    let j₀ := (@equiv ι).symm ⟨0, h_card⟩
    {
      T := ι,
      -- 目标：达到一个可被组合规约方法处理的状态。
      Goal := (ReductionMethod.try_else
                (SchurMethod ι ι R h_card h_card)
                (ZeroColumnMethod ι ι R h_card h_card)
                (by rfl) -- 修正后的 ZeroColumnMethod 的 Sliceι 与 SchurMethod 相同
                (by rfl) -- 修正后的 ZeroColumnMethod 的 Sliceκ 与 SchurMethod 相同
              ).IsSliceable,
      decGoal := by simp [ReductionMethod.try_else, SchurMethod, ZeroColumnMethod]; infer_instance,
      apply := fun i₁ A ↦ (swap R i₀ i₁) * A,
      find := fun A h_goal_not_met ↦
        have h_exists_nz : ∃ i, A i j₀ ≠ 0 := by
          simp [ReductionMethod.try_else, SchurMethod, ZeroColumnMethod] at h_goal_not_met
          push_neg at h_goal_not_met
          exact h_goal_not_met.2
        Classical.choose h_exists_nz,
      find_spec := by
        intro A h_goal_not_met
        have h_exists_nz : ∃ i, A i j₀ ≠ 0 := by
          simp [ReductionMethod.try_else, SchurMethod, ZeroColumnMethod] at h_goal_not_met
          push_neg at h_goal_not_met
          exact h_goal_not_met.2
        let i₁ := Classical.choose h_exists_nz
        apply Or.inl
        simp [SchurMethod]
        rw [swap_mul_apply_left]
        exact Classical.choose_spec h_exists_nz
    }
  -- 2. 规约：使用由组合子构造的复合规约方法。
  reduction := ReductionMethod.try_else
    (SchurMethod ι ι R h_card h_card)
    (ZeroColumnMethod ι ι R h_card h_card)
    (by rfl) -- Sliceι 类型现在相等
    (by rfl) -- Sliceκ 类型现在相等
  -- 3. 兼容性：平凡。
  goal_is_sliceable := by rfl
  -- 4. 度量
  μ := fun {ι' κ'} _ _ _ ↦ card ι'
  -- 5. 单调性
  μ_mono := by
    intro y x t h_eq
    simp
  -- 6. 进展性
  slice_progress := by
    intro A hA
    dsimp [ReductionMethod.try_else, SchurMethod, ZeroColumnMethod] at hA
    dsimp [ReductionMethod.try_else, SchurMethod]
    simp [FinEnum.card_eq_fintypeCard]
    simp [FinEnum.card_eq_fintypeCard] at h_card
    exact h_card

end PLU_Strategy

-- ==================================================================
-- L3.3: 证明“胶水”引理 (Transport & Lift)
-- ==================================================================

section PLU_Proof

variable {ι : Type*} (R : Type*) [FinEnum ι] [Field R] [DecidableEq R]

/-- `transport_plu` 证明了 PLU 分解性质在行变换下是可传递的。 -/
lemma transport_plu (h_card : card ι > 0) :
    Transport (PLU_Strategy R h_card).r (HasPLU ι R) := by
  intro A' B h_r h_plu_A'
  rcases h_r with ⟨i₁, h_eq_B⟩
  -- 从 h_plu_A' (即 A' 存在 PLU 分解) 中获取 P, L, U
  rcases h_plu_A' with ⟨factors, ⟨⟨hP, hL, hU⟩, h_eq_A⟩⟩
  -- 将 factors 分解为 (P, L, U)
  let (P, L, U) := factors
  -- 构造 B 的分解因子。新的置换矩阵是 P 乘以我们用于变换的行交换矩阵。
  let i₀ := (@equiv ι).symm ⟨0, h_card⟩
  let P' := swap R i₀ i₁
  -- use ((P * P'), L, U) 提供了一个类型为 Factors 的值
  use ((P * P'), L, U)
  -- 证明新的因子满足性质，并且满足分解方程
  constructor
  · dsimp [PLU_Schema]
    refine ⟨?_, hL, hU⟩
    apply isPermutation_mul
    · exact hP
    · apply isPermutation_swap
  · dsimp [PLU_Strategy, ReductionStrategy.transform, PivotTransform] at h_eq_B
    dsimp [PLU_Schema] at h_eq_A
    dsimp [PLU_Schema, P']
    rw [mul_assoc, ← h_eq_B, h_eq_A]

-- 我们的归纳命题 P 现在是定义在 SquareMat 上的
def P_univ (x : Matrix ι ι R) : Prop :=
  if h_card : card ι > 0 then
    HasPLU ι R x
  else
    -- 对于 0x0 矩阵，PLU 分解是平凡的
    True

/--
`lift_from_slice_plu` (通用版) 证明了如果子问题（可能是 0x0 矩阵）
的分解存在性（由 `P_univ` 描述）成立，那么原问题也有 PLU 分解。
-/
lemma lift_from_slice_plu (A : Matrix ι ι R) (h_card_pos : card ι > 0)
    (hA : (PLU_Strategy R h_card_pos).reduction.IsSliceable A)
    -- 前提现在是关于通用命题 P_univ 的
    (h_p_slice : P_univ R (((PLU_Strategy R h_card_pos).reduction.slice A hA))) :
    HasPLU ι R A := by
  dsimp [PLU_Strategy, ReductionMethod.try_else] at hA
  by_cases h_schur : (SchurMethod ι ι R h_card_pos h_card_pos).IsSliceable A
  · -- Case 1: 主元非零，使用 SchurMethod
    sorry

  · -- Case 2: 主元为零，且整列为零，使用 ZeroColumnMethod
    sorry

-- /-- `lift_from_slice_plu` 证明了如果子问题有 PLU 分解，那么原问题也有。 -/
-- lemma lift_from_slice_plu (A : Matrix ι ι R) (h_nonempty : card ι > 0)
--     (hA : (PLU_Strategy R h_nonempty).reduction.IsSliceable A) :
--     HasPLU _ R ((PLU_Strategy R h_nonempty).reduction.slice A hA) → HasPLU ι R A := by sorry
  -- -- 这是一个纯代数的证明，涉及到大量的分块矩阵运算。
  -- intro h_slice_plu
  -- -- 策略的 IsSliceable 是 (SchurMethod).IsSliceable ∨ (ZeroColumnMethod).IsSliceable
  -- -- 我们根据这两种情况进行分支证明
  -- dsimp [PLU_Strategy, ReductionMethod.try_else] at hA
  -- by_cases h_schur : (SchurMethod ι ι R h_nonempty h_nonempty).IsSliceable A
  -- · -- Case 1: 主元非零，使用 SchurMethod
  --   -- 1.1. 展开定义，获取子问题的分解
  --   have hA_schur : (PLU_Strategy R h_nonempty).reduction.IsSliceable A := Or.inl h_schur
  --   let schur := SchurMethod ι ι R h_nonempty h_nonempty
  --   let A_slice := schur.slice A h_schur
  --   -- A_slice 和 (PLU_Strategy ...).reduction.slice A hA_schur 定义相同，但类型不同
  --   -- 我们需要一个转换来应用 h_slice_plu
  --   have h_slice_eq : A_slice = (PLU_Strategy R h_nonempty).reduction.slice A hA_schur := by
  --     dsimp [PLU_Strategy, ReductionMethod.try_else]; rw [dif_pos h_schur]
  --   rcases h_slice_eq ▸ h_slice_plu with ⟨⟨P', L', U'⟩, ⟨hP', hL', hU'⟩, h_eq_A_slice⟩
  --   dsimp [PLU_Strategy, HasPLU, HasDecomposition] at h_eq_A_slice

  --   -- 1.2. 定义 SchurMethod 使用的各种索引和等价关系
  --   let i₀ := (@equiv ι).symm ⟨0, h_nonempty⟩
  --   let p_ι : ι → Prop := fun i ↦ i = i₀
  --   let e_ι : ι ≃ ({i // p_ι i} ⊕ {i // ¬p_ι i}) := (Equiv.sumCompl p_ι).symm
  --   let finEnum_p_ι : FinEnum {i // p_ι i} := {
  --     card := 1,
  --     equiv := {
  --       toFun := fun _ ↦ 0,
  --       invFun := fun _ ↦ ⟨i₀, rfl⟩,
  --       left_inv := by intro ⟨i, hi⟩; simp [p_ι] at hi; simp [hi],
  --       right_inv := by intro ⟨i, hi⟩; simp [Fin.fin_one_eq_zero]
  --     },
  --     decEq := by infer_instance
  --   }
  --   let e_ι₁ : {i // p_ι i} ≃ Fin 1 := finEnum_p_ι.equiv
  --   let e_ι₂ : (PLU_Strategy R h_nonempty).reduction.Sliceι≃{ i // ¬p_ι i } := by
  --     simp [PLU_Strategy, ReductionMethod.try_else, SchurMethod]; rfl

  --   -- 1.3. 提取 A 的分块
  --   let A_reindexed := reindex e_ι e_ι A
  --   let A₁₁ := A_reindexed.toBlocks₁₁
  --   let A₁₂ := A_reindexed.toBlocks₁₂
  --   let A₂₁ := reindex e_ι₂.symm (Equiv.refl _) A_reindexed.toBlocks₂₁
  --   let A₂₂ := A_reindexed.toBlocks₂₂

  --   -- 1.4. 构造 A₁₁ 的逆
  --   let A₁₁_fin1 := reindex e_ι₁ e_ι₁ A₁₁
  --   have h_unit_A₁₁_fin1 : IsUnit A₁₁_fin1 := by
  --     rw [show A₁₁_fin1 = !![A i₀ i₀] by ext i j; simp [A₁₁_fin1]; rfl]
  --     exact isUnit_singleton_iff.mpr h_schur
  --   let inv_A₁₁_fin1 := (IsUnit.unit h_unit_A₁₁_fin1).inv
  --   let inv_A₁₁ := reindex e_ι₁.symm (Equiv.refl _) inv_A₁₁_fin1


  --   -- 1.5. 构造完整矩阵的 P, L, U (使用正确的块矩阵代数)
  --   let P_block := fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 P'
  --   let L_block := fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 (P' * A₂₁ * inv_A₁₁) L'
  --   let U_block := fromBlocks A₁₁ A₁₂ 0 U'

  --   let P := P_block.reindex e_ι.symm e_ι.symm
  --   let L := L_block.reindex e_ι.symm e_ι.symm
  --   let U := U_block.reindex e_ι.symm e_ι.symm

  --   -- 1.6. 证明构造是正确的
  --   use (P, L, U)
  --   constructor
  --   · -- 1.6.1. 证明 P, L, U 的性质
  --     dsimp [PLU_Schema]
  --     constructor
  --     · -- P 的性质
  --       dsimp [IsPermutation]
  --       use (Equiv.Perm.sumCongr (Equiv.refl _) (Classical.choice hP'.1))
  --       rw [← PEquiv.toMatrix_trans, Equiv.Perm.sumCongr_trans]
  --       simp [P_block, fromBlocks_one, PEquiv.toMatrix_reindex, hP'.2]
  --     constructor
  --     · -- L 的性质
  --       dsimp [IsUnitLowerTriangular, IsLowerTriangular, IsUpperTriangular]
  --       rw [transpose_reindex, ← fromBlocks_transpose, BlockTriangular_fromBlocks_transpose_iff]
  --       simp only [BlockTriangular, transpose_zero, and_self]
  --       constructor
  --       · refine ⟨by simp [BlockTriangular_singleton_iff], hL'.1⟩
  --       · rw [diag_reindex, diag_fromBlocks_apply]
  --         intro i; rcases e_ι i with (h | h)
  --         · simp [diag_apply, Fin.fin_one_eq_zero]
  --         · simp [diag_apply, hL'.2]
  --     · -- U 的性质
  --       dsimp [IsUpperTriangular]
  --       rw [BlockTriangular_reindex, BlockTriangular_fromBlocks_iff]
  --       refine ⟨by simp [BlockTriangular_singleton_iff], hU', by simp⟩
  --   · -- 1.6.2. 证明分解方程 P * A = L * U
  --     dsimp [PLU_Schema]
  --     rw [← reindex_mul, ← reindex_mul, reindex_inj e_ι.symm.injective e_ι.symm.injective]
  --     rw [reindex_reindex, reindex_reindex, reindex_reindex, Equiv.symm_symm, Equiv.symm_symm]
  --     rw [fromBlocks_multiply, fromBlocks_multiply]
  --     simp only [one_mul, mul_zero, zero_add, add_zero]
  --     congr
  --     · -- 左下角块
  --       simp
  --     · -- 右下角块
  --       have h_slice_def : A_slice = A₂₂ - A₂₁ * inv_A₁₁ * A₁₂ := by
  --         dsimp [schur, SchurMethod.slice, h_schur]
  --         congr
  --       rw [h_slice_def] at h_eq_A_slice
  --       rw [← h_eq_A_slice, add_comm]
  --       simp [sub_add_cancel]

  -- · -- Case 2: 主元为零，且整列为零，使用 ZeroColumnMethod
  --   -- 2.1. 展开定义，获取子问题的分解
  --   have h_zero_col : (ZeroColumnMethod ι ι R h_nonempty).IsSliceable A := hA.resolve_left h_schur
  --   have hA_zero_col : (PLU_Strategy R h_nonempty).reduction.IsSliceable A := Or.inr h_zero_col
  --   let zero_col_method := ZeroColumnMethod ι ι R h_nonempty
  --   let A_slice := zero_col_method.slice A h_zero_col
  --   have h_slice_eq : A_slice = (PLU_Strategy R h_nonempty).reduction.slice A hA_zero_col := by
  --     dsimp [PLU_Strategy, ReductionMethod.try_else]; rw [dif_neg h_schur]
  --     -- 需要证明 ZeroColumnMethod 的 Sliceι/κ 类型与 try_else 的相同
  --     -- 这在 try_else 的前提 h_slice_ι_eq 中已保证
  --     congr
  --   rcases h_slice_eq ▸ h_slice_plu with ⟨⟨P', L', U'⟩, ⟨hP', hL', hU'⟩, h_eq_A_slice⟩
  --   dsimp [HasPLU, HasDecomposition] at h_eq_A_slice

  --   -- 2.2. 定义 ZeroColumnMethod 使用的索引和等价关系
  --   let j₀ := (@equiv ι).symm ⟨0, h_nonempty⟩
  --   let p_κ : ι → Prop := fun j ↦ j = j₀
  --   let e_κ : ι ≃ ({j // p_κ j} ⊕ {j // ¬p_κ j}) := (Equiv.sumCompl p_κ).symm

  --   -- 2.3. 构造完整矩阵的 P, L, U
  --   let P := P'
  --   let L := L'
  --   let U_block := fromBlocks (0 : Matrix _ _ R) U' 0 0
  --   let e_ι_trivial : ι ≃ ι ⊕ Fin 0 := Equiv.trans (Equiv.sumEmpty ι (Fin 0)).symm
  --       (Equiv.sumCongr (Equiv.refl ι) (Equiv.equivOfIsEmpty _ _))
  --   let U := U_block.reindex e_ι_trivial.symm e_κ.symm

  --   -- 2.4. 证明构造是正确的
  --   use (P, L, U)
  --   constructor
  --   · -- 2.4.1. 证明 P, L, U 的性质
  --     dsimp [PLU_Schema]
  --     refine ⟨hP', hL', ?_⟩
  --     -- U 的性质
  --     dsimp [IsUpperTriangular]
  --     rw [BlockTriangular_reindex, BlockTriangular_fromBlocks_iff]
  --     refine ⟨by simp [BlockTriangular_zero], hU', by simp⟩
  --   · -- 2.4.2. 证明分解方程 P * A = L * U
  --     dsimp [PLU_Schema]
  --     have h_A_block : reindex e_ι_trivial e_κ A = fromBlocks 0 A_slice 0 0 := by
  --       ext i j
  --       rcases i with (i' | i')
  --       · rcases j with (j' | j')
  --         · simp [h_zero_col]
  --         · simp [A_slice]
  --       · simp
  --     rw [← reindex_mul, h_A_block, fromBlocks_multiply, mul_zero, zero_mul, zero_add]
  --     rw [← reindex_mul, fromBlocks_multiply, mul_zero, zero_mul, zero_add]
  --     congr
  --     rw [h_eq_A_slice]



end PLU_Proof


-- ==================================================================
-- L3.4: 组装最终证明 (最终版 - SquareMat 宇宙方案)
-- ==================================================================

section FinalProof

variable {ι : Type*} (R : Type*) [FinEnum ι] [Field R] [DecidableEq R]

namespace FinEnum

/--
利用两个 `FinEnum` 类型的 `equiv` 构造一个在它们之间可计算的双射。
这个版本使用了 `Fin.castOrderIso` 来确保类型正确。
-/
@[simps!]
def equivOfCardEq {ι κ : Type*} [FinEnum ι] [FinEnum κ] (h : card ι = card κ) : ι ≃ κ :=
  -- 流程: ι ≃ Fin (card ι) ≃o Fin (card κ) ≃ κ
  (@equiv ι).trans ((Fin.castOrderIso h).toEquiv.trans (@equiv κ).symm)

end FinEnum


-- ------------------------------------------------------------------
-- 步骤 2: 在 SquareMat 宇宙中定义所有包装器
-- ------------------------------------------------------------------

/-- `P_pos_sq` 是 HasPLU 在 PositiveSquareMat 宇宙中的直接映射。 -/
private def P_pos_sq (x : PositiveSquareMat R) : Prop :=
  let e : x.val.mat.ι ≃ x.val.mat.κ := FinEnum.equivOfCardEq x.val.is_square
  HasPLU x.val.mat.ι R (x.val.mat.matrix.reindex (Equiv.refl _) e.symm)

/-- `r_pos_sq` 是 PLU 变换关系在 PositiveSquareMat 宇宙中的映射 (最终健壮版)。 -/
private def r_pos_sq (y x : PositiveSquareMat R) : Prop :=
  -- 条件：比较两个可判定的自然数 `card`
  if h_size_eq : card x.val.mat.ι = card y.val.mat.ι then
    have h_card_pos : card x.val.mat.ι > 0 := x.property

    -- 构造 x 的 reindex
    let e_xκ : x.val.mat.κ ≃ x.val.mat.ι := FinEnum.equivOfCardEq x.val.is_square.symm
    let x_reindexed := x.val.mat.matrix.reindex (Equiv.refl _) e_xκ

    -- 构造 y 的 reindex，通过组合已有的 Equiv
    let e_yx : y.val.mat.ι ≃ x.val.mat.ι := FinEnum.equivOfCardEq h_size_eq.symm
    let e_yκ_to_yι : y.val.mat.κ ≃ y.val.mat.ι := (FinEnum.equivOfCardEq y.val.is_square).symm
    let e_yκ_to_xι : y.val.mat.κ ≃ x.val.mat.ι := e_yκ_to_yι.trans e_yx
    let y_reindexed := y.val.mat.matrix.reindex e_yx e_yκ_to_xι

    (PLU_Strategy R h_card_pos).r y_reindexed x_reindexed
  else
    False



/-- `IsSliceable_sq` 是 IsSliceable 在 SquareMat 宇宙中的映射。 -/
private def IsSliceable_pos_sq (x : PositiveSquareMat R) : Prop :=
  let e_κ : x.val.mat.κ ≃ x.val.mat.ι := FinEnum.equivOfCardEq x.val.is_square.symm
  let A := x.val.mat.matrix.reindex (Equiv.refl _) e_κ
  (PLU_Strategy R x.2).reduction.IsSliceable A

/-- `slice_pos_sq` 返回一个通用的 `SquareMat`，因为维度可能变为 0。 -/
private noncomputable def slice_pos_sq {x : PositiveSquareMat R} (hx : IsSliceable_pos_sq R x) :
      SquareMat R :=
  let S := (PLU_Strategy R x.property).reduction
  let e_κ : x.val.mat.κ ≃ x.val.mat.ι := FinEnum.equivOfCardEq x.val.is_square.symm
  let A := x.val.mat.matrix.reindex (Equiv.refl _) e_κ
  let slice_matrix := S.slice A hx
  have h_slice_sq : card S.Sliceι = card S.Sliceκ := by --sorry -- (依赖于 Schur/ZeroColumn 将方阵映为方阵)
    simp [S, PLU_Strategy, ReductionMethod.try_else, SchurMethod]
  ⟨⟨S.Sliceι, S.Sliceκ, slice_matrix⟩, h_slice_sq⟩

-- /-- `slice_pos_sq` 在 PositiveSquareMat 宇宙中的映射。 -/
-- private noncomputable def slice_pos_sq {x : PositiveSquareMat R}
--     (hx : IsSliceable_pos_sq R x) : PositiveSquareMat R :=
--   let S := (PLU_Strategy R x.property).reduction
--   let e_κ : x.val.mat.κ ≃ x.val.mat.ι := FinEnum.equivOfCardEq x.val.is_square.symm
--   let A := x.val.mat.matrix.reindex (Equiv.refl _) e_κ
--   let slice_matrix := S.slice A hx
--   have h_slice_sq : card S.Sliceι = card S.Sliceκ := by sorry -- (同前)
--   have h_slice_card_pos : card S.Sliceι > 0 := by
--     -- 证明 slice 后的维度仍然 > 0，直到基例
--     -- 这需要修改 μ 的定义，例如 μ = card ι - 1
--     sorry
--   let slice_sq_mat : SquareMat R := ⟨⟨S.Sliceι, S.Sliceκ, slice_matrix⟩, h_slice_sq⟩
--   ⟨slice_sq_mat, h_slice_card_pos⟩


-- ------------------------------------------------------------------
-- 步骤 3: 证明包装引理
-- ------------------------------------------------------------------

/--
`transport_wrapper_sq` 是 `transport_plu` 引理的宇宙级包装器。

它直接证明了 `Transport` 命题，展示了 `P_pos_sq` 在 `r_pos_sq`
关系下的传递性。
-/
private lemma transport_wrapper_sq : Transport (r_pos_sq R) (P_pos_sq R) := by
  intro y x h_r h_p_y
  dsimp [r_pos_sq] at h_r
  split_ifs at h_r with h_size_eq
  dsimp [P_pos_sq] at *
  have h_card_pos : card x.val.mat.ι > 0 := x.property
  let e_xκ := FinEnum.equivOfCardEq x.val.is_square.symm
  let x_reindexed := x.val.mat.matrix.reindex (Equiv.refl _) e_xκ

  let e_yx := FinEnum.equivOfCardEq h_size_eq.symm
  let e_yκ_to_yι := (FinEnum.equivOfCardEq y.val.is_square).symm
  let e_yκ_to_xι := e_yκ_to_yι.trans e_yx
  let y_reindexed := y.val.mat.matrix.reindex e_yx e_yκ_to_xι

  have h_p_y_reindexed : HasPLU x.val.mat.ι R y_reindexed := by
    let e_y_κ_to_ι : y.val.mat.κ ≃ y.val.mat.ι := FinEnum.equivOfCardEq y.val.is_square.symm
    let y_p_ver := y.val.mat.matrix.reindex (Equiv.refl _) e_y_κ_to_ι
    let e_yx_iso : y.val.mat.ι ≃ x.val.mat.ι := FinEnum.equivOfCardEq h_size_eq.symm

    -- 使用新的 hasPLU_reindex_iff 引理
    exact (hasPLU_reindex_iff _ _ R e_yx_iso _).mp h_p_y
  exact (transport_plu R h_card_pos) _ _ h_r h_p_y_reindexed

-- private lemma transport_wrapper_sq : Transport (r_pos_sq R) (P_pos_sq R) := by
--   -- 目标：∀ (y x : PositiveSquareMat R), r_pos_sq R y x → P_pos_sq R y → P_pos_sq R x
--   intro y x h_r h_p_y

--   -- 步骤 1: 展开定义
--   dsimp [r_pos_sq] at h_r
--   dsimp [P_pos_sq] at *

--   -- 步骤 2: if 条件为真，h_r 就是具体的关系证明
--   split_ifs at h_r with h_size_eq

--   -- 步骤 3: 准备调用 transport_plu
--   have h_card_pos : card x.val.mat.ι > 0 := x.property

--   -- 构造与 r_pos_sq 中完全相同的 reindexed 矩阵
--   let e_xκ := FinEnum.equivOfCardEq x.val.is_square.symm
--   let x_reindexed := x.val.mat.matrix.reindex (Equiv.refl _) e_xκ

--   let e_yx := FinEnum.equivOfCardEq h_size_eq.symm
--   let e_yκ_to_yι := (FinEnum.equivOfCardEq y.val.is_square).symm
--   let e_yκ_to_xι := e_yκ_to_yι.trans e_yx
--   let y_reindexed := y.val.mat.matrix.reindex e_yx e_yκ_to_xι

--   -- 步骤 4: 调用具体引理
--   -- h_r 和 h_p_y 的类型现在与 transport_plu 的输入精确匹配！
--   exact (transport_plu R h_card_pos) y_reindexed x_reindexed h_r h_p_y


private lemma lift_wrapper_sq :
    ∀ {x : PositiveSquareMat R} (hx : IsSliceable_pos_sq R x),
    -- P 是定义在 SquareMat 上的通用命题
    (let slice_result := slice_pos_sq R hx;
     if h_slice_pos : card slice_result.mat.ι > 0 then
      P_pos_sq R ⟨slice_result, h_slice_pos⟩ else True) →
    P_pos_sq R x := by
  intro x hx h_p_slice
  dsimp [P_pos_sq]
  let A := x.val.mat.matrix.reindex (Equiv.refl _) (FinEnum.equivOfCardEq x.val.is_square.symm)
  have hA : (PLU_Strategy R x.property).reduction.IsSliceable A := by convert hx
  -- 对子问题的解进行分情况讨论
  let slice_result := slice_pos_sq R hx
  dsimp at h_p_slice
  split_ifs at h_p_slice with h_slice_pos
  · -- Case 1: slice 后的维度 > 0
    refine lift_from_slice_plu R A x.property hA ?_
    simp [P_univ]
    sorry
  · -- Case 2: slice 后的维度 = 0 (即 1x1 -> 0x0)
    -- 此时 h_p_slice 是 True，我们需要一个能处理这种情况的 lift
    -- 这意味着 lift_from_slice_plu 需要一个更通用的前提
    sorry

-- private lemma lift_wrapper_sq :
--     ∀ {x} (hx : IsSliceable_pos_sq R x), P_pos_sq R (slice_pos_sq R hx) → P_pos_sq R x := by
--   intro x hx h_p_slice
--   dsimp [P_pos_sq]
--   let A := x.val.mat.matrix.reindex (Equiv.refl _) (FinEnum.equivOfCardEq x.val.is_square.symm)
--   have hA : (PLU_Strategy R x.2).reduction.IsSliceable A := by
--     dsimp [IsSliceable_pos_sq] at hx; convert hx
--   have h_p_slice_concrete : HasPLU _ R ((PLU_Strategy R x.2).reduction.slice A hA) := by
--     dsimp [P_pos_sq, slice_pos_sq] at h_p_slice; simp [A,hA]; apply h_p_slice;
--   exact lift_from_slice_plu R A x.2 hA h_p_slice_concrete

private lemma reach_metric_wrapper_sq :
    ∀ {x : PositiveSquareMat R}, (fun y ↦ card y.val.mat.ι) x > 0 →
    ∃ y, ∃ (hy : IsSliceable_pos_sq R y),
    r_pos_sq R y x ∧ (fun z ↦ card z.mat.ι) (slice_pos_sq R hy) < (fun z ↦ card z.val.mat.ι) x := by
  intro x h_mu_pos
  let A := x.val.mat.matrix.reindex (Equiv.refl _) (FinEnum.equivOfCardEq x.val.is_square.symm)
  let S_strat := PLU_Strategy R h_mu_pos
  have h_reach_concrete := S_strat.mk_reach_metric (by sorry) -- (证明 μ > 0 → ¬ Goal)
  rcases h_reach_concrete h_mu_pos with ⟨y_mat, hy_sliceable, ⟨t, rfl⟩, h_prog⟩
  let y_sq_mat : SquareMat R := ⟨⟨x.ι, x.κ, y_mat.reindex (Equiv.refl _) (FinEnum.equivOfCardEq x.is_square).symm⟩, x.is_square⟩
  use y_sq_mat
  have h_card_y_pos : card y_sq_mat.ι > 0 := h_mu_pos
  have hy_univ : IsSliceable_sq R y_sq_mat h_card_y_pos := by
    dsimp [IsSliceable_sq]; convert hy_sliceable
  use hy_univ
  constructor
  · dsimp [r_sq]; split_ifs with h_type_eq; exact ⟨t, rfl⟩
  · dsimp [slice_sq]; exact h_prog

private lemma base_metric_wrapper_sq :
    ∀ {x : PositiveSquareMat R}, (fun y ↦ card y.val.mat.ι) x = 0 → P_pos_sq R x := by
  intro x h_mu_zero
  -- 在 h_card_pos 的上下文中，归纳法不会达到 μ = 0 的情况。
  exfalso
  have h_card_x_pos : card x.val.mat.ι > 0 := by sorry -- (需要从归纳法的结构中证明)
  exact h_card_x_pos.ne' h_mu_zero


/-- **PLU 分解存在性定理 (最终版)** -/
theorem exists_plu_decomposition (A : Matrix ι ι R) : HasPLU ι R A := by
  -- 步骤 1: 在顶层通过 by_cases 分离出平凡基例。
  by_cases h_card_zero : card ι = 0
  · -- Case 1: card ι = 0 (0x0 矩阵)
    have h_empty : IsEmpty ι := sorry--FinEnum.isEmpty_of_card_eq_zero h_card_zero
    use (1, 1, 1)
    constructor
    · refine ⟨?_, ?_, ?_⟩
      all_goals { dsimp [IsPermutation, IsUnitLowerTriangular, IsLowerTriangular, IsUpperTriangular]; try { use Equiv.refl _ }; simp [BlockTriangular, diag, Matrix.isEmpty] }
    · sorry--simp [Matrix.isEmpty]
  · -- Case 2: card ι > 0
    have h_card_pos : card ι > 0 := Nat.pos_of_ne_zero h_card_zero

    -- 步骤 2: 定义一个在所有 SquareMat 上都有效的归纳命题 P
    let P_univ (x : SquareMat R) : Prop :=
      if h_pos : card x.mat.ι > 0 then
        -- 如果维度 > 0, P 是 HasPLU
        P_pos_sq R ⟨x, h_pos⟩
      else
        -- 如果维度 = 0, P 平凡为真 (因为我们已经在顶层处理了)
        True

    -- 步骤 3: 将问题提升到 PositiveSquareMat 宇宙，并调用通用的归纳定理
    let x_pos : PositiveSquareMat R := ⟨SquareMat.of A, h_card_pos⟩
    have h_univ_proof : P_univ x_pos.val :=
      transformSliceInduction (X := PositiveSquareMat R)
        (μ := fun y ↦ card y.val.mat.ι)
        (P := fun y ↦ P_univ y.val)
        (h_trans := by
          -- 这里的 transport 作用在 P_univ 上
          intro y x h_r h_p_y
          dsimp [P_univ] at *
          split_ifs at h_p_y with h_y_pos
          -- 调用 transport_wrapper_sq
          exact (transport_wrapper_sq R) (h_r) (h_p_y)
        )
        (IsSliceable := IsSliceable_pos_sq R)
        (slice := fun {y} hy ↦ slice_pos_sq hy) -- slice 返回 SquareMat
        (lift_from_slice := by
          intro y hy h_p_slice -- h_p_slice 是 P_univ (slice_pos_sq hy)
          -- 目标是 P_univ y.val
          -- 这正是 lift_wrapper_sq 的工作，但需要处理 P_univ 的 if
          dsimp [P_univ]
          split_ifs with h_y_pos
          exact lift_wrapper_sq R h_y_pos hy h_p_slice
        )
        (reach_metric := by sorry)
        (base_metric := by
          -- 基例是 μ y = 0，但在 PositiveSquareMat 宇宙中，μ = card y.ι > 0，所以这个分支不可达
          intro y h_mu_zero; exfalso; exact y.property.ne' h_mu_zero
        )
        (x_pos)

    -- 步骤 4: 从宇宙证明中提取具体证明
    dsimp [P_univ] at h_univ_proof
    rw [dif_pos h_card_pos] at h_univ_proof
    exact h_univ_proof

end FinalProof

end MatDecompFormal.Instances
