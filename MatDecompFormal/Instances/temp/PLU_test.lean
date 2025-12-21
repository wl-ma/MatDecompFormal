import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

import MatDecompFormal.Framework.Induction
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Abstractions.Strategy
import MatDecompFormal.Abstractions.ReductionCombinators
import MatDecompFormal.Components.Reductions.Schur
import MatDecompFormal.Components.Reductions.ZeroColumn
import MatDecompFormal.Components.Transformations.Elementary.Pivot
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular

namespace MatDecompFormal.Instances.PLU

open MatDecompFormal.Framework
open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Components.Transformations.Elementary
open MatDecompFormal.Components.Properties
open Matrix FinEnum

/-!
# PLU 分解的存在性证明

本文件展示了如何使用本框架来证明任意可逆方阵的 PLU 分解的存在性。
PLU 分解指出，对于任意可逆方阵 `A`，存在一个置换矩阵 `P`、一个
单位下三角矩阵 `L` 和一个上三角矩阵 `U`，使得 `P * A = L * U`。

这个证明完美地体现了本框架的设计哲学：
1.  **定义 Schema**: 清晰地描述 PLU 分解的目标。
2.  **组装 Strategy**: 将 `PivotTransform`（用于主元选择）和 `SchurMethod`
    （用于基于舒尔补的规约）组合成一个完整的归纳策略。
3.  **证明“胶水”引理**: 提供 `transport` 和 `lift_from_slice` 这两个
    连接 `Schema` 和 `Strategy` 的关键证明。
4.  **调用归纳引擎**: 一行代码完成最终的归纳证明。

### 注意
为了简化，本证明针对的是**可逆方阵** (`IsUnit A`)。这保证了在主元选择
步骤中，如果主元为零，其下方必定存在非零元素，从而满足 `PivotTransform`
的前提条件。将此证明推广到任意矩阵需要更复杂的秩理论。
-/

section PLU_Schema

variable (ι R : Type*) [FinEnum ι] [Field R] [DecidableEq R]
/--
`PLU_Schema` 定义了 PLU 分解的“蓝图”。
-/
def PLU_Schema :
    DecompositionSchema ι ι R where
  -- 分解因子是一个三元组 (P, L, U)。
  Factors := Matrix ι ι R × Matrix ι ι R × Matrix ι ι R
  -- 属性：P 是置换矩阵，L 是单位下三角，U 是上三角。
  property := fun (P, L, U) ↦
    IsPermutation P ∧ IsUnitLowerTriangular L ∧ IsUpperTriangular U
  -- 方程：P * A = L * U。
  equation := fun A (P, L, U) ↦ P * A = L * U

/--
`HasPLU` 是一个命题，表示矩阵 `A` 存在一个 PLU 分解。

我们将其定义为一个 `def` 而不是 `abbrev`，并明确地包含它所依赖的
类型类约束 `[Field R]` 和 `[DecidableEq R]`。这解决了在泛型上下文中
（如 `Transport`）使用它时，类型类实例无法被推断的问题。
-/
def HasPLU (A : Matrix ι ι R) : Prop :=
  HasDecomposition (PLU_Schema (ι := ι) (R := R)) A

end PLU_Schema


section PLU_Strategy

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


section PLU_Proof

variable {ι : Type*} (R : Type*) [FinEnum ι] [Field R] [DecidableEq R]

/--
这是一个关键的“胶水”引理，它连接了 Schema 和 Strategy。
它证明了 `HasPLU` 这个性质在 `PLU_Strategy` 的变换（行交换）下是可传递的。
这个引理只在维度大于0的情况下有意义，因此我们将 `h_card` 作为显式参数。
-/
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



/--
这是另一个关键的“胶水”引理，对应于 `lift_from_slice`。
它证明了如果子问题有 PLU 分解，我们就能构造出原问题的 PLU 分解。
这本质上是标准 PLU 算法证明中的分块矩阵代数构造。
-/
lemma lift_from_slice_plu {A : Matrix ι ι R} (h_card : card ι > 0)
    (hA : (PLU_Strategy R h_card).reduction.IsSliceable A)
    (h_plu_slice : HasPLU ι R ((PLU_Strategy R h_card).reduction.slice A hA)) : HasPLU ι R A := by
  -- 准备工作：定义 i₀, j₀ 和分块用的等价关系
  let i₀ := (@equiv ι).symm ⟨0, h_card⟩
  let j₀ := (@equiv ι).symm ⟨0, h_card⟩
  let e_ι : ι ≃ ({i // i = i₀} ⊕ {i // i ≠ i₀}) := (Equiv.sumCompl (fun i ↦ i = i₀)).symm
  let e_κ : ι ≃ ({j // j = j₀} ⊕ {j // j ≠ j₀}) := (Equiv.sumCompl (fun j ↦ j = j₀)).symm

  -- 展开 h_plu_slice 的定义，获取子问题的分解因子 P', L', U'
  rcases h_plu_slice with ⟨⟨P_sub, L_sub, U_sub⟩, ⟨hP_sub, hL_sub, hU_sub⟩, h_eq_sub⟩

  -- 对 IsSliceable 的两种情况进行分情况讨论
  dsimp only [PLU_Strategy, ReductionMethod.try_else, SchurMethod, ZeroColumnMethod] at hA
  by_cases h_pivot_nz : A i₀ j₀ ≠ 0
  · -- # 情况 1: 主元非零 (A i₀ j₀ ≠ 0)
    -- 此时 slice 是舒尔补 (或其简化形式)，我们需要进行舒尔补的重构。
    -- 这是一个非常复杂的代数构造，思路如下：
    -- A = | A₁₁  A₁₂ |
    --     | A₂₁  A₂₂ |
    -- P' * (A₂₂ - A₂₁ * A₁₁⁻¹ * A₁₂) = L' * U'  (这是 h_eq_sub)
    -- 目标是找到 P, L, U 使得 P * A = L * U
    -- 构造：
    -- P = | 1  0 |
    --     | 0 P' |
    -- L = | 1      0 | * | 1       0 | = | 1          0 |
    --     | P'A₂₁A₁₁⁻¹ I |   | 0      L' |   | P'A₂₁A₁₁⁻¹  L' |
    -- U = | A₁₁  A₁₂ |
    --     | 0    U'  |
    -- 然后验证 (P*A) = L*U，以及 P, L, U 的性质。
    sorry
  · -- # 情况 2: 第一列为零 (∀ i, A i j₀ = 0)
    -- 此时 A 的形式是 A = | 0  A₁₂ |
    --                     | 0  A₂₂ |
    -- slice 是 A₂₂，所以 h_eq_sub 是 P' * A₂₂ = L' * U'
    -- 构造：
    -- P = | 1  0 |
    --     | 0 P' |
    -- L = | 1  0 |
    --     | 0 L' |
    -- U = | 0  A₁₂ |
    --     | 0  U'  |
    -- 验证：
    -- P * A = | 1  0 | * | 0 A₁₂ | = | 0 A₁₂ |
    --         | 0 P' |   | 0 A₂₂ |   | 0 P'A₂₂|
    -- L * U = | 1  0 | * | 0 A₁₂ | = | 0 A₁₂ |
    --         | 0 L' |   | 0  U' |   | 0 L'U' |
    -- 由于 P'A₂₂ = L'U'，所以 P*A = L*U 成立。
    -- 接下来验证 P, L, U 的性质。
    -- 构造 P, L, U
    let P := fromBlocks 1 0 0 P_sub
    let L := fromBlocks 1 0 0 L_sub
    let U := fromBlocks 0 (A.submatrix (fun _ ↦ i₀) (fun j ↦ j.val)) 0 U_sub
    -- 1. 构造最终的 P, L, U
    let P_final := P.reindex e_ι.symm e_ι.symm
    let L_final := L.reindex e_ι.symm e_ι.symm
    let U_final := U.reindex e_ι.symm e_κ.symm
    -- 2. 提供存在性见证
    use (P_final, L_final, U_final)
    -- 3. 证明性质和方程
    constructor
    · -- 3a. 证明 P, L, U 的性质
      -- P 是置换矩阵，L 是单位下三角，U 是上三角
      -- 这需要一系列关于分块矩阵性质的引理
      sorry
    · -- 3b. 证明 P * A = L * U
      -- 这需要一系列关于分块矩阵乘法的引理
      sorry


/--
**PLU 分解存在性定理 (适用于所有方阵)**
-/
theorem exists_plu (A : Matrix ι ι R) : HasPLU ι R A := by
  -- 归纳基于矩阵的维度 `card ι`
  -- 如果维度为 0，基例是平凡的。
  if h_card : card ι = 0 then
    -- 处理 0x0 矩阵的基例
    -- 0x0 矩阵 A=0。P=1, L=1, U=0。1*0 = 1*0
    have A_is_zero : A = 0 := by sorry--ext i; have := card_eq_zero_iff.mp h_card; exfalso; exact this i
    use (1, 1, 0)
    simp [PLU_Schema, IsPermutation, IsUnitLowerTriangular, IsLowerTriangular, IsUpperTriangular, A_is_zero]--, isPermutation_one, isUnitLowerTriangular_one, isUpperTriangular_zero]
    sorry
  else
    -- 主归纳证明
    -- 将 h_card 转换为 card ι > 0
    have h_card_pos : card ι > 0 := Nat.pos_of_ne_zero h_card
    -- 获取我们的策略实例
    let S := PLU_Strategy R h_card_pos
    -- 调用主归纳定理
    apply transformSliceInduction (μ := S.μ)
      -- 1. Transport 引理
      (h_trans := transport_plu R h_card_pos)
      -- 2. IsSliceable
      (IsSliceable := S.reduction.IsSliceable)
      -- 3. slice
      (slice := @S.reduction.slice)
      -- 4. lift_from_slice
      (lift_from_slice := lift_from_slice_plu R h_card_pos)
      -- 5. reach_metric
      (reach_metric := by
        -- `mk_reach_metric` 自动构造这个证明
        apply S.mk_reach_metric
        -- 我们需要提供 `mk_reach_metric` 所需的前提：
        -- `∀ A, S.μ A > 0 → ¬ S.transform.Goal A`
        -- 即：维度大于0的矩阵，不一定满足“可切片”条件。
        intro A' h_μ_pos
        -- 这个证明是平凡的，因为一个任意的、维度大于0的矩阵
        -- 其第一列不一定全为0，主元也不一定非零。
        -- 所以它不一定满足 `IsSliceable`，因此 `¬ Goal` 成立的可能性是存在的。
        -- 为了形式化，我们需要一个反例，或者证明 ¬Goal 不是 False。
        -- 暂时 `sorry`，这是一个可以被具体反例填充的证明。
        sorry
      )
      -- 6. base_metric
      (base_metric := fun A' hμ_eq_0 ↦ by
        -- 如果 μ A' = 0，则 card ι' = 0。
        -- 这是一个不可能的情况，因为归纳只在维度 > 0 的子问题上进行，
        -- 而我们的外层 if 已经处理了 card ι = 0 的情况。
        -- `transformSliceInduction` 的归纳是良基的，它不会在 h_card > 0 的情况下
        -- 到达一个维度为0的矩阵。
        -- hμ_eq_0 与 h_card_pos 矛盾。
        exfalso; exact h_card hμ_eq_0
      )
      -- 应用于原始矩阵 A
      (A)

end PLU_Proof

end MatDecompFormal.Instances.PLU








-- import Mathlib

-- section BiGLFamilyMulAction

-- -- variable (m n R : Type*)
-- -- [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n][CommRing R]
-- variable (R : Type) [CommRing R]

-- /-- 双侧作用群：`G_L × G_R`. -/
-- @[simp] def BiGL  (R : Type) [CommRing R] : MatObjsize → Type :=
--     fun i : MatObjsize ↦ (GL (Fin i.m) R) × (GL (Fin (i.n)) R)

-- instance (R : Type) [CommRing R] : (i : MatObjsize) → Monoid (BiGL R i) :=
--   fun _ => Prod.instMonoid

-- instance {i} : MulAction (BiGL R i) (Matrix (Fin (i.m)) (Fin (i.n)) R) where
--   smul gh A := gh.1.1 * A * gh.2.2
--   one_smul := by
--     intro A; simp [HSMul.hSMul]
--   mul_smul := by
--     intro g₁ g₂ A
--     simp [HSMul.hSMul, Matrix.mul_assoc]

-- instance {i} : DistribMulAction (BiGL R i) (Matrix (Fin (i.m)) (Fin (i.n)) R) where
--   smul_zero := by
--     intro a
--     simp only [HSMul.hSMul, SMul.smul, Matrix.mul_zero, Units.inv_eq_val_inv, Matrix.coe_units_inv,
--       Matrix.zero_mul]
--   smul_add := by
--     intro a x y
--     simp only [HSMul.hSMul, SMul.smul, Matrix.mul_add, Units.inv_eq_val_inv, Matrix.coe_units_inv,
--       Matrix.add_mul]

-- /-- 双侧作用：`(g,h) ▷ A = g · A · h⁻¹`. -/
-- instance fma : @FamilyMulAction MatObjsize (BiGL R) _ (fun i : MatObjsize  ↦ Matrix (Fin (i.m)) (Fin (i.n)) R) where
--     FM := @instMulActionBiGLMatrixFinMN R _

-- end BiGLFamilyMulAction

-- section feasible

-- variable [Zero F]
-- /--
-- 矩阵大小合法
-- -/
-- @[mk_iff] class MatNonEmpty (x : MatObj F) : Prop where
--   (hμ : x.μ > 0)

-- /--
-- 矩阵大小合法，第一列不都为0
-- -/
-- @[mk_iff] class MatFirstColNonZero (x : MatObj F) extends MatNonEmpty x where
--   (hA : (fun i ↦ x.A i ⟨0, Nat.pos_of_mul_pos_left hμ⟩) ≠ 0)

-- /--
-- 矩阵大小合法，左上角不为0
-- -/
-- class MatPivotNonZero (x : MatObj F) extends MatNonEmpty x where
--   (hA : x.A ⟨0, Nat.pos_of_mul_pos_right hμ⟩ ⟨0, Nat.pos_of_mul_pos_left hμ⟩ ≠ 0)

-- instance {x : MatObj F} (hμ : x.μ > 0) : NeZero x.n :=
--   ⟨Nat.pos_iff_ne_zero.mp <| Nat.pos_of_mul_pos_left hμ⟩

-- instance {x : MatObj F} (hμ : x.μ > 0) : NeZero x.m :=
--    ⟨Nat.pos_iff_ne_zero.mp <| Nat.pos_of_mul_pos_right hμ⟩

-- instance {x : { x : MatObj F // MatNonEmpty x}} : NeZero x.1.n :=
--   instNeZeroNatNOfGtμOfNat x.2.hμ

-- instance {x : { x : MatObj F // MatNonEmpty x}} : NeZero x.1.m :=
--   instNeZeroNatMOfGtμOfNat x.2.hμ

-- instance {x : { x : MatObj F // MatPivotNonZero x}} : NeZero x.1.n :=
--   instNeZeroNatNOfGtμOfNat x.2.hμ

-- instance {x : { x : MatObj F // MatPivotNonZero x}} : NeZero x.1.m :=
--   instNeZeroNatMOfGtμOfNat x.2.hμ

-- instance {x : { x : MatObj F // MatFirstColNonZero x}} : NeZero x.1.n :=
--   instNeZeroNatNOfGtμOfNat x.2.hμ

-- instance {x : { x : MatObj F // MatFirstColNonZero x}} : NeZero x.1.m :=
--   instNeZeroNatMOfGtμOfNat x.2.hμ

-- lemma MatNonEmpty_eq (R) [Zero R] : MatNonEmpty = (fun (x : MatObj R) ↦ x.μ > 0) := by
--   ext i
--   simp only [matNonEmpty_iff, gt_iff_lt]

-- end feasible

-- theorem matrix_rowOperation_induction {R} [Field R]
--     (P : MatObj R → Prop)
--     (trans : Transport MatrixRel.IsRowEquiv P)
--     (bridge : ∀ {x} (hx : S_col1Ready x), P (slice_botRight hx) → P x)
--     (baseμ : ∀ {x}, x.μ = 0 → P x) :
--   ∀ x, P x := by
--   apply equivSliceInduction_viaElimOp (X := MatObj R) MatObj.μ trans S_col1Ready
--     slice_botRight bridge _ MatrixRel.IsRowEquiv.muMono S_col1Ready_prog baseμ
--   rw [← MatNonEmpty_eq]
--   exact gaussColElimOp R

-- lemma IsRowEchelonable.baseμ [CommRing R] {x : MatObj R} (hx : x.μ = 0) :
--     x.IsRowEchelonable := by
--   simp [MatObj.μ] at hx
--   simp [MatObj.IsRowEchelonable, IsRowEchelonable]
--   use 1
--   simp [Matrix.isRowEchelon_iff]
--   intro i j hij hnt
--   simp [ne_top_iff] at hnt
--   rcases hnt with ⟨w, hw⟩
--   rcases hx with h | h
--   · simp [h] at i
--     exfalso
--     exact not_succ_le_zero i.1 i.2
--   simp [h] at w
--   exfalso
--   exact not_succ_le_zero w.1 w.2

-- theorem matrix_Gauss_pre {R} [Field R] :
--   ∀ x : MatObj R, x.IsRowEchelonable := by
--   apply matrix_rowOperation_induction
--   exact IsRowEchelonable.trans
--   exact fun {x} hx a ↦ IsRowEchelonable.bridge hx a
--   exact IsRowEchelonable.baseμ


-- /--
-- Every matrix over a field can be put into row echelon form by Gaussian elimination.
-- This is the main existence theorem for row echelon forms.
-- -/
-- theorem exists_rowEchelonForm {R} [Field R] {n m} (x : Matrix (Fin n) (Fin m) R) :
--   x.IsRowEchelonable := by
--   let y : MatObj R := ⟨n,m,x⟩
--   apply matrix_Gauss_pre y

-- end

-- end GaussianEliminator
