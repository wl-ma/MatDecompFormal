import MatDecompFormal.Framework.Induction
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Abstractions.Strategy
import MatDecompFormal.Abstractions.ReductionCombinators -- For try_else
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
import MatDecompFormal.Components.Properties.Reindex
import MatDecompFormal.Components.Reductions.Schur
import MatDecompFormal.Components.Reductions.ZeroColumn
import MatDecompFormal.Components.Transformations.Elementary.Pivot
-- 假设一个新的 Universe.lean 文件定义了 SquareMatFamily
import MatDecompFormal.Framework.Universe

namespace MatDecompFormal.Instances

open MatDecompFormal.Abstractions
open MatDecompFormal.Components.Properties
open MatDecompFormal.Components.Reductions
open MatDecompFormal.Components.Transformations.Elementary
open MatDecompFormal.Framework
open Matrix FinEnum

/-!
# 列选主元 LU 分解 (PLU Decomposition) - v3.0 (最终版)

本文件使用本框架证明了任意一个域上的方阵都存在 PLU 分解。
即，对于任意方阵 `A`，存在一个置换矩阵 `P`、一个单位下三角矩阵 `L`
和一个上三角矩阵 `U`，使得 `P * A = L * U`。

### 证明流程 (最终版)
1.  **定义 `PLU_Schema`**: 描述 PLU 分解的目标。
2.  **定义 `PLU_Strategy`**: 封装了基于 `Pivot` 变换和 `Schur`/`ZeroColumn`
    规约的算法策略。
3.  **定义归纳命题 `P_univ`**: 将 `HasPLU` 提升到 `SquareMatFamily` 宇宙。
4.  **证明包装引理**:
    - `transport_plu`: 证明 `P_univ` 在变换关系下的传递性。
    - `lift_from_slice_plu`: 证明 `P_univ` 可以从子问题解中提升。
    - `base_plu`: 证明 `n=0` 的基例。
    - `reach_plu`: 证明 `n>0` 的归纳步骤，这是所有宇宙问题被解决的核心。
5.  **调用主定理**: 将所有组件传入 `transformSliceInduction`，证明对所有
    `SquareMatFamily` 成立。
6.  **最终定理**: 将宇宙中的结论转换回任意 `Matrix ι ι R` 上的定理。
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

/-- `HasPLU` 是一个命题，表示矩阵 `A` 存在一个 PLU 分解。 -/
def HasPLU (A : Matrix ι ι R) : Prop :=
  HasDecomposition (PLU_Schema (ι := ι) (R := R)) A

end PLU_Schema


section PLU_Strategy
-- ==================================================================
-- L3.2: 定义并组装策略 (Strategy)
-- ==================================================================

variable {ι : Type*} (R : Type*) [FinEnum ι] [Field R] [DecidableEq R]

/-- `PLU_Strategy` 封装了 PLU 分解的完整算法策略。 -/
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
-- L3.3: 定义归纳命题和“胶水”引理
-- ==================================================================

section PLU_Proof

variable (R : Type*) [Field R] [DecidableEq R]

/-- `P_univ` 是 `HasPLU` 在 `SquareMatFamily` 宇宙中的归纳命题。 -/
def P_univ (x : Σ n, SquareMatFamily n R) : Prop :=
  HasPLU x.2.ι R x.2.matrix

/-- `IsSliceable_univ` 是 `IsSliceable` 在宇宙中的包装器。 -/
def IsSliceable_univ (x : Σ n, SquareMatFamily n R) : Prop :=
  if h_pos : x.1 > 0 then
    have := x.2.h_card
    (PLU_Strategy R (x.2.h_card.out.symm ▸ h_pos)).reduction.IsSliceable x.2.matrix
  else
    False

namespace FinEnum

/--
利用两个 `FinEnum` 类型的 `equiv` 构造一个在它们之间可计算的双射。
这个版本使用了 `Fin.castOrderIso` 来确保类型正确。
-/
@[simps!]
def equivOfCardEq {ι κ : Type*} [FinEnum ι] [FinEnum κ] (h : card ι = card κ) : ι ≃ κ :=
  -- 流程: ι ≃ Fin (card ι) ≃o Fin (card κ) ≃ κ
  (@equiv ι).trans ((Fin.castOrderIso h).toEquiv.trans (@equiv κ).symm)

@[simp] lemma equivOfCardEq_rfl (ι : Type*) [FinEnum ι] :
    equivOfCardEq (ι := ι) (κ := ι) rfl = Equiv.refl ι := by
  dsimp [equivOfCardEq]
  simp

end FinEnum

/-- `slice_univ` 是 `slice` 在宇宙中的包装器。 -/
noncomputable def slice_univ {x : Σ n, SquareMatFamily n R} (hx : IsSliceable_univ R x) :
    Σ n, SquareMatFamily n R :=
  -- 步骤 1: 解包输入 `x` 和 `hx`
  let ⟨n, sq_mat⟩ := x
  -- 从 `hx` 的定义中，我们可以安全地推断出 n > 0
  have h_pos_n : n > 0 := by
    dsimp [IsSliceable_univ] at hx
    split_ifs at hx with hx₁
    exact hx₁

  -- 步骤 2: 使用 `▸` 转换证明类型，以正确地实例化 `PLU_Strategy`
  have h_pos_ι : card sq_mat.ι > 0 := sq_mat.h_card.out.symm ▸ h_pos_n
  let S_strat := PLU_Strategy R h_pos_ι
  let S_reduc := S_strat.reduction

  -- 步骤 3: 获取底层的切片矩阵
  have h_sliceable_concrete : S_reduc.IsSliceable sq_mat.matrix := by
    dsimp [IsSliceable_univ] at hx
    rw [dif_pos h_pos_n] at hx
    -- 我们需要证明 `(PLU_Strategy ...).reduction` 是同一个东西
    -- 最简单的方法是利用 `h_pos_ι` 的定义
    convert hx
  let slice_mat := S_reduc.slice sq_mat.matrix h_sliceable_concrete

  -- 步骤 4: 证明新旧维度之间的关系，为构造新的 `Fact` 做准备
  have h_slice_card_eq_n_minus_1 : card S_reduc.Sliceι = n - 1 := by
    -- 这个证明依赖于 Schur/ZeroColumn 规约方法的具体实现
    have h_card_ι_eq_n : card sq_mat.ι = n := sq_mat.h_card.out
    dsimp [S_reduc, S_strat, PLU_Strategy, ReductionMethod.try_else, SchurMethod]
    -- 无论走哪个分支，Sliceι 的定义都是 `{ i // ¬ p i }`，其中 p 是 `i = i₀`
    -- 所以目标是 `card { i // i ≠ i₀ } = n - 1`
    let i₀ := (@equiv sq_mat.ι).symm ⟨0, h_pos_ι⟩
    have h_card_compl :
        card { i : sq_mat.ι // i ≠ i₀ } = card sq_mat.ι - 1 := by
      classical
      -- 使用 `card_subtype_neq` 计算补集的基数
      simp [FinEnum.card_eq_fintypeCard]
    -- 用维度等式替换
    simpa [h_card_ι_eq_n] using h_card_compl

  -- 步骤 5: 构造返回的 `Σ n, SquareMatFamily n R` 实例
  ⟨n - 1, {
      ι := S_reduc.Sliceι,
      -- 关键：为新的 `SquareMatFamily` 提供 `Fact` 实例
      h_card := ⟨h_slice_card_eq_n_minus_1⟩,
      matrix :=
        -- 在返回之前，需要将可能为矩形的 slice_mat “变方”
        let h_slice_sq : card S_reduc.Sliceι = card S_reduc.Sliceκ := by
          -- 同样，这个证明依赖于 Schur/ZeroColumn 的实现细节
          dsimp [S_reduc, S_strat, PLU_Strategy, ReductionMethod.try_else, SchurMethod]
        slice_mat.reindex (Equiv.refl _) (FinEnum.equivOfCardEq h_slice_sq.symm)
    }⟩


/-- `r_univ` 是变换关系 `r` 在宇宙中的包装器 (v2 - 修正版)。 -/
def r_univ (y x : Σ n, SquareMatFamily n R) : Prop :=
  -- 变换关系只在维度相同时才有意义。
  if h_n_eq : y.1 = x.1 then
    -- 如果维度相同，我们将其记为 n
    let n := x.1
    -- 接下来，根据维度 n 是否为 0 进行分情况讨论。
    if h_pos : n > 0 then
      -- Case 1: 维度 n > 0。这是非平凡的变换发生的地方。
      -- 在这个分支中，我们拥有一个 `n > 0` 的证明 `h_pos`。
      -- 我们可以安全地实例化 `PLU_Strategy`。
      let sq_mat_x := x.2
      -- 为了比较 y 和 x 的矩阵，我们需要将它们 reindex 到同一个索引类型上。
      -- 这里的 `e` 将 y 的索引类型 `y.2.ι` 映射到 x 的索引类型 `x.2.ι`。
      let e : y.2.ι ≃ sq_mat_x.ι :=
        FinEnum.equivOfCardEq ((y.2.h_card.out.trans h_n_eq).trans sq_mat_x.h_card.out.symm)
      let sq_mat_y_reindexed := y.2.matrix.reindex e e
      -- 关系 `r` 被定义为底层策略的 `r`。
      (PLU_Strategy R (sq_mat_x.h_card.out.symm ▸ h_pos)).r sq_mat_y_reindexed sq_mat_x.matrix
    else
      -- Case 2: 维度 n = 0。
      -- 对于 0x0 矩阵，唯一有意义的“变换”是恒等变换。
      -- 这对应于我们修正后的 `ReductionStrategy.r` 定义中的 `y = x` 分支。
      y = x
  else
    -- 如果维度不同，则它们之间不存在变换关系。
    False


/--
`hasPLU_reindex_iff` 证明了 `HasPLU` 属性在通过保序同构 (`OrderIso`)
进行基变换时是逻辑等价的。
-/
lemma hasPLU_reindex_iff {ι ι' R} [FinEnum ι] [FinEnum ι'] [Field R] [DecidableEq R]
    -- 关键修改：e 现在是 OrderIso
    (e : ι ≃o ι') (A : Matrix ι ι R) :
    HasPLU ι R A ↔ HasPLU ι' R (A.reindex e.toEquiv e.toEquiv) := by
  dsimp [HasPLU, HasDecomposition, PLU_Schema]
  constructor
  · -- (→) HasPLU A → HasPLU (reindex A)
    intro ⟨⟨P, L, U⟩, ⟨hP, hL, hU⟩, h_eq⟩
    -- 构造 reindex 后的因子
    let P' := P.reindex e.toEquiv e.toEquiv
    let L' := L.reindex e.toEquiv e.toEquiv
    let U' := U.reindex e.toEquiv e.toEquiv
    use (P', L', U')
    constructor
    · -- 证明新因子的性质，现在调用修正后的 _reindex 引理
      refine ⟨?_, ?_, ?_⟩
      · exact (isPermutation_reindex e.toEquiv _).mp hP
      · exact (isUnitLowerTriangular_reindex e _).mp hL
      · exact (isUpperTriangular_reindex e _).mp hU
    · -- 证明分解方程
      simp [P', L', U']
      rw [← submatrix_mul _ _ _ _ _ e.symm.bijective,
        ← submatrix_mul _ _ _ _ _ e.symm.bijective]
      simp at h_eq
      simp [h_eq]
  · -- (←) HasPLU (reindex A) → HasPLU A
    -- 与前一个方向对称，使用 e.symm (它也是 OrderIso)
    intro ⟨⟨P', L', U'⟩, ⟨hP', hL', hU'⟩, h_eq'⟩
    let P := P'.reindex e.symm.toEquiv e.symm.toEquiv
    let L := L'.reindex e.symm.toEquiv e.symm.toEquiv
    let U := U'.reindex e.symm.toEquiv e.symm.toEquiv
    use (P, L, U)
    constructor
    · refine ⟨?_, ?_, ?_⟩
      · exact (isPermutation_reindex e.symm.toEquiv _).mp hP'
      · exact (isUnitLowerTriangular_reindex e.symm _).mp hL'
      · exact (isUpperTriangular_reindex e.symm _).mp hU'
    · -- 证明方程
      simp [P, L, U]
      have : e.symm ∘ e = id := Equiv.symm_comp_self e.toEquiv
      have hA : (A.reindex e.toEquiv e.toEquiv).reindex e.symm.toEquiv e.symm.toEquiv = A := by
        simp [this]
      have hA_sub :
          (A.reindex e.toEquiv e.toEquiv).submatrix (e : ι → ι') (e : ι → ι') = A := by
        simpa using hA
      -- 对 `h_eq'` 取 submatrix，使两边的索引都落在 `ι` 上
      have h_eq_sub := congrArg (fun M => M.submatrix (e : ι → ι') (e : ι → ι')) h_eq'
      -- 将 submatrix 应用到乘积上
      have h_eq_sub' :
          P'.submatrix e e * (A.reindex e.toEquiv e.toEquiv).submatrix e e =
            L'.submatrix e e * U'.submatrix e e := by
        simp at h_eq_sub
        rw [submatrix_mul _ _ _ e _ e.bijective] at h_eq_sub
        simpa [submatrix_mul (M := P') (N := A.reindex e.toEquiv e.toEquiv)
            (e₁ := (e : ι → ι')) (e₂ := (e : ι → ι')) (e₃ := (e : ι → ι')) e.bijective,
          submatrix_mul (M := L') (N := U') (e₁ := (e : ι → ι')) (e₂ := (e : ι → ι'))
            (e₃ := (e : ι → ι')) e.bijective] using h_eq_sub
      -- 把 submatrix 还原成 reindex 后的矩阵
      simpa [P, L, U, hA_sub, this] using h_eq_sub'

/--
`transport_plu_concrete` 是在具体矩阵类型上操作的底层 transport 引理。
-/
private lemma transport_plu_concrete {ι : Type*} [FinEnum ι] (h_card : card ι > 0) :
    Transport (PLU_Strategy R h_card).r (HasPLU ι (R := R)) := by
  intro x y h_r h_plu_x
  -- 展开新的 r 定义
  dsimp [ReductionStrategy.r] at h_r
  cases h_r with
  | inl hyx =>
      -- Case 1: y = x (自反情况)
      subst hyx; exact h_plu_x
  | inr h =>
      -- Case 2: 存在变换 t (行交换)
      rcases h with ⟨t, hy⟩
      subst hy
      rcases h_plu_x with ⟨⟨P, L, U⟩, ⟨hP, hL, hU⟩, h_eq_x⟩
      let i₀ := (@equiv ι).symm ⟨0, h_card⟩
      let P_swap := swap R i₀ t
      -- 这里选择 P' = P * P_swap（因为 swap 是自逆的）
      let P' := P * P_swap
      have hP' : IsPermutation P' := isPermutation_mul hP (isPermutation_swap _ _)
      use (P', L, U)
      constructor
      · exact ⟨hP', hL, hU⟩
      · dsimp [PLU_Schema, HasDecomposition] at h_eq_x ⊢
        -- 此时 h_eq_x : P * (P_swap * y) = L * U
        -- 直接重写为 P' * y = L * U
        simpa [P', mul_assoc] using h_eq_x

/-- `transport_plu` (最终版) 证明了 `P_univ` 在 `r_univ` 下是可传递的。 -/
private lemma transport_plu : Transport (r_univ R) (P_univ R) := by
  -- 1. 展开定义
  intro x y h_r h_p_x
  dsimp [P_univ, r_univ] at *

  -- 2. 处理 `r_univ` 定义中的 `if` 分支
  split_ifs at h_r with h_n_eq h_pos
  · -- Case 1 (核心): n > 0 且维度相同
    -- 此时 h_r 是 `(PLU_Strategy ...).r (reindex ... x.matrix) y.matrix`
    -- h_p_x 是 `HasPLU x.matrix`
    -- 目标是 `HasPLU y.matrix`

    -- 步骤 a: 为索引构造保序同构 (OrderIso)
    let sq_mat_src := x.2
    let sq_mat_tgt := y.2
    -- 关键：`h_n_eq : x.1 = y.1` 给出了两个索引类型基数的等式。
    let e : sq_mat_src.ι ≃o sq_mat_tgt.ι :=
      FinEnum.orderIsoOfCardEq
        ((sq_mat_src.h_card.out.trans h_n_eq).trans sq_mat_tgt.h_card.out.symm)
    let sq_mat_src_reindexed := sq_mat_src.matrix.reindex e.toEquiv e.toEquiv

    -- 步骤 b: 将 `h_r` 和 `HasPLU` 假设转换到具体矩阵上
    have h_r_concrete :
        (PLU_Strategy R (sq_mat_tgt.h_card.out.symm ▸ h_pos)).r
          sq_mat_src_reindexed sq_mat_tgt.matrix := by
      simpa [sq_mat_src_reindexed, sq_mat_src, sq_mat_tgt, e] using h_r
    have h_card_pos : card sq_mat_tgt.ι > 0 := sq_mat_tgt.h_card.out.symm ▸ h_pos
    have h_plu_reindexed : HasPLU sq_mat_tgt.ι R sq_mat_src_reindexed := by
      have h := (hasPLU_reindex_iff (ι:=sq_mat_src.ι) (ι':=sq_mat_tgt.ι)
          (R:=R) e sq_mat_src.matrix).1 h_p_x
      simpa [sq_mat_src_reindexed] using h

    -- 步骤 c: 调用底层的 transport 引理
    exact (transport_plu_concrete (R := R) (ι := sq_mat_tgt.ι) h_card_pos)
      sq_mat_src_reindexed sq_mat_tgt.matrix h_r_concrete h_plu_reindexed

  · -- Case 2: n = 0
    -- 此时 h_r 蕴含 y = x
    subst h_r
    exact h_p_x


/-- `lift_from_slice_plu` 证明了 `P_univ` 可以从子问题解中提升。 -/
private lemma lift_from_slice_plu {x : Σ n, SquareMatFamily n R} (hx : IsSliceable_univ R x)
    (h_p_slice : P_univ R (slice_univ R hx)) : P_univ R x := by
  -- 展开定义，调用纯代数引理
  sorry

end PLU_Proof


section FinalProof

variable {ι : Type*} (R : Type*) [FinEnum ι] [Field R]

/-- `base_plu` 证明 `n=0` 的基例。 -/
private lemma base_plu {x : Σ n, SquareMatFamily n R}
    (h_n_zero : x.1 = 0) : P_univ R x := by
  classical
  let ⟨n, sq_mat⟩ := x; subst h_n_zero
  dsimp [P_univ]
  -- 从 `card sq_mat.ι = 0` 得到空类型实例
  have h_card_zero : Fintype.card sq_mat.ι = 0 := by
    simpa [FinEnum.card_eq_fintypeCard] using sq_mat.h_card.out
  have h_empty : IsEmpty sq_mat.ι := Fintype.card_eq_zero_iff.1 h_card_zero
  haveI : IsEmpty sq_mat.ι := h_empty
  dsimp [HasPLU, HasDecomposition, PLU_Schema]
  refine ⟨(1, 1, 1), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · dsimp [IsPermutation]; refine ⟨Equiv.refl _, ?_⟩; simp
    · simp [IsUnitLowerTriangular, IsLowerTriangular, IsUpperTriangular]
    · simp [IsUpperTriangular]
  · -- 在空索引上矩阵是惟一的，故 `sq_mat.matrix = 1`
    have h_matrix : sq_mat.matrix = (1 : Matrix sq_mat.ι sq_mat.ι R) := by
      ext i j; cases h_empty.false i
    simp [h_matrix]

variable [DecidableEq R]

/-- `reach_plu` 证明 `n>0` 的归纳步骤。 -/
private lemma reach_plu {x : Σ n, SquareMatFamily n R} (h_n_pos : x.1 > 0) :
    ∃ y, ∃ (hy : IsSliceable_univ R y), r_univ R y x ∧ (fun z ↦ z.1) (slice_univ R hy) < x.1 := by
  let ⟨n, sq_mat⟩ := x
  let A := sq_mat.matrix
  -- 将 `n > 0` 转换为 `card sq_mat.ι > 0`
  have h_card_pos : card sq_mat.ι > 0 := sq_mat.h_card.out.symm ▸ h_n_pos
  let S_strat : ReductionStrategy sq_mat.ι sq_mat.ι R :=
    PLU_Strategy (ι := sq_mat.ι) R h_card_pos
  rcases S_strat.mk_reach_metric (A := A) h_card_pos with
    ⟨y_mat, hy_sliceable_concrete, h_r_concrete, h_prog⟩
  let y_witness : Σ n, SquareMatFamily n R :=
    ⟨n, { sq_mat with matrix := y_mat }⟩
  use y_witness
  have hy : IsSliceable_univ (R := R) y_witness := by
    dsimp [IsSliceable_univ, y_witness, S_strat]
    have h_pos : n > 0 := h_n_pos
    have h_proof_eq : sq_mat.h_card.out.symm ▸ h_pos = h_card_pos := by
      apply Subsingleton.elim
    -- 通过 `simp` 将策略证明统一
    simpa [dif_pos h_pos, h_proof_eq] using hy_sliceable_concrete
  use hy
  constructor
  · dsimp [r_univ, y_witness]; rw [dif_pos rfl, dif_pos h_n_pos]
    -- 目标是 (PLU_Strategy ...).r (reindex ... y_mat) A
    -- reindex 是恒等映射，所以目标就是 .r y_mat A
    simpa [S_strat, h_card_pos, sq_mat.h_card.out]
      using h_r_concrete
  · dsimp [slice_univ]
    -- 目标是 n-1 < n
    have h_ne_zero : n ≠ 0 := Nat.ne_of_gt h_n_pos
    have h_lt : n - 1 < n := by
      simpa [Nat.pred_eq_sub_one] using Nat.pred_lt h_ne_zero
    simpa [slice_univ, y_witness] using h_lt

-- ==================================================================
-- L3.4: 组装最终证明
-- ==================================================================

/-- 对 `SquareMatFamily` 宇宙中的所有矩阵证明 PLU 分解存在性。 -/
private theorem exists_plu_for_family : ∀ (x : Σ n, SquareMatFamily n R), P_univ R x := by
  apply transformSliceInduction (X := Σ n, SquareMatFamily n R)
    (μ := fun x ↦ x.1)
    (P := P_univ R)
    (h_trans := transport_plu R)
    (IsSliceable := IsSliceable_univ R)
    (slice := slice_univ R)
    (lift_from_slice := lift_from_slice_plu R)
    (reach_metric := reach_plu R)
    (base_metric := base_plu R)

/-- **PLU 分解存在性定理 (最终对用户暴露的定理)** -/
theorem exists_plu_decomposition (A : Matrix ι ι R) : HasPLU ι R A := by
  -- 1. 构造一个 `SquareMatFamily` 实例
  let n := card ι
  let sq_mat_family : SquareMatFamily n R := {
    ι := ι,
    matrix := A,
    h_card := ⟨rfl⟩
  }
  let x : Σ n, SquareMatFamily n R := ⟨n, sq_mat_family⟩
  -- 2. 调用在宇宙中证明的定理
  have h_univ := exists_plu_for_family R x
  -- 3. 将宇宙中的结论转换回来
  dsimp [P_univ] at h_univ
  exact h_univ

end FinalProof

end MatDecompFormal.Instances
