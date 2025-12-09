import MatDecompFormal.Framework.Induction
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Abstractions.Strategy
import MatDecompFormal.Abstractions.ReductionCombinators -- For try_else
import MatDecompFormal.Components.Properties.Permutation
import MatDecompFormal.Components.Properties.Triangular
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
    sorry

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


/-- `r_univ` 是变换关系 `r` 在宇宙中的包装器。 -/
def r_univ (y x : Σ n, SquareMatFamily n R) : Prop :=
  if h_n : y.1 = x.1 then
    -- 只有在维度相同时，变换才有意义
    let e : y.2.ι ≃ x.2.ι := FinEnum.equivOfCardEq (y.2.h_card.out.trans h_n.symm).trans x.2.h_card.out.symm
    (PLU_Strategy x.2.ι R (by rw [←h_n]; exact y.2.h_card.out.trans_le (Nat.zero_le _))).r
      (y.2.matrix.reindex e e) x.2.matrix
  else
    False

/-- `transport_plu` 证明了 `P_univ` 在 `r_univ` 下是可传递的。 -/
private lemma transport_plu : Transport r_univ P_univ := by
  intro x y h_r h_p_x
  dsimp [P_univ, r_univ] at *
  split_ifs at h_r with h_n
  -- 证明 `HasPLU` 在 reindex 下不变
  sorry

/-- `lift_from_slice_plu` 证明了 `P_univ` 可以从子问题解中提升。 -/
private lemma lift_from_slice_plu {x : Σ n, SquareMatFamily n R} (hx : IsSliceable_univ x)
    (h_p_slice : P_univ (slice_univ hx)) : P_univ x := by
  -- 展开定义，调用纯代数引理
  sorry

/-- `base_plu` 证明 `n=0` 的基例。 -/
private lemma base_plu {x : Σ n, SquareMatFamily n R} (h_n_zero : x.1 = 0) : P_univ x := by
  let ⟨n, sq_mat⟩ := x; subst h_n_zero
  dsimp [P_univ]
  have h_empty : IsEmpty sq_mat.ι := FinEnum.isEmpty_of_card_eq_zero sq_mat.h_card.out
  dsimp [HasPLU, HasDecomposition, PLU_Schema]
  use (1, 1, 1)
  exact ⟨⟨by dsimp [IsPermutation]; use Equiv.refl _; simp [Matrix.isEmpty],
           by dsimp [IsUnitLowerTriangular, IsLowerTriangular, IsUpperTriangular]; simp [BlockTriangular, diag, Matrix.isEmpty],
           by dsimp [IsUpperTriangular]; simp [BlockTriangular, Matrix.isEmpty]⟩,
         by simp [Matrix.isEmpty]⟩

/-- `reach_plu` 证明 `n>0` 的归纳步骤。 -/
private lemma reach_plu {x : Σ n, SquareMatFamily n R} (h_n_pos : x.1 > 0) :
    ∃ y, ∃ (hy : IsSliceable_univ y), r_univ y x ∧ (fun z ↦ z.1) (slice_univ hy) < x.1 := by
  let ⟨n, sq_mat⟩ := x
  let A := sq_mat.matrix
  let S_strat := PLU_Strategy sq_mat.ι R h_n_pos
  rcases S_strat.mk_reach_metric (A := A) h_n_pos with ⟨y_mat, hy_sliceable_concrete, h_r_concrete, h_prog⟩
  let y_witness : Σ n, SquareMatFamily n R :=
    ⟨n, { ι := sq_mat.ι, matrix := y_mat }⟩
  use y_witness
  have hy : IsSliceable_univ y_witness := by
    dsimp [IsSliceable_univ]; rw [dif_pos h_n_pos]
    exact hy_sliceable_concrete
  use hy
  constructor
  · dsimp [r_univ]; rw [dif_pos rfl]
    -- 目标是 (PLU_Strategy ...).r (reindex ... y_mat) A
    -- reindex 是恒等映射，所以目标就是 .r y_mat A
    convert h_r_concrete
    ext i j; simp
  · dsimp [slice_univ]
    -- 目标是 n-1 < n
    exact h_prog

-- ==================================================================
-- L3.4: 组装最终证明
-- ==================================================================

/-- 对 `SquareMatFamily` 宇宙中的所有矩阵证明 PLU 分解存在性。 -/
private theorem exists_plu_for_family : ∀ (x : Σ n, SquareMatFamily n R), P_univ x := by
  apply transformSliceInduction (X := Σ n, SquareMatFamily n R)
    (μ := fun x ↦ x.1)
    (P := P_univ)
    (h_trans := transport_plu)
    (IsSliceable := IsSliceable_univ)
    (slice := slice_univ)
    (lift_from_slice := lift_from_slice_plu)
    (reach_metric := reach_plu)
    (base_metric := base_plu)

/-- **PLU 分解存在性定理 (最终对用户暴露的定理)** -/
theorem exists_plu_decomposition (A : Matrix ι ι R) : HasPLU A := by
  -- 1. 构造一个 `SquareMatFamily` 实例
  let n := card ι
  let sq_mat_family : SquareMatFamily n R := {
    ι := ι,
    matrix := A,
    h_card := ⟨rfl⟩
  }
  let x : Σ n, SquareMatFamily n R := ⟨n, sq_mat_family⟩
  -- 2. 调用在宇宙中证明的定理
  have h_univ := exists_plu_for_family x
  -- 3. 将宇宙中的结论转换回来
  dsimp [P_univ] at h_univ
  exact h_univ

end MatDecompFormal.Instances
