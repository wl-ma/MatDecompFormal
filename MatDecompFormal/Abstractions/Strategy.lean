import MatDecompFormal.Abstractions.ReductionMethod
import MatDecompFormal.Abstractions.Transformation

namespace MatDecompFormal.Abstractions

/-!
# 规约策略 (Reduction Strategy)

本文件定义了 `ReductionStrategy`，它将“变换”和“规约”组合成一个
完整的、在 `Fin m × Fin n` 矩阵上可执行的归纳步骤。
-/

/--
`ReductionStrategy`

*   `m`, `n`: 原始矩阵的维度。
*   `slice_m`, `slice_n`: 子问题矩阵的维度。
*   `R`: 环类型。
-/
structure ReductionStrategy (m n slice_m slice_n : ℕ) (R : Type*) [CommRing R] where
  /-- 用于达到可切片状态的变换。 -/
  transform : Transformation (Matrix (Fin m) (Fin n) R)
  /-- 用于分解问题的规约方法。 -/
  reduction : ReductionMethod m n slice_m slice_n R
  /-- 兼容性断言：变换的目标 `Goal` 必须与规约方法的 `IsSliceable` 条件在逻辑上等价。 -/
  goal_is_sliceable : transform.Goal = reduction.IsSliceable

  /-- 原问题尺寸 (m×n) 的度量函数。 -/
  μ : Matrix (Fin m) (Fin n) R → ℕ

  /-- 切片问题尺寸 (slice_m×slice_n) 的度量函数。 -/
  μ_slice : Matrix (Fin slice_m) (Fin slice_n) R → ℕ

  /-- 度量单调性：变换不会增大度量（作用在同尺寸 m×n 上）。 -/
  μ_mono :
    ∀ (A : Matrix (Fin m) (Fin n) R) (t : transform.T),
      μ (transform.apply t A) ≤ μ A

  /-- 切片进展性：切片后的度量（用 μ_slice 计）严格小于原问题度量（用 μ 计）。 -/
  slice_progress :
    ∀ (A : Matrix (Fin m) (Fin n) R) (hA : reduction.IsSliceable A),
      μ_slice (reduction.slice A hA) < μ A

/--
`ReductionStrategy.r` 定义了策略所允许的变换关系。
-/
def ReductionStrategy.r {m n slice_m slice_n R} [CommRing R]
    (S : ReductionStrategy m n slice_m slice_n R) (y x : Matrix (Fin m) (Fin n) R) : Prop :=
  (y = x) ∨ (∃ (t : S.transform.T), y = S.transform.apply t x)

/--
`ReductionStrategy.mk_reach` 从一个策略中自动构造出
子类型归纳实例所需的 `reach` 证明。
-/
noncomputable def ReductionStrategy.mk_reach {m n slice_m slice_n R} [CommRing R]
    (S : ReductionStrategy m n slice_m slice_n R) (μ_base : ℕ)
    (_h_pos : m > 0 ∧ n > 0)
    (A : Matrix (Fin m) (Fin n) R)
    (_h_mu_gt_base : S.μ A > μ_base)
    : Σ' (B : Matrix (Fin m) (Fin n) R),
        Σ' (hB : S.reduction.IsSliceable B),
          S.r B A ∧ S.μ_slice (S.reduction.slice B hB) < S.μ A := by
  by_cases h_goal : S.transform.Goal A
  · refine ⟨A, ?_⟩
    have hA_sliceable : S.reduction.IsSliceable A := by
      rw [← S.goal_is_sliceable]; exact h_goal
    refine ⟨hA_sliceable, ?_⟩
    exact ⟨Or.inl rfl, S.slice_progress A hA_sliceable⟩
  · let t := S.transform.find A h_goal
    let B := S.transform.apply t A
    refine ⟨B, ?_⟩
    have hB_sliceable : S.reduction.IsSliceable B := by
      rw [← S.goal_is_sliceable]; exact S.transform.find_spec A h_goal
    refine ⟨hB_sliceable, ?_⟩
    refine ⟨Or.inr ⟨t, rfl⟩, ?_⟩
    have hprog : S.μ_slice (S.reduction.slice B hB_sliceable) < S.μ B :=
      S.slice_progress B hB_sliceable
    have hmono : S.μ B ≤ S.μ A := by
      simpa [B] using S.μ_mono A t
    exact lt_of_lt_of_le hprog hmono

end MatDecompFormal.Abstractions
