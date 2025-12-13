import Mathlib.LinearAlgebra.Matrix.Reindex
import MatDecompFormal.Abstractions.Schema
import MatDecompFormal.Framework.FinEnum

/-
Instances/DecompositionFin.lean

通用桥接模块：从 Fin n 世界的“引擎定理”提升到任意 FinEnum 索引类型。
-/


namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Abstractions
open MatDecompFormal.Framework


/--
`FinDecompositionData R` 封装了一类“在 `Fin n` 上已经做完的矩阵分解”。

使用方式是：针对某个具体分解（比如 PLU），构造一个这样的 `data`：
* 指定对每个索引类型 `ι` 的分解模式 `Schema ι`；
* 给出 **Fin 引擎定理**：对所有 `n` 和 `A : Matrix (Fin n) (Fin n) R`，
  存在 `HasDecomposition (Schema (Fin n)) A`；
* 给出 **reindex 不变性**：对任意索引同构 `e : ι ≃o ι'`，
  `HasDecomposition` 在 `Matrix.reindex e` 下是逻辑等价的。
-/
structure FinDecompositionData (R : Type*) [CommRing R] where
  /-- 对每个索引类型 `ι` 给出一个分解模式 `DecompositionSchema`. -/
  Schema : ∀ (ι : Type*) [FinEnum ι], DecompositionSchema ι ι R

  /--
  **Fin 引擎定理**：在所有 `Fin n` 上已经证明了存在性。

  例如对于 PLU，这里就是：
  `∀ n A, HasPLU_fin n A`。
  -/
  exists_fin :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R),
      HasDecomposition (Schema (Fin n)) A

  /--
  **reindex 不变性**：`HasDecomposition` 在索引等价 `e : ι ≃o ι'` 下保持等价。

  注意这里使用的是 `Equiv` 的有序版本 `≃o`，是为了兼容
  像“上三角”“置换矩阵”这类依赖顺序的性质（例如 PLU）。
  -/
  hasDecomp_reindex_iff :
    ∀ {ι ι' : Type*} [FinEnum ι] [FinEnum ι']
      (e : ι ≃o ι') (A : Matrix ι ι R),
      HasDecomposition (Schema ι) A
        ↔ HasDecomposition (Schema ι') (A.reindex e.toEquiv e.toEquiv)

namespace FinDecompositionData

variable {R : Type*} [CommRing R] (data : FinDecompositionData R)

section FinWorld

/-- 在 Fin 世界中的存在性定理就是 `exists_fin` 本身，给个别名方便使用。 -/
@[simp]
theorem exists_decomposition_fin
    (n : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    HasDecomposition (data.Schema (Fin n)) A :=
  data.exists_fin n A

end FinWorld

section FinEnumWorld

variable [DecidableEq R]

/--
核心桥接定理：

如果 `data` 提供了
* 在 `Fin n` 上的存在性 `exists_fin`;
* 在 `reindex` 下的不变性 `hasDecomp_reindex_iff`；

那么对于任意带 `FinEnum` 结构的索引类型 `ι`，任意方阵
`A : Matrix ι ι R` 都存在对应的分解。

这个定理就是以后各个具体分解（PLU, QR, ...）对外暴露的
`exists_..._decomposition` 的“通用内核”。
-/
theorem exists_decomposition_finEnum
    {ι : Type*} [FinEnum ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    HasDecomposition (data.Schema ι) A := by
  classical
  -- 令 n 为 ι 的基数
  let n : ℕ := FinEnum.card ι
  -- 由 FinEnum 得到一个规范的有序同构 ι ≃o Fin n
  let e : ι ≃o Fin n := orderIsoOfFinEnum ι
  -- 在 Fin 世界里，对 reindex 后的矩阵应用引擎定理
  let A_fin : Matrix (Fin n) (Fin n) R :=
    A.reindex e.toEquiv e.toEquiv
  have h_fin : HasDecomposition (data.Schema (Fin n)) A_fin :=
    data.exists_fin n A_fin
  -- 利用 reindex 不变性，把 Fin 世界的结论搬回 ι 世界
  have :=
    (data.hasDecomp_reindex_iff (e := e) (A := A)).mpr h_fin
  exact this

/-- 一个方便的别名：把 `A` 当作隐式参数。 -/
@[simp]
theorem exists_decomposition_finEnum'
    {ι : Type*} [FinEnum ι] [DecidableEq ι] :
    ∀ A : Matrix ι ι R, HasDecomposition (data.Schema ι) A :=
  data.exists_decomposition_finEnum

end FinEnumWorld

end FinDecompositionData

end MatDecompFormal.Instances








-- import Mathlib.Data.Fin.Basic
-- import Mathlib.LinearAlgebra.Matrix.Basis
-- import MatDecompFormal.Framework.Induction
-- import MatDecompFormal.Abstractions.Schema

-- /-!
--   一个对 `Matrix (Fin n) (Fin n) R` 家族的统一归纳原理，
--   用于任意矩阵分解（PLU、LU、QR 等）的 Fin n 版本存在性定理。
-- -/

-- namespace MatDecompFormal.Instances.Core

-- open MatDecompFormal.Abstractions
-- open MatDecompFormal.Framework
-- open Matrix

-- universe u

-- variable (R : Type u) [CommRing R]

-- /-!
-- ## 1. Fin 方阵宇宙：`FinSqMatFamily R`

-- 我们把「所有尺寸的 Fin 方阵」打包成一个 σ 型：
-- `Σ n, Matrix (Fin n) (Fin n) R`，并在上面跑 `transformSliceInduction`。
-- -/

-- /-- 所有 `Fin n` 尺寸方阵组成的宇宙。 -/
-- abbrev FinSqMatFamily (R : Type u) :=
--   Σ n : ℕ, Matrix (Fin n) (Fin n) R

-- namespace FinSqMatFamily

-- variable {R}

-- /-- 外层维度作为归纳度量。 -/
-- @[inline] def μ (x : FinSqMatFamily R) : ℕ := x.1

-- /-- 投影出维度 `n`。 -/
-- @[inline] def dim (x : FinSqMatFamily R) : ℕ := x.1

-- /-- 投影出矩阵本体。 -/
-- @[inline] def mat (x : FinSqMatFamily R) : Matrix (Fin x.1) (Fin x.1) R := x.2

-- end FinSqMatFamily


-- /-!
-- ## 2. 对任意 `Schema_fin : ∀ n` 的族，定义家族上的性质 `P_univ`

-- 给定一族分解模式

-- Schema_fin : ∀ n, DecompositionSchema (Fin n) (Fin n) R

-- 我们在 σ 型上定义性质

-- P_univ x := HasDecomposition (Schema_fin x.1) x.2

-- -/

-- /-- 家族上的命题：该尺寸下的矩阵 `x.2` 按 `Schema_fin x.1` 有分解。 -/
-- def P_univ (Schema_fin : ∀ n, DecompositionSchema (Fin n) (Fin n) R)
--     (x : FinSqMatFamily R) : Prop :=
--   HasDecomposition (Schema_fin x.1) x.2

-- /-!

-- ## 3. 核心原定理：`exists_decomposition_fin`

-- 这个定理把通用的 `transformSliceInduction` 固定在

-- * `X := Σ n, Matrix (Fin n) (Fin n) R`
-- * 度量 `μ x := x.1`
-- * 性质 `P x := HasDecomposition (Schema_fin x.1) x.2`

-- 上。
-- -/

-- /--
-- **Fin 家族分解原定理（meta-theorem）**

-- 给定：

-- * 一族分解模式
--   `Schema_fin : ∀ n, DecompositionSchema (Fin n) (Fin n) R`；
-- * 一步变换关系 `r_univ`，`IsSliceable_univ` 与 `slice_univ`；
-- * 传递性、lift、reach、base 等归纳前提；

-- 则对所有 `n` 和 `A : Matrix (Fin n) (Fin n) R`，
-- `A` 相对于 `Schema_fin n` 都存在分解。
-- -/
-- theorem exists_decomposition_fin
--     (Schema_fin : ∀ n : ℕ, DecompositionSchema (Fin n) (Fin n) R)
--     -- 家族层面的“允许变换”关系:
--     (r_univ : FinSqMatFamily R → FinSqMatFamily R → Prop)
--     -- 家族层面的“可切片”谓词:
--     (IsSliceable_univ : FinSqMatFamily R → Prop)
--     -- 家族层面的切片算子:
--     (slice_univ :
--       ∀ {x : FinSqMatFamily R}, IsSliceable_univ x → FinSqMatFamily R)
--     -- 1. P 在 r_univ 下可以搬运（Transport）:
--     (transport_univ :
--       Transport r_univ (P_univ (R := R) Schema_fin))
--     -- 2. 从子问题解（slice_univ hx 上的 P）提升回原问题（lift）:
--     (lift_from_slice_univ :
--       ∀ {x : FinSqMatFamily R} (hx : IsSliceable_univ x),
--         P_univ (R := R) Schema_fin (slice_univ hx) →
--         P_univ (R := R) Schema_fin x)
--     -- 3. 进展性（reach）：如果 μ x > 0，就能在 r_univ 下找到 y：
--     --    (a) y 可切片；
--     --    (b) y 和 x 通过 r_univ 相关；
--     --    (c) 切片后的度量严格减小。
--     (reach_metric_univ :
--       ∀ {x : FinSqMatFamily R},
--         FinSqMatFamily.μ (R := R) x > 0 →
--         ∃ y : FinSqMatFamily R,
--         ∃ (hy : IsSliceable_univ y),
--         r_univ y x ∧
--         FinSqMatFamily.μ (R := R) (slice_univ hy)
--         < FinSqMatFamily.μ (R := R) x)
--     -- 4. 基例：μ x = 0 的情形（也就是 n = 0）。
--     (base_metric_univ :
--       ∀ {x : FinSqMatFamily R},
--         FinSqMatFamily.μ (R := R) x = 0 →
--         P_univ (R := R) Schema_fin x) :
--     ∀ n (A : Matrix (Fin n) (Fin n) R), HasDecomposition (Schema_fin n) A := by
--   -- 在整个家族上应用通用的 transformSliceInduction
--   let X := FinSqMatFamily R
--   have h_all :
--     ∀ x : X, P_univ (R := R) Schema_fin x :=
--       transformSliceInduction
--         (X            := X)
--         (μ            := FinSqMatFamily.μ (R := R))
--         (P            := P_univ (R := R) Schema_fin)
--         (h_trans      := transport_univ)
--         (IsSliceable  := IsSliceable_univ)
--         (slice        := slice_univ)
--         (lift_from_slice := lift_from_slice_univ)
--         (reach_metric := reach_metric_univ)
--         (base_metric  := base_metric_univ)

--   -- 把族上的结论 specialize 回每个固定的 n
--   intro n A
--   have := h_all ⟨n, A⟩
--   -- 展开 P_univ 的定义
--   simpa [P_univ] using this

-- /-!

-- ## 4. 打包版：`FinDecompData` + `exists_decomposition_fin'`

-- 为了让每个具体分解（PLU/LU/QR）文件中调用更干净，
-- 我们把所有家族层面的数据打包成一个结构。
-- -/

-- /--
-- 把 Fin 家族分解所需的全部“宇宙层”数据打包起来，方便实例文件使用。
-- -/
-- structure FinDecompData where
--   Schema_fin : ∀ n : ℕ, DecompositionSchema (Fin n) (Fin n) R
--   r_univ     : FinSqMatFamily R → FinSqMatFamily R → Prop
--   IsSliceable_univ : FinSqMatFamily R → Prop
--   slice_univ :
--     ∀ {x : FinSqMatFamily R}, IsSliceable_univ x → FinSqMatFamily R
--   transport_univ :
--     Transport r_univ (P_univ (R := R) Schema_fin)
--   lift_from_slice_univ :
--     ∀ {x : FinSqMatFamily R} (hx : IsSliceable_univ x),
--       P_univ (R := R) Schema_fin (slice_univ hx) →
--       P_univ (R := R) Schema_fin x
--   reach_metric_univ :
--     ∀ {x : FinSqMatFamily R},
--       FinSqMatFamily.μ (R := R) x > 0 →
--       ∃ y : FinSqMatFamily R,
--       ∃ (hy : IsSliceable_univ y),
--       r_univ y x ∧
--       FinSqMatFamily.μ (R := R) (slice_univ hy)
--       < FinSqMatFamily.μ (R := R) x
--   base_metric_univ :
--     ∀ {x : FinSqMatFamily R},
--       FinSqMatFamily.μ (R := R) x = 0 →
--       P_univ (R := R) Schema_fin x

-- /--
-- 同一个原定理，但把所有 house-keeping 参数打包成 `FinDecompData`，
-- 实例文件里调用起来更整洁。
-- -/
-- theorem exists_decomposition_fin'
--     (data : FinDecompData R) :
--     ∀ n (A : Matrix (Fin n) (Fin n) R),
--     HasDecomposition (data.Schema_fin n) A :=
--   exists_decomposition_fin (R := R)
--     data.Schema_fin
--     data.r_univ
--     data.IsSliceable_univ
--     (fun x => data.slice_univ x)
--     data.transport_univ
--     data.lift_from_slice_univ
--     data.reach_metric_univ
--     data.base_metric_univ

-- end MatDecompFormal.Instances.Core
