import Mathlib

namespace MatDecompFormal.Framework

-- /-!
-- # 矩阵族 (Matrix Families)

-- 本文件定义了 `SquareMatFamily n R`，这是一个封装了维度为 `n` 的
-- 所有方阵的结构体。

-- 这个结构体是本框架归纳引擎的基石。通过将矩阵按其维度 `n : ℕ`
-- 进行分组，我们创建了一个可以在其上进行良基归纳的“宇宙”。
-- 归纳法将在这个宇宙的 Σ 类型 `Σ n, SquareMatFamily n R` 上进行，
-- 其度量函数就是维度 `n`。
-- -/

-- /--
-- `SquareMatFamily n R` 封装了一个维度为 n 的方阵。
-- 它将不稳定的索引类型 `ι` “藏”在结构体内部，而将稳定的维度 `n`
-- 暴露为顶层参数。
-- -/
-- structure SquareMatFamily (n : ℕ) (R : Type*) [CommRing R] where
--   ι : Type*
--   [finEnum_ι : FinEnum ι]
--   [h_card : Fact (FinEnum.card ι = n)] -- 关键约束！
--   matrix : Matrix ι ι R

-- -- 提升实例
-- attribute [instance] SquareMatFamily.finEnum_ι
-- attribute [instance] SquareMatFamily.h_card

-- /--
-- `PositiveSquareMatFamily n R` 是一个子类型，确保维度 n > 0。
-- -/
-- def PositiveSquareMatFamily (n : ℕ) (h_pos : n > 0) (R : Type*) [CommRing R] :=
--   SquareMatFamily n R


-- /--
-- `FinRectObj` 是我们宇宙的基本粒子，代表一个 m × n 的矩阵。
-- -/
-- structure FinRectObj (R : Type*) where
--   m : ℕ
--   n : ℕ
--   A : Matrix (Fin m) (Fin n) R

-- /-- 宇宙现在是所有 m × n 矩阵的集合。 -/
-- abbrev FinRectUniverse (R : Type*) := FinRectObj R

-- -- 注意：μ 不再是宇宙的固定属性！
-- -- 不同的分解可能在不同维度上归纳（行、列、或 min(m,n)）。
-- -- 因此，μ 将成为 `Strategy` 的一部分，而不是 Universe 的一部分。

-- /--
-- `PosFinRectUniverse R` 是所有维度 m > 0 且 n > 0 的矩阵的子类型。
-- 这是我们进行归纳证明的主要舞台。
-- -/
-- def PosFinRectUniverse (R : Type*) := { x : FinRectUniverse R // x.m > 0 ∧ x.n > 0 }

-- /-- 纯 `Fin n` 宇宙里的方阵对象。 -/
-- structure FinSqObj (R : Type*) where
--   n : ℕ
--   A : Matrix (Fin n) (Fin n) R

-- /-- 方便的别名：`Σ n, Matrix (Fin n) (Fin n) R` 的包装形式。 -/
-- abbrev FinSqUniverse (R : Type*) := FinSqObj R

-- /-- 维度度量：就是 `n` 本身。 -/
-- def μ_fin {R} (x : FinSqUniverse R) : ℕ := x.n

-- /--
-- `PosFinSqUniverse R` 是一个子类型，代表所有维度 n > 0 的方阵。
-- 这是我们进行归纳证明的主要舞台。
-- -/
-- def PosFinSqUniverse (R : Type*) := { x : FinSqUniverse R // μ_fin x > 0 }


/-!
# 矩阵宇宙 (Matrix Universe) - v5.0 (Σ-Type Final)

本文件定义了框架的“宇宙”类型。最终版本采纳了 Σ 类型的设计，
将矩阵的维度 `m` 和 `n` 作为宇宙对象的顶层参数暴露出来，
从而彻底解决了类型依赖问题，简化了整个框架的类型推断。
-/

/--
`FinRectFamily m n R` 封装了一个固定维度 `m × n` 的矩阵。
-/
structure FinRectFamily (m n : ℕ) (R : Type*) where
  A : Matrix (Fin m) (Fin n) R

/--
`FinRectUniverse R` 是所有 `m × n` 矩阵的集合，定义为 Σ 类型。
宇宙中的一个对象 `x` 是一个依赖对 `⟨⟨m, n⟩, fam⟩`，其中 `fam.A` 是矩阵。
-/
abbrev FinRectUniverse (R : Type*) := Σ (dims : ℕ × ℕ), FinRectFamily dims.1 dims.2 R

/--
`PosFinRectUniverse R` 是所有维度 `m > 0 ∧ n > 0` 的矩阵的子类型。
-/
abbrev PosFinRectUniverse (R : Type*) := { x : FinRectUniverse R // x.1.1 > 0 ∧ x.1.2 > 0 }

-- 辅助函数，用于从宇宙对象中提取矩阵
@[simp] def FinRectUniverse.matrix {R} (x : FinRectUniverse R) : Matrix (Fin x.1.1) (Fin x.1.2) R :=
  x.2.A

-- /--
-- `inductive_μ` 将一个仅在正维度上定义的度量扩展到整个 `FinRectUniverse`。
-- 零维度对象映射为给定的基准值 `μ_base_pos`，正维度对象则使用用户度量。
-- -/
-- noncomputable def inductive_μ {R} (μ_pos : PosFinRectUniverse R → ℕ)
--     (μ_base_pos : ℕ) (x : FinRectUniverse R) : ℕ :=
--   if h : x.1.1 > 0 ∧ x.1.2 > 0 then μ_pos ⟨x, h⟩ else μ_base_pos

/-- `FinSqFamily n R` 封装一个固定维度 `n × n` 的方阵。 -/
structure FinSqFamily (n : ℕ) (R : Type*) where
  A : Matrix (Fin n) (Fin n) R

/-- `FinSqUniverse R`：所有 `n × n` 方阵的宇宙（Σ 类型）。 -/
abbrev FinSqUniverse (R : Type*) := Σ (n : ℕ), FinSqFamily n R

/-- `PosFinSqUniverse R`：维度 `n > 0` 的方阵子类型。 -/
abbrev PosFinSqUniverse (R : Type*) := { x : FinSqUniverse R // x.1 > 0 }

/-- 从方阵宇宙对象中取出矩阵。 -/
@[simp] def FinSqUniverse.matrix {R} (x : FinSqUniverse R) : Matrix (Fin x.1) (Fin x.1) R :=
  x.2.A

end MatDecompFormal.Framework









-- import Mathlib
-- import Mathlib.Data.FinEnum

-- namespace MatDecompFormal.Framework
-- open FinEnum

-- /--
-- `Mat R` 是一个“宇宙”类型，它包含了所有带有 `FinEnum` 索引的矩阵。

-- 一个 `Mat R` 的实例 `x` 包含了：
-- - `x.ι`, `x.κ`: 行和列的索引类型。
-- - `x.finEnum_ι`, `x.finEnum_κ`: 保证索引类型是有限且可枚举的实例。
-- - `x.matrix`: `Matrix x.ι x.κ R` 类型的矩阵本身。

-- 通过将这些信息打包，我们可以定义一个在所有矩阵上统一操作的归纳法。
-- -/
-- @[ext]
-- structure Mat (R : Type*) where
--   ι : Type*
--   κ : Type*
--   [finEnum_ι : FinEnum ι]
--   [finEnum_κ : FinEnum κ]
--   matrix : Matrix ι κ R

-- -- 将 `FinEnum` 实例提升到结构体层面，使得当有一个 `x : Mat R` 时，
-- -- Lean 可以自动推断出 `x.ι` 和 `x.κ` 具有 `FinEnum` 实例。
-- attribute [instance] Mat.finEnum_ι Mat.finEnum_κ

-- /--
-- `SquareMat` (v2 - 最终版)
-- 这个结构体直接封装了一个方阵。

-- 关键设计：索引类型 `ι` 是一个顶层的、可直接访问的字段，
-- 而不是深埋在子结构中。这使得在不同 `SquareMat` 实例之间
-- 比较和传递类型信息变得直接和类型安全。
-- -/
-- structure SquareMat (R : Type*) [CommRing R] where
--   ι : Type*
--   [finEnum_ι : FinEnum ι]
--   matrix : Matrix ι ι R

-- -- 提升实例，方便使用
-- attribute [instance] SquareMat.finEnum_ι


-- /--
-- `PositiveSquareMat` (v2 - 最终版)
-- 这个结构体现在被定义为 `SquareMat` 的一个子类型，其中维度 `card ι`
-- 被证明是大于零的。
-- -/
-- def PositiveSquareMat (R : Type*) [CommRing R] :=
--   { x : SquareMat R // card x.ι > 0 }

-- -- 我们可以为 PositiveSquareMat 定义一些方便的构造器或访问器
-- namespace PositiveSquareMat

-- variable {R : Type*} [CommRing R]

-- -- 从一个已有的 SquareMat 和一个维度 > 0 的证明来构造
-- def mk (x : SquareMat R) (h_pos : card x.ι > 0) : PositiveSquareMat R :=
--   ⟨x, h_pos⟩

-- -- 允许我们像访问 SquareMat 一样访问 PositiveSquareMat 的字段
-- instance : Coe (PositiveSquareMat R) (SquareMat R) where
--   coe x := x.val

-- end PositiveSquareMat

-- end MatDecompFormal.Framework
