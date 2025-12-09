import Mathlib
import Mathlib.Data.FinEnum

namespace MatDecompFormal.Framework
open FinEnum

/--
`Mat R` 是一个“宇宙”类型，它包含了所有带有 `FinEnum` 索引的矩阵。

一个 `Mat R` 的实例 `x` 包含了：
- `x.ι`, `x.κ`: 行和列的索引类型。
- `x.finEnum_ι`, `x.finEnum_κ`: 保证索引类型是有限且可枚举的实例。
- `x.matrix`: `Matrix x.ι x.κ R` 类型的矩阵本身。

通过将这些信息打包，我们可以定义一个在所有矩阵上统一操作的归纳法。
-/
@[ext]
structure Mat (R : Type*) where
  ι : Type*
  κ : Type*
  [finEnum_ι : FinEnum ι]
  [finEnum_κ : FinEnum κ]
  matrix : Matrix ι κ R

-- 将 `FinEnum` 实例提升到结构体层面，使得当有一个 `x : Mat R` 时，
-- Lean 可以自动推断出 `x.ι` 和 `x.κ` 具有 `FinEnum` 实例。
attribute [instance] Mat.finEnum_ι Mat.finEnum_κ

/--
`SquareMat` (v2 - 最终版)
这个结构体直接封装了一个方阵。

关键设计：索引类型 `ι` 是一个顶层的、可直接访问的字段，
而不是深埋在子结构中。这使得在不同 `SquareMat` 实例之间
比较和传递类型信息变得直接和类型安全。
-/
structure SquareMat (R : Type*) [CommRing R] where
  ι : Type*
  [finEnum_ι : FinEnum ι]
  matrix : Matrix ι ι R

-- 提升实例，方便使用
attribute [instance] SquareMat.finEnum_ι


/--
`PositiveSquareMat` (v2 - 最终版)
这个结构体现在被定义为 `SquareMat` 的一个子类型，其中维度 `card ι`
被证明是大于零的。
-/
def PositiveSquareMat (R : Type*) [CommRing R] :=
  { x : SquareMat R // card x.ι > 0 }

-- 我们可以为 PositiveSquareMat 定义一些方便的构造器或访问器
namespace PositiveSquareMat

variable {R : Type*} [CommRing R]

-- 从一个已有的 SquareMat 和一个维度 > 0 的证明来构造
def mk (x : SquareMat R) (h_pos : card x.ι > 0) : PositiveSquareMat R :=
  ⟨x, h_pos⟩

-- 允许我们像访问 SquareMat 一样访问 PositiveSquareMat 的字段
instance : Coe (PositiveSquareMat R) (SquareMat R) where
  coe x := x.val

end PositiveSquareMat

/--
`SquareMatFamily n R` 是一个结构体，它封装了一个**维度为 n 的方阵**。

这个结构体是解决宇宙层级问题的关键。它将不稳定的索引类型 `ι`
“藏”在结构体内部，而将稳定的维度 `n : ℕ` 暴露为顶层参数。

一个 `SquareMatFamily n R` 的实例 `x` 包含：
- `x.ι`: 一个具体的索引类型。
- `x.finEnum_ι`: 证明 `ι` 是可枚举的。
- `x.h_card`: 一个**证明**，保证 `card x.ι = n`。
- `x.matrix`: `Matrix x.ι x.ι R` 类型的矩阵本身。
-/
structure SquareMatFamily (n : ℕ) (R : Type*) [CommRing R] where
  ι : Type*
  [finEnum_ι : FinEnum ι]
  [h_card : Fact (card ι = n)] -- 关键约束！
  matrix : Matrix ι ι R

-- 提升实例
attribute [instance] SquareMatFamily.finEnum_ι
attribute [instance] SquareMatFamily.h_card








-- /--
-- `SquareMat R` 是 `Mat R` 的一个子类型，它只包含所有方阵。
-- 一个 `SquareMat R` 的实例 `x` 包含：
-- - `x.mat`: 一个 `Mat R` 类型的底层对象。
-- - `x.is_square`: 一个证明，确保 `x.mat` 是方阵。
-- -/
-- structure SquareMat (R : Type*) where
--   mat : Mat R
--   is_square : card mat.ι = card mat.κ

-- -- 为了方便，我们可以为 SquareMat 创建一些快捷方式
-- namespace SquareMat

-- variable {R : Type*}

-- -- -- 允许我们直接访问底层的 ι, κ, matrix
-- -- def ι (x : SquareMat R) : Type* := x.mat.ι
-- -- def κ (x : SquareMat R) : Type* := x.mat.κ
-- -- def matrix (x : SquareMat R) : Matrix x.ι x.κ R := x.mat.matrix

-- -- 自动推断 FinEnum 实例
-- instance instFinEnum_ι (x : SquareMat R) : FinEnum x.mat.ι := x.mat.finEnum_ι
-- instance instFinEnum_κ (x : SquareMat R) : FinEnum x.mat.κ := x.mat.finEnum_κ

-- -- 允许我们将一个具体方阵直接“提升”为 SquareMat
-- def of {ι : Type*} [FinEnum ι] {R : Type*} (A : Matrix ι ι R) : SquareMat R :=
--   ⟨⟨ι, ι, A⟩, rfl⟩

-- end SquareMat


-- /-- `PositiveSquareMat R` 是所有维度大于 0 的方阵的子类型。 -/
-- def PositiveSquareMat (R : Type*) := {x : SquareMat R // card x.mat.ι > 0}

-- namespace PositiveSquareMat

-- def of {ι : Type*} [FinEnum ι] {R : Type*} (A : Matrix ι ι R) (h_card_pos : card ι > 0) :
--     PositiveSquareMat R :=
--   ⟨⟨⟨ι, ι, A⟩, rfl⟩, h_card_pos⟩

-- end PositiveSquareMat

end MatDecompFormal.Framework
