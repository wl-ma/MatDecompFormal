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

-- 在 Framework/Universe.lean (或 Induction.lean)

/--
`SquareMat R` 是 `Mat R` 的一个子类型，它只包含所有方阵。
一个 `SquareMat R` 的实例 `x` 包含：
- `x.mat`: 一个 `Mat R` 类型的底层对象。
- `x.is_square`: 一个证明，确保 `x.mat` 是方阵。
-/
structure SquareMat (R : Type*) where
  mat : Mat R
  is_square : card mat.ι = card mat.κ

-- 为了方便，我们可以为 SquareMat 创建一些快捷方式
namespace SquareMat

variable {R : Type*}

-- -- 允许我们直接访问底层的 ι, κ, matrix
-- def ι (x : SquareMat R) : Type* := x.mat.ι
-- def κ (x : SquareMat R) : Type* := x.mat.κ
-- def matrix (x : SquareMat R) : Matrix x.ι x.κ R := x.mat.matrix

-- 自动推断 FinEnum 实例
instance instFinEnum_ι (x : SquareMat R) : FinEnum x.mat.ι := x.mat.finEnum_ι
instance instFinEnum_κ (x : SquareMat R) : FinEnum x.mat.κ := x.mat.finEnum_κ

-- 允许我们将一个具体方阵直接“提升”为 SquareMat
def of {ι : Type*} [FinEnum ι] {R : Type*} (A : Matrix ι ι R) : SquareMat R :=
  ⟨⟨ι, ι, A⟩, rfl⟩

end SquareMat


/-- `PositiveSquareMat R` 是所有维度大于 0 的方阵的子类型。 -/
def PositiveSquareMat (R : Type*) := {x : SquareMat R // card x.mat.ι > 0}

namespace PositiveSquareMat

def of {ι : Type*} [FinEnum ι] {R : Type*} (A : Matrix ι ι R) (h_card_pos : card ι > 0) :
    PositiveSquareMat R :=
  ⟨⟨⟨ι, ι, A⟩, rfl⟩, h_card_pos⟩

end PositiveSquareMat

end MatDecompFormal.Framework
