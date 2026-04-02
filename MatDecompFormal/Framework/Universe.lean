import Mathlib

namespace MatDecompFormal.Framework

/-!
# 矩阵宇宙 (Matrix Universe)

本文件定义了框架的“宇宙”类型，使用 Σ 类型统一组织不同尺寸的矩阵，
从而让跨维度规约和归纳在同一个宿主类型上表达。
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

@[simp] def FinRectUniverse.matrix {R} (x : FinRectUniverse R) : Matrix (Fin x.1.1) (Fin x.1.2) R :=
  x.2.A

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
