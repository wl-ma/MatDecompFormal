import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

namespace MatDecompFormal.Abstractions

open Matrix

/-!
# 矩阵属性的抽象 (Abstract Matrix Properties)

本文件定义了 `MatrixGroup` 类型类，用于捕获那些构成群的矩阵属性
（例如，置换矩阵、正交矩阵）。这个抽象的主要目的是为了组织代码、
统一概念，并为未来的通用引理和自动化策略提供支持。
-/

/--
`MatrixGroup P` 是一个类型类，它断言满足性质 `P` 的 `n × n` 矩阵
在矩阵乘法下构成一个群。
-/
class MatrixGroup {n R} [CommRing R] (P : Matrix (Fin n) (Fin n) R → Prop) where
  /-- 乘法封闭性：两个满足性质 P 的矩阵相乘，结果仍然满足 P。 -/
  mul_closed : ∀ {A B}, P A → P B → P (A * B)
  /-- 单位元属于该集合。 -/
  one_mem : P 1
  /-- 求逆封闭性：满足性质 P 的矩阵，其逆矩阵也满足 P。 -/
  inv_closed : ∀ {A}, P A → P A⁻¹
  /-- 可逆性：满足性质 P 的矩阵都是可逆的（即是环中的单位）。 -/
  invertible : ∀ {A}, P A → IsUnit A

end MatDecompFormal.Abstractions
