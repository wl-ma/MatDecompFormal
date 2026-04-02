import Mathlib.Algebra.Ring.Defs
import Mathlib.LinearAlgebra.Matrix.Defs

namespace MatDecompFormal.Abstractions

/-!
# 规约方法 (Reduction Method)

本文件定义了 `ReductionMethod`，它封装了在 `Fin m × Fin n` 矩阵上进行
问题规约的纯代数部分。
-/

/--
`ReductionMethod` (Fin m n 版)

*   `m`, `n`, `R`: 原始矩阵的维度和环类型。
*   `slice_m`, `slice_n`: 子问题（切片）矩阵的维度。
*   `IsSliceable`: 描述一个 `Matrix (Fin m) (Fin n) R` 何时可以被切片。
*   `slice`: 从可切片矩阵中提取 `Matrix (Fin slice_m) (Fin slice_n) R` 类型的子问题。
*   `reconstruct`: 从原始矩阵上下文和子矩阵的解重构出完整矩阵。
*   `reconstruct_slice_eq`: 证明 `reconstruct` 和 `slice` 的代数一致性。
-/
structure ReductionMethod (m n slice_m slice_n : ℕ) (R : Type*) [CommRing R] where
  /-- 一个谓词，用于判断一个矩阵是否处于可以被“切片”的“标准型”。 -/
  IsSliceable : Matrix (Fin m) (Fin n) R → Prop

  /-- “切片”算子，从一个可切片的矩阵中提取出更小的子问题。 -/
  slice : (A : Matrix (Fin m) (Fin n) R) → (hA : IsSliceable A) →
    Matrix (Fin slice_m) (Fin slice_n) R

  /-- “重构”函数：从原始矩阵的上下文和子矩阵的解来组装一个完整的矩阵。 -/
  reconstruct : (A : Matrix (Fin m) (Fin n) R) → (hA : IsSliceable A) →
                (slice_sol : Matrix (Fin slice_m) (Fin slice_n) R) → Matrix (Fin m) (Fin n) R

  /-- 重构的正确性证明：用原始切片进行重构会得到原始矩阵。 -/
  reconstruct_slice_eq : ∀ (A : Matrix (Fin m) (Fin n) R) (hA : IsSliceable A),
                           reconstruct A hA (slice A hA) = A

end MatDecompFormal.Abstractions
