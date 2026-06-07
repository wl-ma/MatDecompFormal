import MatDecompFormal.Instances.SVD.Direct
import MatDecompFormal.Instances.SVD.Spectral

universe u

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

/-!
# Singular Value Decomposition: Framework Entry

This file assembles the SVD descent through the rectangular universe driver:

```lean
RectStrategyData
mkRectSubtypeInductionInstanceFromStrategy
RectSubtypeInductionInstance.prove_for_matrix
```

The main framework theorem is conditional only on the singular-vector oracle.
The recursion, base cases, reachability, unitary transport, and block-ready
lift all go through the shared rectangular descent template.
-/

/-- Universe-level base case for the SVD target. -/
theorem svd_base_univ (x : RectUniverse ℂ) :
    ((∀ (x_sub : PosRectUniverse ℂ), (x_sub : RectUniverse ℂ) ≠ x) ∨
      rectSubtypeμ x ≤ rectSubtypeμBase) →
      SVD_P x := by
  intro hx
  rcases rectSubtypeBaseDimEqZero x hx with hrow | hcol
  · letI : IsEmpty x.ι := Fintype.card_eq_zero_iff.mp hrow
    exact base_svd_empty_rows x.A
  · letI : IsEmpty x.κ := Fintype.card_eq_zero_iff.mp hcol
    exact base_svd_empty_cols x.A

noncomputable def svd_strategy_data
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SVDSimilarityOracle m n)
    (hooks : SVDDescentHooks oracle) :
    RectStrategyData ℂ SVD_P :=
  mkRectStrategyData
    (svd_strategy_core oracle)
    (svd_strategy_proof oracle hooks)

noncomputable def svd_framework_inst
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SVDSimilarityOracle m n)
    (hooks : SVDDescentHooks oracle) :
    RectSubtypeInductionInstance ℂ :=
  mkRectSubtypeInductionInstanceFromStrategy
    SVD_P
    svd_base_univ
    (svd_strategy_data oracle hooks)

/--
Framework-routed SVD theorem.

This is the recursive SVD assembly theorem over the project's rectangular
descent driver. The remaining mathematical inputs are exactly the one-step
singular-vector oracle and the block-ready lift hook.
-/
theorem exists_svd_framework
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SVDSimilarityOracle m n)
    (hooks : SVDDescentHooks oracle)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasSVD A := by
  have hP :
      (svd_framework_inst oracle hooks).P (RectUniverse.ofMatrix A) :=
    RectSubtypeInductionInstance.prove_for_matrix
      (inst := svd_framework_inst oracle hooks) A
  exact hP

/--
Framework-routed SVD theorem conditional only on the one-step singular-vector
oracle. The proof-side descent hooks are constructed concretely in
`Direct.lean`.
-/
theorem exists_svd_framework_oracle
    (oracle :
      ∀ {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
        [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n],
        SVDSimilarityOracle m n)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasSVD A := by
  exact exists_svd_framework oracle (svd_descent_hooks oracle) A

/--
Framework-routed SVD theorem in terms of the concrete one-step block-ready
oracle. This is the current closest interface to the intended singular-vector
construction.
-/
theorem exists_svd_framework_blockOracle
    (blockOracle :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        SVDBlockReadyOracle p q)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasSVD A := by
  let oracle :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        SVDSimilarityOracle p q :=
    fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        svdSimilarityOracleOfBlockReady p q (blockOracle (p := p) (q := q))
  exact exists_svd_framework_oracle oracle A

/--
Framework-routed SVD theorem in terms of one-step head singular-vector data.
This is the interface targeted by the concrete `Aᴴ * A` spectral construction.
-/
theorem exists_svd_framework_headSingularVectorData
    (headData :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        SVDHeadSingularVectorData p q)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasSVD A := by
  let blockOracle :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        SVDBlockReadyOracle p q :=
    fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        svdBlockReadyOracleOfHeadSingularVectorData p q (headData (p := p) (q := q))
  exact exists_svd_framework_blockOracle blockOracle A

/--
Framework-routed SVD theorem in terms of basis-level one-step singular-vector
data. This is closer to the standard construction: choose orthonormal left and
right bases whose head vectors form a singular pair and whose off-head
components vanish.
-/
theorem exists_svd_framework_headBasisData
    (basisData :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        SVDHeadBasisData p q)
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasSVD A := by
  let headData :
      ∀ {p q : Type u} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
        [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q],
        SVDHeadSingularVectorData p q :=
    fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        svdHeadSingularVectorDataOfHeadBasisData p q (basisData (p := p) (q := q))
  exact exists_svd_framework_headSingularVectorData headData A

/--
Unconditional complex singular value decomposition, assembled through the
project's rectangular descent framework.
-/
theorem exists_svd
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasSVD A := by
  exact exists_svd_framework_headBasisData
    (fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        svdHeadBasisData p q)
    A

end MatDecompFormal.Instances
