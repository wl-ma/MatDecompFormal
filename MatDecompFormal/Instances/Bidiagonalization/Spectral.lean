import MatDecompFormal.Instances.Bidiagonalization.Existence
import MatDecompFormal.Instances.SVD.Spectral

universe u

namespace MatDecompFormal.Instances

open Matrix

/-!
# Bidiagonalization Spectral One-Step Bridge

This file supplies a concrete complex one-step oracle for the current
block-ready bidiagonalization template by reusing the existing SVD head
block-ready construction. The final theorem is still assembled through
`exists_unitary_bidiagonalization_oracle`, hence through the rectangular
descent framework.
-/

/--
The SVD head block-ready oracle is stronger than the current
bidiagonalization readiness invariant.
-/
noncomputable def bidiagonalizationStepOracleOfSVDBlockReady
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n]
    (oracle : SVDBlockReadyOracle m n) :
    BidiagonalizationStepOracle ℂ m n where
  U := oracle.U
  V := oracle.V
  unitary_U := oracle.unitary_U
  unitary_V := oracle.unitary_V
  ready := by
    intro A
    rcases oracle.blockReady A with ⟨_σ, _hσ, _h11, h12, h21⟩
    exact ⟨by
      intro i
      simpa [BidiagonalizationReady] using congrFun (congrFun h21 i) (),
      by
        intro j
        simpa [BidiagonalizationReady] using congrFun (congrFun h12 ()) j⟩

/-- Concrete complex one-step oracle obtained from the existing SVD spectral step. -/
noncomputable def bidiagonalizationStepOracle
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m] [Nonempty m]
    [Fintype n] [DecidableEq n] [LinearOrder n] [Nonempty n] :
    BidiagonalizationStepOracle ℂ m n :=
  bidiagonalizationStepOracleOfSVDBlockReady
    (svdBlockReadyOracleOfHeadSingularVectorData m n
      (svdHeadSingularVectorDataOfHeadBasisData m n (svdHeadBasisData m n)))

/--
Unconditional complex unitary bidiagonalization, routed through the
bidiagonalization rectangular descent framework.
-/
theorem exists_unitary_bidiagonalization
    {m n : Type u} [Fintype m] [DecidableEq m] [LinearOrder m]
    [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix m n ℂ) :
    HasUnitaryBidiagonalization A := by
  exact exists_unitary_bidiagonalization_oracle
    (fun {p q} [Fintype p] [DecidableEq p] [LinearOrder p] [Nonempty p]
      [Fintype q] [DecidableEq q] [LinearOrder q] [Nonempty q] =>
        bidiagonalizationStepOracle (m := p) (n := q))
    A

end MatDecompFormal.Instances
