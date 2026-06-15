import MatDecompFormal.Instances.LDL.Strategy

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

open scoped ComplexOrder

section Presentation

variable {ι : Type*}

noncomputable def ldl_framework_inst {R : Type*} [RCLike R] [TrivialStar R] :
    SquareSubtypeInductionInstance R :=
  mkSquareSubtypeInductionInstanceFromStrategy
    LDL_P
    ldl_base_univ
    ldl_strategy_data

/--
Primary LDL theorem routed through the generic subtype-induction template, using
a Schur-complement strategy core.
-/
theorem exists_ldl_decomposition
    {R : Type*} [RCLike R] [TrivialStar R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι R) (hA : A.PosDef) :
    HasLDLDecomposition A := by
  have hP :
      (ldl_framework_inst : SquareSubtypeInductionInstance R).P
        (SquareUniverse.ofMatrix A) :=
    SquareSubtypeInductionInstance.prove_for_matrix
      (inst := ldl_framework_inst) A
  exact hP hA

end Presentation

end MatDecompFormal.Instances
