import MatDecompFormal.Instances.PLU.Driver

namespace MatDecompFormal.Instances

open Matrix
open MatDecompFormal.Framework

variable {ι : Type} {R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [DivisionRing R]

/-- Type-indexed PLU existence theorem. -/
theorem exists_plu_decomposition (A : Matrix ι ι R) : HasPLU A := by
  by_cases h_sub : Subsingleton ι
  · exact base_plu_subsingleton A
  · let stepData : SquareStrategyData R PLU_P :=
      plu_strategy_data
    let inst : SquareSubtypeInductionInstance R :=
      mkSquareSubtypeInductionInstanceFromStrategy
        PLU_P
        plu_base_univ
        stepData
    have hP :
        inst.P (SquareUniverse.ofMatrix A) :=
      SquareSubtypeInductionInstance.prove_for_matrix
        (inst := inst) A
    exact hP

end MatDecompFormal.Instances
