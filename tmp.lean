import MatDecompFormal.Framework.Universe
open MatDecompFormal.Framework
#check PositiveSquareMat
#check (⟨SquareMat.of (Matrix.zero (Fin 1) (Fin 1)), by decide⟩ : PositiveSquareMat Nat)
