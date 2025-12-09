import MatDecompFormal.Framework.Universe
open MatDecompFormal.Framework
set_option pp.universes true
#check (fun (x : PositiveSquareMat Nat) => x)
#check (fun (x y : PositiveSquareMat Nat) => (x,y))
