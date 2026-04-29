import Mathlib.Data.FinEnum
import Mathlib.Order.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Algebra.Ring.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Block


namespace MatDecompFormal.Framework
open FinEnum Matrix

/-!
`Framework.FinEnum` packages the canonical bridge from the internal `Fin` proof
layer to the external `FinEnum` presentation layer.

Within the project, the intended reading is:

* do the main construction and proof work on `Fin`;
* use the order isomorphisms in this file to present the final result on `FinEnum`.
-/

/--
Provide a canonical `LinearOrder` instance for any `FinEnum` type `α`.
The order relation `i ≤ j` is defined by comparing the enumeration indices of `i` and `j`.
-/
noncomputable instance LinearOrder.ofFinEnum (α : Type*) [FinEnum α] : LinearOrder α :=
  LinearOrder.lift' (@equiv α _) (equiv.injective)


/--
`orderIsoOfFinEnum` constructs the canonical bridge between the external
`FinEnum` presentation layer and the internal `Fin` proof layer.

Instance files should read this map from right to left when proving results
internally, and from left to right when exporting the final `FinEnum` theorem.
-/
noncomputable def orderIsoOfFinEnum (α : Type*) [FinEnum α] : α ≃o Fin (card α) :=
{
  toEquiv := equiv,
  map_rel_iff' := by intro a b; rfl
}

/--
`FinEnum.orderIsoOfCardEq` constructs an order isomorphism `α ≃o β` whenever
`α` and `β` have equal cardinality.
-/
noncomputable def FinEnum.orderIsoOfCardEq {α β} [FinEnum α] [FinEnum β]
    (h : card α = card β) : α ≃o β :=
  (orderIsoOfFinEnum α).trans ((Fin.castOrderIso h).trans (orderIsoOfFinEnum β).symm)

end MatDecompFormal.Framework
