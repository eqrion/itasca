import Exec.Interp.StructuredMachine.ReturnStack
import Exec.Interp.Machines.Core.CoreOwnership
namespace Exec.Interp.StructuredMachine

/-- Returning only exposes saved caller syntax and values already in the
callee. Concrete cumulative source predicates prove these two facts. -/
structure ReturnSemantics (supported : Abs.AState → Prop)
    (owned : Abs.Ownership.Bounds → Abs.AState → Prop) : Prop where
  covered : ∀ {s ambient f rest}, supported ⟨s,ambient,f::rest,[]⟩ → ∀ results,
    supported (returnedState s ambient rest results)
  ownership : ∀ {s ambient f rest} results, (∀ value ∈ results,value ∈ f.vals) →
    ∀ bounds, owned bounds ⟨s,ambient,f::rest,[]⟩ → owned bounds (returnedState s ambient rest results)
end Exec.Interp.StructuredMachine
