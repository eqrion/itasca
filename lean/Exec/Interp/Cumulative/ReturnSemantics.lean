import Exec.Interp.StructuredMachine.ReturnSemantics
import Exec.Abs.CumulativeState
import Exec.Abs.Stateful.OwnershipStore
namespace Exec.Interp.Cumulative
open Abs.Ownership

def returnSemantics : StructuredMachine.ReturnSemantics Abs.CumulativeState StatefulOwned where
  covered := by
    intro s ambient f rest covered results
    cases rest with
    | nil => exact ⟨by simp [returnedState,Forall],covered.functions⟩
    | cons caller rest =>
      refine ⟨?_,covered.functions⟩
      intro frame member
      change frame ∈ {caller with vals := caller.vals++results}::rest at member
      rcases List.mem_cons.mp member with rfl | member
      · exact covered.active caller (by simp)
      · exact covered.active frame (by simp [member])
  ownership := by
    intro s ambient f rest results subset bounds owned
    have fresh := returnedState_owned results subset bounds owned.core
    cases rest <;> exact ⟨fresh.values,owned.heap⟩
end Exec.Interp.Cumulative
