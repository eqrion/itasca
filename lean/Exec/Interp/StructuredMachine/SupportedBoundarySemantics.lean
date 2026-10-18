import Exec.Interp.StructuredMachine.CallSemantics
import Exec.Abs.Supported.PureCoverage
import Exec.Abs.Stateful.OwnershipStore
import Exec.Interp.StructuredMachine.ReturnSemantics
import Exec.Abs.SupportedState
namespace Exec.Interp.StructuredMachine

def supportedCallSemantics {allowed : instr → Prop} (language : Abs.Supported.Language allowed) : CallSemantics (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned where
  covered s ambient f rest index after frames covered step :=
    Abs.Supported.slice_instruction_covered s ambient f rest (.CALL (.mk_uN index)) after _ (.call _) language covered step
  ownership := by
    intro s ambient f rest index after frames step bounds owned
    exact ⟨Abs.Ownership.instruction_ownership bounds s ambient f rest (.CALL (.mk_uN index)) after _ [] (.call _)
      (owned.values.2 {f with code := .CALL (.mk_uN index)::after} (by simp))
      (fun frame member => owned.values.2 frame (by simp [member])) owned.values.1 step,owned.heap⟩
end Exec.Interp.StructuredMachine
namespace Exec.Interp.StructuredMachine
open Abs.Ownership

def supportedReturnSemantics {allowed : instr → Prop} : ReturnSemantics (Abs.SupportedState allowed) StatefulOwned where
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
end Exec.Interp.StructuredMachine
