import Itasca.Runtime.SourceMachine.Supported.PureCoverage
import Itasca.Runtime.SourceMachine.Stateful.OwnershipStore
import Itasca.Runtime.SourceMachine.SupportedState
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Machine.Frames.ReturnStack
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership

/-!
A defined call keeps the active frames within the supported source grammar.

Main declarations: `call_supported` and `return_owned`. A direct consumer is `Interp.Machine.Calls.StructuredCall`.
-/

namespace Itasca.Runtime.Interp.Machine
open SourceMachine.Ownership

/-- A defined call keeps the active frames within the supported source grammar. -/
theorem call_supported (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (index : Nat)
    (after : List instr) (frames : List SourceMachine.AFrame)
    (covered : SourceMachine.SupportedState ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩)
    (step : SourceMachine.astep ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩ = .next ⟨s,ambient,frames,[]⟩) :
    SourceMachine.SupportedState ⟨s,ambient,frames,[]⟩ :=
  SourceMachine.Supported.slice_instruction_covered s ambient f rest (.CALL (.mk_uN index)) after _ (.call _) covered step

/-- A defined call preserves stateful reference ownership. -/
theorem call_owned (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (index : Nat)
    (after : List instr) (frames : List SourceMachine.AFrame)
    (step : SourceMachine.astep ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩ = .next ⟨s,ambient,frames,[]⟩) :
    ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩ →
      SourceMachine.Ownership.StatefulOwned bounds ⟨s,ambient,frames,[]⟩ := by
  intro bounds owned
  exact ⟨SourceMachine.Ownership.instruction_ownership bounds s ambient f rest (.CALL (.mk_uN index)) after _ [] (.call _)
    (owned.values.2 {f with code := .CALL (.mk_uN index)::after} (by simp))
    (fun frame member => owned.values.2 frame (by simp [member])) owned.values.1 step,owned.heap⟩

/-- Returning exposes only saved caller syntax, so the state stays supported. -/
theorem return_supported {s ambient f rest} (covered : SourceMachine.SupportedState ⟨s,ambient,f::rest,[]⟩) (results : List val) :
    SourceMachine.SupportedState (returnedState s ambient rest results) := by
  cases rest with
  | nil => exact ⟨by simp [returnedState,Forall],covered.functions⟩
  | cons caller rest =>
    refine ⟨?_,covered.functions⟩
    intro frame member
    change frame ∈ {caller with vals := caller.vals++results}::rest at member
    rcases List.mem_cons.mp member with rfl | member
    · exact covered.active caller (by simp)
    · exact covered.active frame (by simp [member])

/-- Returning callee values preserves stateful reference ownership. -/
theorem return_owned {s ambient f rest} (results : List val) (subset : ∀ value ∈ results, value ∈ f.vals) :
    ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds ⟨s,ambient,f::rest,[]⟩ →
      SourceMachine.Ownership.StatefulOwned bounds (returnedState s ambient rest results) := by
  intro bounds owned
  have fresh := returned_state_owned results subset bounds owned.core
  cases rest <;> exact ⟨fresh.values,owned.heap⟩

end Itasca.Runtime.Interp.Machine
