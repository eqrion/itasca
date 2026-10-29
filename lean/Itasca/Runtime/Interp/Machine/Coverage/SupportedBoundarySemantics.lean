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

namespace Itasca.Runtime.Interp.StructuredMachine
open Abs.Ownership

/-- A defined call keeps the active frames within the supported source grammar. -/
theorem call_supported (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (index : Nat)
    (after : List instr) (frames : List Abs.AFrame)
    (covered : Abs.SupportedState ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩)
    (step : Abs.astep ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩ = .next ⟨s,ambient,frames,[]⟩) :
    Abs.SupportedState ⟨s,ambient,frames,[]⟩ :=
  Abs.Supported.slice_instruction_covered s ambient f rest (.CALL (.mk_uN index)) after _ (.call _) covered step

/-- A defined call preserves stateful reference ownership. -/
theorem call_owned (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (index : Nat)
    (after : List instr) (frames : List Abs.AFrame)
    (step : Abs.astep ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩ = .next ⟨s,ambient,frames,[]⟩) :
    ∀ bounds, Abs.Ownership.StatefulOwned bounds ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩ →
      Abs.Ownership.StatefulOwned bounds ⟨s,ambient,frames,[]⟩ := by
  intro bounds owned
  exact ⟨Abs.Ownership.instruction_ownership bounds s ambient f rest (.CALL (.mk_uN index)) after _ [] (.call _)
    (owned.values.2 {f with code := .CALL (.mk_uN index)::after} (by simp))
    (fun frame member => owned.values.2 frame (by simp [member])) owned.values.1 step,owned.heap⟩

/-- Returning exposes only saved caller syntax, so the state stays supported. -/
theorem return_supported {s ambient f rest} (covered : Abs.SupportedState ⟨s,ambient,f::rest,[]⟩) (results : List val) :
    Abs.SupportedState (returnedState s ambient rest results) := by
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
    ∀ bounds, Abs.Ownership.StatefulOwned bounds ⟨s,ambient,f::rest,[]⟩ →
      Abs.Ownership.StatefulOwned bounds (returnedState s ambient rest results) := by
  intro bounds owned
  have fresh := returnedState_owned results subset bounds owned.core
  cases rest <;> exact ⟨fresh.values,owned.heap⟩

end Itasca.Runtime.Interp.StructuredMachine
