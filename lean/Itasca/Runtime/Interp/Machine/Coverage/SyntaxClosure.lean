import Itasca.Runtime.SourceMachine.Supported.PureCoverage
import Itasca.Runtime.SourceMachine.Stateful.TableSet
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Machine.Frames.ReturnStack
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Machine.SuspendedPoint

/-!
Sections, each formerly its own module: SupportedBoundarySemantics, SyntaxClosure.
-/

/-! ## SupportedBoundarySemantics -/

section

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

end

/-! ## SyntaxClosure -/

section

/-!
A step keeps the frame's code and labels within the binary instruction grammar.

Main declarations: `SyntaxClosure`. A direct consumer is `Interp.Machine.Control.BranchIfOwned`.
-/

namespace Itasca.Runtime.Interp.Machine
/-- A step keeps the frame's code and labels within the binary instruction grammar. -/
def SyntaxClosure (before after : SourceMachine.AFrame) : Prop :=
  SourceMachine.FrameSupported before → SourceMachine.FrameSupported after

theorem SyntaxClosure.refl (f : SourceMachine.AFrame) : SyntaxClosure f f := fun h => h

theorem SyntaxClosure.tail (f : SourceMachine.AFrame) (op : instr) (after : List instr)
    (locals values : List val) :
    SyntaxClosure { f with code := op :: after } { f with code := after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  exact ⟨fun i hi => code i (List.mem_cons_of_mem _ hi), labels⟩

theorem SyntaxClosure.replace (f : SourceMachine.AFrame) (op next : instr) (after : List instr)
    (locals values : List val) (nextAllowed : SourceMachine.BinaryInstr next) :
    SyntaxClosure { f with code := op :: after } { f with code := next :: after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  refine ⟨?_, labels⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl | member
  · exact nextAllowed
  · exact code i (List.mem_cons_of_mem _ member)

theorem SyntaxClosure.branch (f : SourceMachine.AFrame) (depth : Nat) (label : SourceMachine.Label)
    (lookup : f.labels[depth]? = some label) (values : List val) :
    SyntaxClosure f { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := values } := by
  rintro ⟨code, labels⟩
  have retained := labels label (List.mem_of_getElem? lookup)
  constructor
  · intro i hi
    rcases List.mem_append.mp hi with member | member
    · exact retained.1 i member
    · exact retained.2 i member
  · intro next member
    exact labels next (List.mem_of_mem_drop member)

end Itasca.Runtime.Interp.Machine

end
