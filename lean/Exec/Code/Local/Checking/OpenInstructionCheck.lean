import Exec.Code.Local.Checking.CheckedInstructionPrefix
import Exec.Code.Local.Relations.Common.CoreInstructionAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Earlier bytecode may contain forward branches whose owner has not closed.
Resolved targets may equal the current end; final return emission makes that
end a valid instruction address. Other forms already pass the actual checker. -/
inductive OpenInstructionCheck (function : runtime.bytecode.CompiledFunction)
    (pending : Nat → Prop) (index : Nat) : runtime.bytecode.Instr → Prop
  | checked {instruction} (accepted : runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true) :
      OpenInstructionCheck function pending index instruction
  | jump {target} (ready : target.val ≤ function.code.length ∨ pending index) :
      OpenInstructionCheck function pending index (.Jump target)
  | zero {condition target} (slot : condition.val+1 ≤ function.slot_count.val)
      (ready : target.val ≤ function.code.length ∨ pending index) :
      OpenInstructionCheck function pending index (.JumpIfZero condition target)
  | nonzero {condition target} (slot : condition.val+1 ≤ function.slot_count.val)
      (ready : target.val ≤ function.code.length ∨ pending index) :
      OpenInstructionCheck function pending index (.JumpIfNonZero condition target)

/-- Numerical growth and preservation of pending owners retain a prefix check. -/
theorem OpenInstructionCheck.grow {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} {index instruction}
    (held : OpenInstructionCheck before pending index instruction)
    (growth : InstructionCheckExtends before after) (owners : pending index → next index) :
    OpenInstructionCheck after next index instruction := by
  have ready {target : U32} (prior : target.val ≤ before.code.length ∨ pending index) :
      target.val ≤ after.code.length ∨ next index := prior.imp (fun bound => bound.trans growth.code) owners
  cases held with
  | checked accepted => exact .checked (instruction_valid_monotone before after instruction growth accepted)
  | jump prior => exact .jump (ready prior)
  | zero slot prior => exact .zero (slot.trans growth.slots) (ready prior)
  | nonzero slot prior => exact .nonzero (slot.trans growth.slots) (ready prior)

/-- Strict final code growth publishes every resolved branch, while retaining
all earlier instruction checks and slot bounds. -/
theorem OpenInstructionCheck.publish {before after : runtime.bytecode.CompiledFunction}
    {index instruction} (held : OpenInstructionCheck before (fun _ => False) index instruction)
    (growth : InstructionCheckExtends before after) (strict : before.code.length < after.code.length) :
    runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true := by
  cases held with
  | checked accepted => exact instruction_valid_monotone before after instruction growth accepted
  | jump ready => exact (CoreInstructionBounds.jump ((ready.resolve_right id).trans_lt strict)).accepts
  | zero slot ready =>
    exact (CoreInstructionBounds.jumpIfZero (slot.trans growth.slots) ((ready.resolve_right id).trans_lt strict)).accepts
  | nonzero slot ready =>
    exact (CoreInstructionBounds.jumpIfNonZero (slot.trans growth.slots) ((ready.resolve_right id).trans_lt strict)).accepts

/-- All stored instructions, including bytes skipped after a source terminator,
retain their own check. Semantic reachability alone does not imply this fact. -/
def OpenInstructionPrefix (function : runtime.bytecode.CompiledFunction) (pending : Nat → Prop) : Prop :=
  ∀ index instruction, function.code.val[index]? = some instruction → OpenInstructionCheck function pending index instruction

/-- Appending the actual epilogue turns closed prefix checks into a complete
instruction certificate when the epilogue itself checks in the final function. -/
theorem OpenInstructionPrefix.publish {before after : runtime.bytecode.CompiledFunction}
    (held : OpenInstructionPrefix before (fun _ => False))
    (growth : InstructionCheckExtends before after) (fragment : List runtime.bytecode.Instr)
    (code : after.code.val = before.code.val++fragment) (nonempty : 0 < fragment.length)
    (fresh : ∀ instruction ∈ fragment,
      runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true) :
    CheckedInstructionPrefix after := by
  have strict : before.code.length < after.code.length := by
    change before.code.val.length < after.code.val.length
    rw [code,List.length_append]
    omega
  intro instruction member
  rw [code] at member
  rcases List.mem_append.mp member with old | new
  · obtain ⟨index,inside,found⟩ := List.getElem_of_mem old
    exact (held index instruction (by simp [List.getElem?_eq_getElem inside,found])).publish growth strict
  · exact fresh instruction new

end Exec.Code
