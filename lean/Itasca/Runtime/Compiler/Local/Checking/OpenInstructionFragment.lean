import Itasca.Runtime.Compiler.Local.Checking.OpenInstructionCompiler

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Appending a control fragment retains old checks and supplies each new word's
own check at its absolute bytecode coordinate, including pending branch sites. -/
theorem OpenInstructionPrefix.append_open {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} (held : OpenInstructionPrefix before pending)
    (growth : InstructionCheckExtends before after) (owners : ∀ index, pending index → next index)
    (fragment : List runtime.bytecode.Instr) (code : after.code.val = before.code.val++fragment)
    (fresh : ∀ index instruction, fragment[index]? = some instruction →
      OpenInstructionCheck after next (before.code.length+index) instruction) :
    OpenInstructionPrefix after next := by
  intro index instruction found
  rw [code] at found
  by_cases inside : index < before.code.val.length
  · rw [List.getElem?_append_left inside] at found
    exact (held index instruction found).grow growth (owners index)
  · rw [List.getElem?_append_right (by omega : before.code.val.length ≤ index)] at found
    have checked := fresh (index-before.code.val.length) instruction found
    have same : before.code.length+(index-before.code.val.length) = index := by
      change before.code.val.length+(index-before.code.val.length) = index
      omega
    simpa only [same] using checked

end Itasca.Runtime.Code
