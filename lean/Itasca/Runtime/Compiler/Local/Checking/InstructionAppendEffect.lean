import Itasca.Runtime.Compiler.Local.Checking.OpenInstructionFragment

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Concrete append effects separate local emission checks and ownership
transport from the retained prefix. This also supports temporary table builders. -/
def InstructionAppendEffect {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  InstructionCheckExtends before.function after.function ∧
    ∃ fragment : List runtime.bytecode.Instr,
      after.function.code.val = before.function.code.val++fragment ∧
      (∀ index, PendingInstructionSite before index → PendingInstructionSite after index) ∧
      (∀ index instruction, fragment[index]? = some instruction →
        OpenInstructionCheck after.function (PendingInstructionSite after) (before.function.code.length+index) instruction)

/-- Every recorded append effect preserves a complete prefix check. -/
theorem InstructionAppendEffect.apply {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (effect : InstructionAppendEffect before after) (held : CompilerInstructionPrefix before) :
    CompilerInstructionPrefix after := by
  obtain ⟨growth,fragment,code,owners,fresh⟩ := effect
  exact held.append_open growth owners fragment code fresh

/-- Metadata preparation followed by a branch append has the same concrete
append effect at the original instruction position. -/
theorem InstructionAppendEffect.prepend_unchanged {A : Type}
    {before middle after : runtime.compiler.FunctionCompiler A}
    (first : InstructionAppendEffect before middle)
    (unchanged : middle.function.code = before.function.code)
    (second : InstructionAppendEffect middle after) : InstructionAppendEffect before after := by
  obtain ⟨growth,_,_,owners,_⟩ := first
  obtain ⟨growth',fragment,code,owners',fresh⟩ := second
  refine ⟨growth.trans growth',fragment,?_,fun index owned => owners' index (owners index owned),?_⟩
  · simpa only [unchanged] using code
  · simpa only [unchanged] using fresh

/-- A table builder temporarily defers checking its one dispatch word until
its target rows have been appended. Every other stored instruction is checked. -/
def OpenInstructionPrefixExcept (function : runtime.bytecode.CompiledFunction) (pending : Nat → Prop)
    (omitted : Nat) : Prop :=
  ∀ index instruction, index ≠ omitted → function.code.val[index]? = some instruction →
    OpenInstructionCheck function pending index instruction

def CompilerInstructionPrefixExcept (compiler : runtime.compiler.FunctionCompiler A) (omitted : Nat) : Prop :=
  OpenInstructionPrefixExcept compiler.function (PendingInstructionSite compiler) omitted

/-- Appending a checked branch stub preserves every table-builder obligation
apart from its explicitly deferred dispatch word. -/
theorem InstructionAppendEffect.apply_except {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (effect : InstructionAppendEffect before after) (omitted : Nat)
    (held : CompilerInstructionPrefixExcept before omitted) : CompilerInstructionPrefixExcept after omitted := by
  obtain ⟨growth,fragment,code,owners,fresh⟩ := effect
  intro index instruction different found
  rw [code] at found
  by_cases prior : index < before.function.code.val.length
  · rw [List.getElem?_append_left prior] at found
    exact (held index instruction different found).grow growth (owners index)
  · rw [List.getElem?_append_right (by omega : before.function.code.val.length ≤ index)] at found
    have checked := fresh (index-before.function.code.val.length) instruction found
    have same : before.function.code.length+(index-before.function.code.val.length) = index := by
      change before.function.code.val.length+(index-before.function.code.val.length) = index
      omega
    simpa only [same] using checked

/-- Deferral is discharged by an actual check of the retained dispatch word. -/
theorem CompilerInstructionPrefixExcept.complete {A : Type} {compiler : runtime.compiler.FunctionCompiler A} {omitted : Nat}
    (held : CompilerInstructionPrefixExcept compiler omitted)
    (dispatch : ∀ instruction, compiler.function.code.val[omitted]? = some instruction →
      runtime.bytecode.CompiledFunction.instruction_valid compiler.function instruction = .ok true) :
    CompilerInstructionPrefix compiler := by
  intro index instruction found
  by_cases same : index = omitted
  · subst index
    exact .checked (dispatch instruction found)
  · exact held index instruction same found

end Itasca.Runtime.Compiler
