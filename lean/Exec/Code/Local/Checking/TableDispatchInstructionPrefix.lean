import Exec.Code.Local.Checking.InstructionAppendEffect

namespace Exec.Code
open Aeneas Aeneas.Std

/-- An emitted dispatch word can be deferred at its exact new position while
every previously stored instruction retains its ordinary prefix check. -/
theorem Emitted.defer_new_instruction {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction)
    (held : CompilerInstructionPrefix before) :
    CompilerInstructionPrefixExcept after before.function.code.length := by
  have growth := emitted.instructionCheckExtends
  have frames : after.frames = before.frames := by
    obtain ⟨budget,code,sources,rfl,_,_⟩ := emitted
    rfl
  have appended : after.function.code.val = before.function.code.val++[instruction] := by
    obtain ⟨budget,code,sources,rfl,appended,_⟩ := emitted
    exact appended
  intro index selected different found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [appended,List.length_append,List.length_singleton] at bound
  change index ≠ before.function.code.val.length at different
  have prior : index < before.function.code.val.length := by omega
  rw [appended,List.getElem?_append_left prior] at found
  apply (held index selected found).grow growth
  intro owned
  simpa only [PendingInstructionSite,frames] using owned

/-- Metadata-only changes preserve all prefix checks from numerical growth and
unchanged ownership. No new instruction obligation is introduced. -/
theorem InstructionAppendEffect.of_unchanged_code {A : Type}
    {before after : runtime.compiler.FunctionCompiler A}
    (growth : InstructionCheckExtends before.function after.function)
    (code : after.function.code = before.function.code) (frames : after.frames = before.frames) :
    InstructionAppendEffect before after := by
  refine ⟨growth,[],by simpa using congrArg alloc.vec.Vec.val code,?_,by simp⟩
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

/-- The target-row append preceding each actual table stub preserves every
check, including the temporary dispatch exception. Budget state is arbitrary. -/
theorem instruction_append_effect_jump_table {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (budget : runtime.compiler.Budget A) (table : alloc.vec.Vec U32) (target : U32)
    (appended : table.val = before.function.jump_tables.val++[target]) :
    InstructionAppendEffect before {before with budget,function := {before.function with jump_tables := table}} := by
  apply InstructionAppendEffect.of_unchanged_code (before := before)
    (after := {before with budget,function := {before.function with jump_tables := table}}) _ rfl rfl
  refine ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,?_⟩
  change before.function.jump_tables.val.length ≤ table.val.length
  rw [appended,List.length_append,List.length_singleton]
  omega

end Exec.Code
