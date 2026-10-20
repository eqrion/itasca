import Exec.Code.Local.Checking.TableLoopInstructionPrefix
import Exec.Code.Local.Relations.Table.BranchTableLower
import Exec.Code.Local.Relations.Common.CoreInstructionAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std

/-- The actual dispatch and all target stubs establish the complete instruction
prefix. Source stack geometry supplies the selector, and the deferred dispatch
check is discharged against the completed side table. -/
theorem compiler_lower_table_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (stack : List valtype) (layout : CompilerLayout before (stack++[.I32]))
    (aligned : SourceAligned before)
    (depths : ∀ depth ∈ before.table_depths.val, depth.val < before.frames.val.length)
    (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (room : before.function.code.val.length+1+2*before.table_depths.val.length ≤ Usize.max)
    (tables : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (coordinate : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (nonempty : 0 < before.table_depths.val.length)
    (transfers : TableTransferBounds before)
    (heightFits : before.height.val ≤ before.function.slot_count.val)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨start,len,selector,emitted,startAt,count,operand,emission,run⟩ :=
    compiler_lower_table_success ops law before after called
  have selected := compiler_operand ops before (stack++[.I32]) layout 1#usize (by decide) (by simp)
  rw [operand,WP.spec_ok] at selected
  obtain ⟨word,equal,wordAt⟩ := selected
  have same : word = selector := core.result.Result.Ok.inj equal.symm
  subst word
  have selectorFits : selector.val+1 ≤ before.function.slot_count.val := by
    have height := layout.height
    simp [offset] at wordAt
    simp only [slots_append,slots, width] at height
    omega
  have deferred := emission.defer_new_instruction held
  have growth := emission.instructionCheckExtends
  obtain ⟨targets,built⟩ := run.built law
  simp only [List.drop_zero] at built
  obtain ⟨budget,code,sources,frame,appended,sourceAppend⟩ := emission
  subst emitted
  have codeSize : code.val.length = before.function.code.val.length+1 := by simp [appended]
  have sourceSize : sources.val.length = before.function.source_offsets.val.length+1 := by
    have size := congrArg List.length sourceAppend
    simpa only [List.length_map,List.length_append,List.length_singleton] using size
  have safe : TableLoopSafe {before with budget,function := {before.function with code,source_offsets := sources}} 0 Usize.max := by
    refine ⟨?_,depths,fixups.mono (by change before.function.code.val.length ≤ code.val.length; omega),?_,?_,coordinate⟩
    · change sources.val.length = code.val.length
      rw [sourceSize,codeSize,aligned]
    · change code.val.length+2*(before.table_depths.val.length-0) ≤ Usize.max
      simpa only [codeSize,Nat.sub_zero] using room
    · change before.function.jump_tables.val.length ≤ code.val.length
      omega
  have transfer : TableTransferBounds {before with budget,function := {before.function with code,source_offsets := sources}} := by
    intro depth member index frame found position
    have old := transfers depth member index frame found position
    exact ⟨old.1,fun loop => (old.2 loop).trans (by change before.function.code.val.length ≤ code.val.length; omega)⟩
  have final := run.instruction_prefix_except law safe le_rfl transfer heightFits deferred
  apply final.complete
  intro instruction found
  obtain ⟨fragment,finalCode,_⟩ := built.code_prefix
  have header : after.function.code.val[before.function.code.length]? = some (.JumpTable selector start len) := by
    rw [finalCode,appended,List.append_assoc]
    change (before.function.code.val++(.JumpTable selector start len :: fragment))[before.function.code.val.length]? = _
    simp
  rw [header] at found
  cases Option.some.inj found
  apply CoreInstructionBounds.accepts
  apply CoreInstructionBounds.jumpTable
  · have capacity := (run.fixed law).stable.capacity
    exact selectorFits.trans capacity
  · omega
  · change start.val+len.val ≤ after.function.jump_tables.val.length
    rw [built.tables,List.length_append,built.length]
    change start.val+len.val ≤ before.function.jump_tables.val.length+before.table_depths.val.length
    omega

end Exec.Code
