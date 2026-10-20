import Exec.Code.Local.Checking.ForwardBranchInstructionPrefix
import Exec.Code.Local.Relations.Control.BranchSkipLoopSafety

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Actual loop branching checks its overlap-safe transfer and retained backward
target, preserving every earlier pending owner. Skip also covers table stubs. -/
theorem compiler_branch_loop_instruction_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (loop : frame.kind = .Loop)
    (sourcePosition : source.val+frame.params.val+skip.val = before.height.val)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.params.val ≤ before.function.slot_count.val)
    (target : frame.start_pc.val ≤ before.function.code.length)
    (codeFits : before.function.code.val.length+2 ≤ Usize.max)
    (offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    InstructionAppendEffect before after := by
  have effect : after.function.code.val = before.function.code.val++branchInstructions frame.height source frame.params frame.start_pc ∧
      after.frames = before.frames := by
    by_cases elided : frame.params = 0#u32 ∨ source = frame.height
    · have effect := branch_elided_loop_with_skip ops law before frame index depth source skip lookup position loop elided
        sourcePosition (by omega) (by omega) coordinateFits
      rw [called,WP.spec_ok] at effect
      obtain ⟨code,frames⟩ := effect rfl
      exact ⟨by simpa [branchInstructions,elided] using code,frames⟩
    · have effect := branch_transfer_loop_with_skip ops law before frame index depth source skip lookup position loop
        (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) sourcePosition codeFits offsetsFit coordinateFits
      rw [called,WP.spec_ok] at effect
      obtain ⟨code,frames⟩ := effect rfl
      exact ⟨by simpa [branchInstructions,elided] using code,frames⟩
  obtain ⟨code,frames⟩ := effect
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_branch_tables ops law before after depth skip false called)
    (compiler_branch_stable_result ops law before after depth skip false (.Ok ()) called).capacity
    (compiler_branch_code_mono ops law before after depth skip false (.Ok ()) called)
  refine ⟨growth,_,code,?_,?_⟩
  · intro index owned
    simpa only [PendingInstructionSite,frames] using owned
  · exact branchInstructions_open_checks after.function (PendingInstructionSite after) before.function.code.length
      frame.height source frame.params frame.start_pc order (sourceFits.trans growth.slots) (.inl (target.trans growth.code))

/-- Apply the concrete append effect to the current checked prefix. -/
theorem compiler_branch_loop_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (loop : frame.kind = .Loop)
    (sourcePosition : source.val+frame.params.val+skip.val = before.height.val)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.params.val ≤ before.function.slot_count.val)
    (target : frame.start_pc.val ≤ before.function.code.length)
    (codeFits : before.function.code.val.length+2 ≤ Usize.max)
    (offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after :=
  (compiler_branch_loop_instruction_effect ops law before after frame index depth source skip lookup position loop sourcePosition order sourceFits target codeFits offsetsFit coordinateFits called).apply held

end Exec.Code
