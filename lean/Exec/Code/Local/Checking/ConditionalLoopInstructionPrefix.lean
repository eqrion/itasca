import Exec.Code.Local.Checking.ConditionalForwardInstructionPrefix
import Exec.Code.Local.Relations.Control.BranchSuccessConditionalLoop

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Actual conditional loop branching checks its selector and transfer, retains
its backward target, and preserves all previously recorded pending owners. -/
theorem compiler_branch_if_loop_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length) (loop : frame.kind = .Loop)
    (sourcePosition : source.val+frame.params.val+1 = before.height.val)
    (conditionAt : before.before.val[before.before.val.length-1]? = some condition)
    (resumePosition : resume.val = before.function.code.val.length+3)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.params.val ≤ before.function.slot_count.val)
    (test : condition.val+1 ≤ before.function.slot_count.val)
    (target : frame.start_pc.val ≤ before.function.code.length)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have effect : after.function.code.val = before.function.code.val++branchIfInstructions frame.height source frame.params frame.start_pc condition resume ∧
      after.frames = before.frames := by
    by_cases elided : frame.params = 0#u32 ∨ source = frame.height
    · obtain ⟨code,frames⟩ := branch_if_elided_loop_success ops law before frame index depth source condition
        lookup position loop elided sourcePosition conditionAt after called
      exact ⟨by simpa [branchIfInstructions,elided] using code,frames⟩
    · obtain ⟨code,frames⟩ := branch_if_transfer_loop_success ops law before frame index depth source condition resume
        lookup position loop (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) sourcePosition conditionAt resumePosition after called
      exact ⟨by simpa [branchIfInstructions,elided] using code,frames⟩
  obtain ⟨code,frames⟩ := effect
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_branch_tables ops law before after depth 1#u32 true called)
    (compiler_branch_stable_result ops law before after depth 1#u32 true (.Ok ()) called).capacity
    (compiler_branch_code_mono ops law before after depth 1#u32 true (.Ok ()) called)
  refine held.append_open growth ?_ _ code ?_
  · intro index owned
    simpa only [PendingInstructionSite,frames] using owned
  · apply branchIfInstructions_open_checks after.function (PendingInstructionSite after) before.function.code.length
      frame.height source frame.params frame.start_pc condition resume order (sourceFits.trans growth.slots) (test.trans growth.slots)
    · intro transfer
      change resume.val ≤ after.function.code.val.length
      rw [code,branchIfInstructions,if_neg transfer,List.length_append]
      simp only [List.length_cons,List.length_nil]
      omega
    · exact .inl (target.trans growth.code)

end Exec.Code
