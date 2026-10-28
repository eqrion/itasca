import Itasca.Runtime.Code.Local.Checking.ForwardBranchInstructionPrefix
import Itasca.Runtime.Code.Local.Relations.Control.BranchSuccessConditionalTransfer

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Actual conditional forward branching checks its condition and transfer,
retains the local skip address, and records its final jump's pending owner. -/
theorem compiler_branch_if_forward_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length) (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val+frame.results.val+1 = before.height.val)
    (conditionAt : before.before.val[before.before.val.length-1]? = some condition)
    (resumePosition : resume.val = before.function.code.val.length+3)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.results.val ≤ before.function.slot_count.val)
    (test : condition.val+1 ≤ before.function.slot_count.val)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨fixups,site,frames,code,siteAt,appended⟩ : ∃ fixups site,
      after.frames.val = before.frames.val.set index.val {frame with end_reachable := true,fixups} ∧
      after.function.code.val = before.function.code.val++branchIfInstructions frame.height source frame.results core.num.U32.MAX condition resume ∧
      site.val = before.function.code.length+(branchIfInstructions frame.height source frame.results core.num.U32.MAX condition resume).length-1 ∧
      fixups.val = frame.fixups.val++[site] := by
    by_cases elided : frame.results = 0#u32 ∨ source = frame.height
    · obtain ⟨code,fixups,site,siteAt,frames,appended⟩ := branch_if_elided_forward_success ops law before frame index depth source condition
        lookup position forward elided sourcePosition conditionAt after called
      exact ⟨fixups,site,frames,by simpa [branchIfInstructions,elided] using code,
        by simpa [branchIfInstructions,elided] using siteAt,appended⟩
    · obtain ⟨code,fixups,site,siteAt,frames,appended⟩ := branch_if_transfer_forward_success ops law before frame index depth source condition resume
        lookup position forward (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) sourcePosition conditionAt resumePosition after called
      exact ⟨fixups,site,frames,by simpa [branchIfInstructions,elided] using code,
        by simpa [branchIfInstructions,elided,Nat.add_sub_assoc] using siteAt,appended⟩
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_branch_tables ops law before after depth 1#u32 true called)
    (compiler_branch_stable_result ops law before after depth 1#u32 true (.Ok ()) called).capacity
    (compiler_branch_code_mono ops law before after depth 1#u32 true (.Ok ()) called)
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  have selected : after.frames.val[index.val]? = some {frame with end_reachable := true,fixups} := by
    rw [frames,List.getElem?_set_self bound]
  have pending := pending_instruction_fixup after index.val _ site selected (by change site ∈ fixups.val; simp [appended])
  refine held.append_open growth ?_ _ code ?_
  · intro position owned
    exact pending_instruction_replace index.val frame _ lookup frames rfl
      (by intro site member; change site ∈ fixups.val; rw [appended]; exact List.mem_append_left _ member) position owned
  · apply branchIfInstructions_open_checks after.function (PendingInstructionSite after) before.function.code.length
      frame.height source frame.results core.num.U32.MAX condition resume order (sourceFits.trans growth.slots) (test.trans growth.slots)
    · intro transfer
      change resume.val ≤ after.function.code.val.length
      rw [code,branchIfInstructions,if_neg transfer,List.length_append]
      simp only [List.length_cons,List.length_nil]
      omega
    · exact .inr (by rw [← siteAt]; exact pending)

end Itasca.Runtime.Code
