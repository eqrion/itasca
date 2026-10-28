import Exec.Code.Local.Checking.InstructionAppendEffect
import Exec.Code.Local.Checking.PendingInstructionReplace
import Exec.Code.Local.Checking.OpenInstructionFragment
import Exec.Code.Local.Checking.BranchInstructionAcceptance
import Exec.Code.Local.Relations.Control.BranchSkipForwardSafety
import Exec.Code.Local.Relations.Table.ControlTablePreservation
import Exec.Code.Local.Callbacks.Control.CompilerBranchMetadata
import Exec.Code.Local.Callbacks.Control.CompilerCodeMonotoneControl

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Actual forward branching preserves every old instruction check, validates
its transfer, and records the final jump's pending owner. The skip parameter
also covers branch-table target stubs. -/
theorem compiler_branch_forward_instruction_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val+frame.results.val+skip.val = before.height.val)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.results.val ≤ before.function.slot_count.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : before.function.code.val.length+2 ≤ Usize.max)
    (offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    InstructionAppendEffect before after := by
  obtain ⟨fixups,site,frames,code,siteAt,appended⟩ : ∃ fixups site,
      after.frames.val = before.frames.val.set index.val {frame with end_reachable := true,fixups} ∧
      after.function.code.val = before.function.code.val++branchInstructions frame.height source frame.results core.num.U32.MAX ∧
      site.val = before.function.code.length+(branchInstructions frame.height source frame.results core.num.U32.MAX).length-1 ∧
      fixups.val = frame.fixups.val++[site] := by
    by_cases elided : frame.results = 0#u32 ∨ source = frame.height
    · have effect := branch_elided_forward_with_skip ops law before frame index depth source skip lookup position forward elided
        sourcePosition fixupsFit (by omega) (by omega) coordinateFits
      rw [called,WP.spec_ok] at effect
      obtain ⟨code,fixups,site,siteAt,frames,appended⟩ := effect rfl
      exact ⟨fixups,site,frames,by simpa [branchInstructions,elided] using code,
        by simpa [branchInstructions,elided] using siteAt,appended⟩
    · have effect := branch_transfer_forward_with_skip ops law before frame index depth source skip lookup position forward
        (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) sourcePosition fixupsFit codeFits offsetsFit coordinateFits
      rw [called,WP.spec_ok] at effect
      obtain ⟨code,fixups,site,siteAt,frames,appended⟩ := effect rfl
      exact ⟨fixups,site,frames,by simpa [branchInstructions,elided] using code,
        by simpa [branchInstructions,elided,Nat.add_sub_assoc] using siteAt,appended⟩
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_branch_tables ops law before after depth skip false called)
    (compiler_branch_stable_result ops law before after depth skip false (.Ok ()) called).capacity
    (compiler_branch_code_mono ops law before after depth skip false (.Ok ()) called)
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  have selected : after.frames.val[index.val]? = some {frame with end_reachable := true,fixups} := by
    rw [frames,List.getElem?_set_self bound]
  have pending := pending_instruction_fixup after index.val _ site selected (by change site ∈ fixups.val; simp [appended])
  refine ⟨growth,_,code,?_,?_⟩
  · intro position owned
    exact pending_instruction_replace index.val frame _ lookup frames rfl
      (by intro site member; change site ∈ fixups.val; rw [appended]; exact List.mem_append_left _ member) position owned
  · apply branchInstructions_open_checks after.function (PendingInstructionSite after) before.function.code.length
      frame.height source frame.results core.num.U32.MAX order (sourceFits.trans growth.slots)
    exact .inr (by rw [← siteAt]; exact pending)

/-- Apply the concrete append effect to the current checked prefix. -/
theorem compiler_branch_forward_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val+frame.results.val+skip.val = before.height.val)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+frame.results.val ≤ before.function.slot_count.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : before.function.code.val.length+2 ≤ Usize.max)
    (offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after :=
  (compiler_branch_forward_instruction_effect ops law before after frame index depth source skip lookup position forward sourcePosition order sourceFits fixupsFit codeFits offsetsFit coordinateFits called).apply held

end Itasca.Runtime.Code
