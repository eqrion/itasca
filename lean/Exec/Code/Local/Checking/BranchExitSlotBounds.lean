import Exec.Code.Local.Checking.FrameExitSlotBounds
import Exec.Code.Local.Checking.ConditionalLoopInstructionPrefix
import Exec.Code.Local.Relations.Table.BranchTableSkip
import Exec.Code.Local.Relations.Table.BranchTableArguments

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The source transfer interval pays for a recorded forward exit. This holds
for ordinary branches and selector-skipping table stubs. -/
theorem compiler_branch_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (frame : runtime.compiler.Frame) (depth source skip : U32)
    (found : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (sourcePosition : source.val+(frameBranchWidth frame).val+skip.val = before.height.val)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+(frameBranchWidth frame).val ≤ before.function.slot_count.val)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have capacity := (compiler_branch_stable_result ops law before after depth skip false (.Ok ()) called).capacity
  by_cases loop : frame.kind = .Loop
  · have operands : source.val+frame.params.val+skip.val = before.height.val := by
      simpa only [frameBranchWidth,loop] using sourcePosition
    obtain ⟨_,frames⟩ := compiler_branch_loop_skip_success ops law before frame index depth source skip
      found position loop operands after called
    exact held.retained (congrArg alloc.vec.Vec.val frames) capacity
  · have width : frameBranchWidth frame = frame.results := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    obtain ⟨fixups,frames,_⟩ := compiler_branch_forward_skip_success ops law before frame index depth source skip
      found position loop (by simpa only [width] using sourcePosition) after called
    apply held.record index.val frame fixups frames capacity
    rw [width] at sourceFits
    omega

/-- A conditional branch records the same checked exit interval while retaining
its condition and local continuation in the ordinary instruction invariant. -/
theorem compiler_branch_if_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (frame : runtime.compiler.Frame) (depth source condition resume : U32)
    (found : before.frames.val[index.val]? = some frame)
    (position : index.val+depth.val+1 = before.frames.val.length)
    (sourcePosition : source.val+(frameBranchWidth frame).val+1 = before.height.val)
    (conditionAt : before.before.val[before.before.val.length-1]? = some condition)
    (resumeAt : resume.val = before.function.code.val.length+3)
    (order : frame.height.val ≤ source.val)
    (sourceFits : source.val+(frameBranchWidth frame).val ≤ before.function.slot_count.val)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have capacity := (compiler_branch_stable_result ops law before after depth 1#u32 true (.Ok ()) called).capacity
  by_cases loop : frame.kind = .Loop
  · have operands : source.val+frame.params.val+1 = before.height.val := by
      simpa only [frameBranchWidth,loop] using sourcePosition
    have frames : after.frames = before.frames := by
      by_cases elided : frame.params = 0#u32 ∨ source = frame.height
      · exact (branch_if_elided_loop_success ops law before frame index depth source condition
          found position loop elided operands conditionAt after called).2
      · exact (branch_if_transfer_loop_success ops law before frame index depth source condition resume
          found position loop (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) operands conditionAt resumeAt after called).2
    exact held.retained (congrArg alloc.vec.Vec.val frames) capacity
  · have width : frameBranchWidth frame = frame.results := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    have operands : source.val+frame.results.val+1 = before.height.val := by simpa only [width] using sourcePosition
    obtain ⟨fixups,frames⟩ : ∃ fixups, after.frames.val = before.frames.val.set index.val
        {frame with end_reachable := true,fixups} := by
      by_cases elided : frame.results = 0#u32 ∨ source = frame.height
      · obtain ⟨_,fixups,_,_,frames,_⟩ := branch_if_elided_forward_success ops law before frame index depth source condition
          found position loop elided operands conditionAt after called
        exact ⟨fixups,frames⟩
      · obtain ⟨_,fixups,_,_,frames,_⟩ := branch_if_transfer_forward_success ops law before frame index depth source condition resume
          found position loop (fun eq => elided (.inl eq)) (fun eq => elided (.inr eq)) operands conditionAt resumeAt after called
        exact ⟨fixups,frames⟩
    apply held.record index.val frame fixups frames capacity
    rw [width] at sourceFits
    omega

end Itasca.Runtime.Code
