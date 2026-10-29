import Itasca.Runtime.Compiler.Local.Checking.FrameExitSlotBounds
import Itasca.Runtime.Compiler.Local.Checking.ConditionalInstructionPrefix
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSkip
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableArguments
import Itasca.Runtime.Compiler.Local.Checking.NumericInstructionPrefix

/-!
Exit-slot bounds for branch instructions and their public compiler callbacks. The callback theorem includes observation and branch-specific slot obligations.
-/

/-! ## Branch Exit Slot Bounds -/

section

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

end

/-! ## Branch Callback Exit Slots -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Actual operand observation preserves every recorded forward-exit region. -/
theorem compiler_observe_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have frame := compiler_observe_frame ops law before state
  rw [called,WP.spec_ok] at frame
  dsimp only at frame
  have frames : after.frames = before.frames := by rw [frame]
  exact held.retained (congrArg alloc.vec.Vec.val frames) (compiler_observe_stable ops law before after state called).capacity

/-- Lift a source-derived raw branch preservation proof through actual br and
its final dead-stack observation. Forward/loop adapters discharge the local
branch premise; no body-level target trace is assumed here. -/
theorem compiler_br_callback_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : FrameExitSlotBounds before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 0#u32 false = .ok (.Ok (),middle) →
      FrameExitSlotBounds middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at called
  split at called
  · rename_i live
    obtain ⟨⟨status,middle⟩,emitted,rest⟩ := bind_ok_inv _ _ _ called
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      have checked := branch live middle emitted
      apply compiler_observe_exit_slots ops law {middle with reachable := false} after state _ rest
      exact checked.retained rfl le_rfl
  · exact compiler_observe_exit_slots ops law before after state held called

/-- Lift source-derived conditional branch checking through actual br_if and
its stack observation, including a dead prefix that emits no branch. -/
theorem compiler_br_if_callback_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : FrameExitSlotBounds before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),middle) →
      FrameExitSlotBounds middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at called
  split at called
  · rename_i live
    obtain ⟨⟨status,middle⟩,emitted,rest⟩ := bind_ok_inv _ _ _ called
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      exact compiler_observe_exit_slots ops law middle after state (branch live middle emitted) rest
  · exact compiler_observe_exit_slots ops law before after state held called

end Itasca.Runtime.Code

end
