import Itasca.Runtime.Compiler.Local.Checking.ScopeEntryInstructionPrefix
import Itasca.Runtime.Compiler.Local.Coordinates.ScalarSourceCoordinates
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessConditional
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericInstructionPublication
import Itasca.Runtime.Compiler.Local.Lowering.Table.ScalarTablePreservation
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Source.StartJumpTableBounds
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSkipSafety

/-!
Sections, each formerly its own module: ScalarExitSlotBounds, ConditionalInstructionPrefix, NumericInstructionPrefix, BranchCallbackExitSlots, BranchCallbackInstructionPrefix, DeadInstructionPrefix, TerminalInstructionPrefix, NoopInstructionPrefix, TableCallbackExitSlots, LoopBranchInstructionPrefix.
-/

/-! ## ScalarExitSlotBounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Ordinary metadata retention preserves all previously recorded result regions. -/
theorem CompilerOrdinaryStable.exit_slots {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerOrdinaryStable before after) (held : FrameExitSlotBounds before) : FrameExitSlotBounds after :=
  held.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity

end Itasca.Runtime.Compiler

end

/-! ## ConditionalInstructionPrefix -/

section

/-!
Checked instruction-prefix preservation for forward and loop conditional branches, used by branch callback certification.
-/

/-! ## Conditional Forward Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
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
  · apply branch_if_instructions_open_checks after.function (PendingInstructionSite after) before.function.code.length
      frame.height source frame.results core.num.U32.MAX condition resume order (sourceFits.trans growth.slots) (test.trans growth.slots)
    · intro transfer
      change resume.val ≤ after.function.code.val.length
      rw [code,branchIfInstructions,if_neg transfer,List.length_append]
      simp only [List.length_cons,List.length_nil]
      omega
    · exact .inr (by rw [← siteAt]; exact pending)

end Itasca.Runtime.Compiler

end

/-! ## Conditional Loop Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
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
  · apply branch_if_instructions_open_checks after.function (PendingInstructionSite after) before.function.code.length
      frame.height source frame.params frame.start_pc condition resume order (sourceFits.trans growth.slots) (test.trans growth.slots)
    · intro transfer
      change resume.val ≤ after.function.code.val.length
      rw [code,branchIfInstructions,if_neg transfer,List.length_append]
      simp only [List.length_cons,List.length_nil]
      omega
    · exact .inl (target.trans growth.code)

end Itasca.Runtime.Compiler

end

end

/-! ## NumericInstructionPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std SourceMachine.Numeric

/-- Observation preserves every instruction's operand check and pending branch
owner, including in an unreachable source region. -/
theorem compiler_observe_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have stable := compiler_observe_stable ops law before after state called
  have frame := compiler_observe_frame ops law before state
  rw [called,WP.spec_ok] at frame
  dsimp only at frame
  have growth : InstructionCheckExtends before.function after.function := by
    refine ⟨stable.capacity,?_,?_,?_,?_,?_⟩ <;> rw [frame] <;> exact le_rfl
  have same : after.function.code.val = before.function.code.val := by rw [frame]
  refine held.append growth ?_ [] (by simpa using same) (by simp)
  intro index owned
  have frames : after.frames = before.frames := by rw [frame]
  simpa only [PendingInstructionSite,frames] using owned

end Itasca.Runtime.Compiler

end

/-! ## BranchCallbackExitSlots -/

section

/-!
Exit-slot bounds for branch instructions and their public compiler callbacks. The callback theorem includes observation and branch-specific slot obligations.
-/

/-! ## Branch Exit Slot Bounds -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Branch Callback Exit Slots -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

end

/-! ## BranchCallbackInstructionPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Lift a source-derived raw branch preservation proof through actual br and
its final dead-stack observation. Forward/loop adapters discharge the local
branch premise; no body-level target trace is assumed here. -/
theorem compiler_br_callback_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : CompilerInstructionPrefix before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 0#u32 false = .ok (.Ok (),middle) →
      CompilerInstructionPrefix middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
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
      apply compiler_observe_open_instructions ops law {middle with reachable := false} after state _ rest
      have owners : PendingInstructionSite {middle with reachable := false} = PendingInstructionSite middle := by
        funext index
        rfl
      simpa only [CompilerInstructionPrefix,owners] using checked
  · exact compiler_observe_open_instructions ops law before after state held called

/-- Lift source-derived conditional branch checking through actual br_if and
its stack observation, including a dead prefix that emits no branch. -/
theorem compiler_br_if_callback_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : CompilerInstructionPrefix before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),middle) →
      CompilerInstructionPrefix middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
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
      exact compiler_observe_open_instructions ops law middle after state (branch live middle emitted) rest
  · exact compiler_observe_open_instructions ops law before after state held called

/-- Every ordinary dead opcode performs only observation, regardless of its
immediates or numeric/reference/SIMD family. -/
theorem compiler_dead_op_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false) (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  unfold runtime.compiler.lower.FunctionCompiler.op at called
  rw [if_neg (by simp [dead])] at called
  exact compiler_observe_open_instructions ops law before after state held called

end Itasca.Runtime.Compiler

end

/-! ## DeadInstructionPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every dead ordinary lowerer observes without changing code or frames.
Both maintained invariants survive independently of the opcode or immediates. -/
theorem compiler_dead_op_checked_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false) (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  have checked := compiler_dead_op_open_instructions ops law before after state opcode a b bits dead held called
  unfold runtime.compiler.lower.FunctionCompiler.op at called
  rw [if_neg (by simp [dead])] at called
  exact ⟨checked,compiler_observe_exit_slots ops law before after state exits called⟩

end Itasca.Runtime.Compiler

end

/-! ## TerminalInstructionPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Ordinary append effects preserve all older checks when frame ownership is
unchanged, including terminal callbacks that subsequently become unreachable. -/
theorem CompilerInstructionPrefix.append_with_frames {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} (held : CompilerInstructionPrefix before)
    (growth : InstructionCheckExtends before.function after.function) (frames : after.frames = before.frames)
    (fragment : List runtime.bytecode.Instr) (code : after.function.code.val = before.function.code.val++fragment)
    (fresh : ∀ instruction ∈ fragment,
      runtime.bytecode.CompiledFunction.instruction_valid after.function instruction = .ok true) :
    CompilerInstructionPrefix after := by
  refine held.append growth ?_ fragment code fresh
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

/-- The trap callback checks its emitted trap instruction, or emits no code
when the source prefix is already unreachable. -/
theorem compiler_unreachable_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_unreachable_tables ops law before after state called)
    (compiler_unreachable_stable_result ops law before after state (.Ok ()) called).capacity
    (compiler_unreachable_code_mono ops law before after state called)
  cases live : before.reachable with
  | false =>
    have effect := callback_unreachable_dead ops law before state live
    rw [called,WP.spec_ok] at effect
    dsimp only at effect
    exact held.append_with_frames growth (by rw [effect]) [] (by simpa using congrArg alloc.vec.Vec.val effect.code) (by simp)
  | true =>
    have effect := callback_unreachable ops law before state live codeFits sourceFits coordinateFits
    rw [called,WP.spec_ok] at effect
    obtain ⟨_,code,frames,_⟩ := effect rfl
    apply held.append_with_frames growth frames [.Unreachable] code
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact CoreInstructionBounds.accepts .unreachable

/-- Live RETURN's source suffix fits the current frame; later observation
retains that capacity and every previously stored instruction check. -/
theorem compiler_return_live_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (body : runtime.compiler.Frame) (source : U32)
    (live : before.reachable = true) (bodyFrame : before.frames.val[0]? = some body)
    (height : before.height.val = source.val+body.results.val)
    (heightFits : before.height.val ≤ before.function.slot_count.val)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_return_tables ops law before after state called)
    (compiler_return_stable_result ops law before after state (.Ok ()) called).capacity
    (compiler_return_code_mono ops law before after state called)
  have effect := callback_return ops law before state body source live bodyFrame height codeFits sourceFits coordinateFits
  rw [called,WP.spec_ok] at effect
  obtain ⟨_,code,frames,_⟩ := effect rfl
  apply held.append_with_frames growth frames [.Return source body.results] code
  intro instruction member
  simp only [List.mem_singleton] at member
  subst instruction
  exact (CoreInstructionBounds.return_ (by have capacity := growth.slots; omega)).accepts

/-- A return in dead source code only observes the source stack. -/
theorem compiler_return_dead_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dead : before.reachable = false)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_return_tables ops law before after state called)
    (compiler_return_stable_result ops law before after state (.Ok ()) called).capacity
    (compiler_return_code_mono ops law before after state called)
  have effect := callback_return_dead ops law before state dead
  rw [called,WP.spec_ok] at effect
  dsimp only at effect
  exact held.append_with_frames growth (by rw [effect]) [] (by simpa using congrArg alloc.vec.Vec.val effect.code) (by simp)

end Itasca.Runtime.Compiler

end

/-! ## NoopInstructionPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- NOP and DROP perform only the final operand observation on both live and
dead paths. They preserve all instruction and recorded exit-slot checks. -/
theorem compiler_nop_drop_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (drop : Bool)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (if drop then 26#u16 else 1#u16)
      0#u32 0#u32 0#u128 = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  have dispatch : runtime.compiler.lower.FunctionCompiler.op ops before state
      (if drop then 26#u16 else 1#u16) 0#u32 0#u32 0#u128 = runtime.compiler.FunctionCompiler.observe ops before state := by
    cases drop <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> split <;> rfl
  rw [dispatch] at called
  exact ⟨compiler_observe_open_instructions ops law before after state held called,
    compiler_observe_exit_slots ops law before after state exits called⟩

end Itasca.Runtime.Compiler

end

/-! ## TableCallbackExitSlots -/

section

/-!
Exit-slot bounds for br_table targets, the target loop and the compiler callback. The final callback retains both label and branch-table slot requirements.
-/

/-! ## Table Exit Slot Bounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Each actual table arm records an exit only for its source-bounded result
region. Loop arms retain the existing flags and bounds. -/
theorem compiler_table_branch_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (transfers : TableTransferBounds before) (heightFits : before.height.val ≤ before.function.slot_count.val)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  obtain ⟨_,_,_,_,effect⟩ := compiler_table_target_code ops law before after index depth lookup called
  have capacity := (compiler_table_branch_fixed ops law before after index depth lookup called).stable.capacity
  cases effect with
  | loop selected frame source found position kind operands code frames =>
    exact held.retained (congrArg alloc.vec.Vec.val frames) capacity
  | forward selected frame source fixups site found position kind operands code frames appended siteAt =>
    have region := (transfers depth (List.mem_of_getElem? lookup) selected frame found position).1
    have width : frameBranchWidth frame = frame.results := by cases eq : frame.kind <;> simp_all [frameBranchWidth]
    rw [width] at region
    exact held.record selected.val frame fixups frames capacity (by omega)

/-- A finite table run retains all source transfer bounds needed by subsequent
arms and all slot bounds recorded by previous forward exits. -/
theorem TableBranchRun.exit_slots {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A} {index : Nat}
    (run : TableBranchRun ops before index after) (transfers : TableTransferBounds before)
    (heightFits : before.height.val ≤ before.function.slot_count.val) (held : FrameExitSlotBounds before) :
    FrameExitSlotBounds after := by
  induction run with
  | done => exact held
  | @cons before middle after index inside called rest ih =>
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := List.getElem?_eq_getElem inside
    obtain ⟨_,_,_,height,code⟩ := compiler_table_target_code ops law before middle index depth lookup called
    have depths := compiler_table_branch_depths ops before middle index (.Ok ()) called
    have capacity := (compiler_table_branch_fixed ops law before middle index depth lookup called).stable.capacity
    exact ih (transfers.advance code depths height) (by rw [height]; exact heightFits.trans capacity)
      (compiler_table_branch_exit_slots ops law before middle index depth lookup transfers heightFits held called)

/-- The actual dispatch emission and finite target builder retain all branch
exit bounds independently of their final instruction-check certificate. -/
theorem compiler_lower_table_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (transfers : TableTransferBounds before) (heightFits : before.height.val ≤ before.function.slot_count.val)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after called
  have growth := emission.instruction_check_extends
  obtain ⟨budget,code,sources,frame,appended,_⟩ := emission
  subst emitted
  apply run.exit_slots law _ heightFits (held.retained rfl le_rfl)
  intro depth member index frame found position
  have region := transfers depth member index frame found position
  refine ⟨region.1,fun loop => (region.2 loop).trans ?_⟩
  change before.function.code.length ≤ code.length
  exact growth.code

end Itasca.Runtime.Compiler

end

/-! ## Table Callback Exit Slots -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Collecting a table label preserves instruction checks and pending owners. -/
theorem compiler_table_label_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  exact held.retained (by rw [frame]) (by rw [frame])

/-- Lift the source-derived raw table proof through the final default label,
scratch-buffer clearing, and dead-stack observation of the actual callback. -/
theorem compiler_br_table_callback_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : FrameExitSlotBounds before)
    (lower : ∀ labeled,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
        ops before state fallback = .ok (.Ok (),labeled) → labeled.reachable = true → ∀ lowered,
      runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled = .ok (.Ok (),lowered) →
      FrameExitSlotBounds lowered)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at called
  obtain ⟨⟨result,labeled⟩,labelCalled,rest⟩ := bind_ok_inv _ _ _ called
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    have checked := compiler_table_label_exit_slots ops law before labeled state fallback held labelCalled
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    split at rest
    · rename_i live
      obtain ⟨⟨result,lowered⟩,lowerCalled,rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
        have loweredChecked := lower labeled labelCalled live lowered lowerCalled
        simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
        obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
        exact compiler_observe_exit_slots ops law {lowered with reachable := false,table_depths := cleared}
          after state (loweredChecked.retained rfl le_rfl) observed
    · obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
      exact compiler_observe_exit_slots ops law {labeled with table_depths := cleared}
        after state (checked.retained rfl le_rfl) observed

end Itasca.Runtime.Compiler

end

end

/-! ## LoopBranchInstructionPrefix -/

section

namespace Itasca.Runtime.Compiler
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
  · exact branch_instructions_open_checks after.function (PendingInstructionSite after) before.function.code.length
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

end Itasca.Runtime.Compiler

end
