import Itasca.Runtime.Compiler.Local.Checking.OpenInstructionCompiler
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Checking.InstructionAppendEffect
import Itasca.Runtime.Compiler.Local.Checking.OpenInstructionFragment
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSkipSafety
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerBranchMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl

/-!
Checked prefixes for forward branches, including pending-site replacement and transfer instruction acceptance. Resolving a branch preserves all earlier open checks.
-/

/-! ## Branch Instruction Acceptance -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- A branch's overlap-safe copy fits from the independently checked source
and destination regions. Scalar/two-word copies are specialized by the runtime. -/
theorem transfer_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (dst src count : U32) (order : dst.val ≤ src.val)
    (source : src.val+count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (transferInstruction dst src count) = .ok true := by
  unfold transferInstruction
  split
  · rename_i one
    exact (CoreInstructionBounds.copy (by omega) (by omega)).accepts
  · split
    · rename_i two
      exact (CoreInstructionBounds.copy2 (by omega) (by omega)).accepts
    · exact (CoreInstructionBounds.copyN (by omega) source order).accepts

/-- Every word in an unconditional branch fragment checks, with only the final
jump allowed to wait for its recorded control-frame owner. -/
theorem branchInstructions_open_checks (function : runtime.bytecode.CompiledFunction)
    (pending : Nat → Prop) (start : Nat) (dst src count target : U32)
    (order : dst.val ≤ src.val) (source : src.val+count.val ≤ function.slot_count.val)
    (ready : target.val ≤ function.code.length ∨ pending (start+(branchInstructions dst src count target).length-1)) :
    ∀ index instruction, (branchInstructions dst src count target)[index]? = some instruction →
      OpenInstructionCheck function pending (start+index) instruction := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simp only [branchInstructions,if_pos elided,List.length_singleton,Nat.add_sub_cancel] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : .Jump target = instruction := by simpa [branchInstructions,elided] using found
      rw [← same,Nat.add_zero]
      exact .jump ready
    | succ index => simp [branchInstructions,elided] at found
  · simp only [branchInstructions,if_neg elided,List.length_cons,List.length_nil] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : transferInstruction dst src count = instruction := by simpa [branchInstructions,elided] using found
      rw [← same]
      exact .checked (transfer_instruction_accepts function dst src count order source)
    | succ index =>
      cases index with
      | zero =>
        have same : .Jump target = instruction := by simpa [branchInstructions,elided] using found
        rw [← same]
        apply OpenInstructionCheck.jump
        simpa only [Nat.reduceAdd,show start+2-1 = start+1 by omega] using ready
      | succ index => simp [branchInstructions,elided] at found

/-- Conditional branch fragments check the selector and transfer immediately;
only their selected label target may remain pending. The skip address already
names the fragment's continuation. -/
theorem branchIfInstructions_open_checks (function : runtime.bytecode.CompiledFunction)
    (pending : Nat → Prop) (start : Nat) (dst src count target condition resume : U32)
    (order : dst.val ≤ src.val) (source : src.val+count.val ≤ function.slot_count.val)
    (test : condition.val+1 ≤ function.slot_count.val)
    (continuation : ¬ (count = 0#u32 ∨ src = dst) → resume.val ≤ function.code.length)
    (ready : target.val ≤ function.code.length ∨ pending (start+(branchIfInstructions dst src count target condition resume).length-1)) :
    ∀ index instruction, (branchIfInstructions dst src count target condition resume)[index]? = some instruction →
      OpenInstructionCheck function pending (start+index) instruction := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simp only [branchIfInstructions,if_pos elided,List.length_singleton,Nat.add_sub_cancel] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : .JumpIfNonZero condition target = instruction := by simpa [branchIfInstructions,elided] using found
      rw [← same,Nat.add_zero]
      exact .nonzero test ready
    | succ index => simp [branchIfInstructions,elided] at found
  · simp only [branchIfInstructions,if_neg elided,List.length_cons,List.length_nil] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : .JumpIfZero condition resume = instruction := by simpa [branchIfInstructions,elided] using found
      rw [← same]
      exact .zero test (.inl (continuation elided))
    | succ index =>
      cases index with
      | zero =>
        have same : transferInstruction dst src count = instruction := by simpa [branchIfInstructions,elided] using found
        rw [← same]
        exact .checked (transfer_instruction_accepts function dst src count order source)
      | succ index =>
        cases index with
        | zero =>
          have same : .Jump target = instruction := by simpa [branchIfInstructions,elided] using found
          rw [← same]
          apply OpenInstructionCheck.jump
          simpa only [Nat.reduceAdd,show start+3-1 = start+2 by omega] using ready
        | succ index => simp [branchIfInstructions,elided] at found

end Itasca.Runtime.Code

end

/-! ## Pending Instruction Replace -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Recording a branch changes one frame's liveness and extends its fixups.
Every earlier pending instruction retains an owner, even if equal frame values
occur at more than one position. -/
theorem pending_instruction_replace {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (index : Nat) (frame replacement : runtime.compiler.Frame)
    (lookup : before.frames.val[index]? = some frame)
    (frames : after.frames.val = before.frames.val.set index replacement)
    (guard : replacement.if_pc = frame.if_pc)
    (fixups : ∀ site ∈ frame.fixups.val, site ∈ replacement.fixups.val)
    (position : Nat) (owned : PendingInstructionSite before position) : PendingInstructionSite after position := by
  obtain ⟨owner,member,site,atSite,kind⟩ := owned
  by_cases selected : owner = frame
  · subst owner
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    have found : after.frames.val[index]? = some replacement := by
      rw [frames,List.getElem?_set_self bound]
    obtain ⟨within,equal⟩ := List.getElem?_eq_some_iff.mp found
    refine ⟨replacement,equal ▸ List.getElem_mem within,site,atSite,?_⟩
    exact kind.imp (fun guarded => guard.trans guarded) (fixups site)
  · obtain ⟨ownerIndex,inside,equal⟩ := List.getElem_of_mem member
    have original : before.frames.val[ownerIndex]? = some owner := by
      simp [List.getElem?_eq_getElem inside,equal]
    have different : index ≠ ownerIndex := by
      intro same
      rw [← same,lookup] at original
      exact selected (Option.some.inj original).symm
    have found : after.frames.val[ownerIndex]? = some owner := by
      rw [frames,List.getElem?_set_ne different]
      exact original
    obtain ⟨within,equal⟩ := List.getElem?_eq_some_iff.mp found
    exact ⟨owner,equal ▸ List.getElem_mem within,site,atSite,kind⟩

/-- A captured fixup entry witnesses ownership at its exact code coordinate. -/
theorem pending_instruction_fixup {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (index : Nat) (frame : runtime.compiler.Frame) (site : Usize)
    (lookup : compiler.frames.val[index]? = some frame) (member : site ∈ frame.fixups.val) :
    PendingInstructionSite compiler site.val := by
  obtain ⟨within,equal⟩ := List.getElem?_eq_some_iff.mp lookup
  exact ⟨frame,equal ▸ List.getElem_mem within,site,rfl,Or.inr member⟩

end Itasca.Runtime.Code

end

/-! ## Forward Branch Instruction Prefix -/

section

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

end
