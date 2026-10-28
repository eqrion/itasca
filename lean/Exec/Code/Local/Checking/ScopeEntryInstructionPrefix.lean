import Exec.Code.Local.Publication.ScopeEntryPublication
import Exec.Code.Local.Checking.OpenInstructionFragment
import Exec.Code.Local.Relations.Table.ControlTablePreservation

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

private theorem pending_append {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {frame : runtime.compiler.Frame} (frames : after.frames.val = before.frames.val++[frame])
    (index : Nat) (owned : PendingInstructionSite before index) : PendingInstructionSite after index := by
  obtain ⟨owner,member,site,position,kind⟩ := owned
  refine ⟨owner,?_,site,position,kind⟩
  rw [frames]
  exact List.mem_append_left _ member

/-- Actual live and dead scope entry preserves checking of every old instruction.
LOOP checks its hook; IF checks its condition and records ownership of the new
forward guard. The premises describe only the current source-reader boundary. -/
theorem compiler_scope_entry_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeEntryGeometry before state bt) (mode : ScopeEntryMode geometry kind)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_enter_tables ops law before after state kind bt called)
    (compiler_enter_stable_result ops law before after state kind bt (.Ok ()) called).capacity
    (compiler_enter_code_mono ops law before after state kind bt called)
  cases mode with
  | block live position =>
    have effect := enter_block ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    exact held.append growth (pending_append frames) [] (by simpa using congrArg alloc.vec.Vec.val code) (by simp)
  | loop live position codeFits offsetsFit =>
    have effect := enter_loop ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position codeFits offsetsFit
      geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    apply held.append growth (pending_append frames) [.LoopHead] code
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact CoreInstructionBounds.accepts .loopHead
  | if_ stack layout live position codeFits offsetsFit =>
    have effect := enter_if ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      stack layout codeFits offsetsFit geometry.controls geometry.selected geometry.valuesFit geometry.heightFits
      geometry.sourceFits position geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨_,condition,height,source,conditionPosition,code,_,_,frames,_⟩ := effect rfl
    apply held.append_open growth (pending_append frames) [.JumpIfZero condition core.num.U32.MAX] code
    intro index instruction found
    cases index with
    | zero =>
      have same : .JumpIfZero condition core.num.U32.MAX = instruction := by simpa using found
      rw [← same]
      apply OpenInstructionCheck.zero
      · have fits := layout.live_slots_fit live
        simp only [slots_append,slots,width] at fits
        have capacity := growth.slots
        omega
      · apply Or.inr
        unfold PendingInstructionSite
        rw [frames]
        refine ⟨_,List.mem_append_right _ (List.mem_singleton_self _),_,?_,Or.inl rfl⟩
        rfl
    | succ index => simp at found
  | dead kind dormant position =>
    have effect := enter_dead ops law before state geometry.ctrl geometry.prior kind bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit dormant
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    exact held.append growth (pending_append frames) [] (by simpa using congrArg alloc.vec.Vec.val code) (by simp)

end Itasca.Runtime.Code
