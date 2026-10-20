import Exec.Code.Local.Checking.ElseCallbackInstructionPrefix
import Exec.Code.Local.Checking.FrameExitSlotBounds

namespace Exec.Code
open Aeneas Aeneas.Std

/-- ELSE records the completed THEN arm's result interval, retaining previous
forward exits whether the arm falls through or is already terminated. -/
theorem ElseTransition.exit_slots {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {prior frame guard site condition old noEntry fixups normal}
    (transition : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (held : FrameExitSlotBounds before)
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val)
    (region : normal = true → frame.height.val+frame.results.val ≤ before.function.slot_count.val) :
    FrameExitSlotBounds after := by
  intro selected member live
  rw [transition.afterFrames] at member
  rcases List.mem_append.mp member with previous | current
  · exact (held selected (by rw [transition.beforeFrames]; exact List.mem_append_left _ previous) live).trans capacity
  · have same : selected = {frame with kind := .Else,if_pc := none,end_reachable := frame.end_reachable || normal,fixups} := by
      simpa only [List.mem_singleton] using current
    subst selected
    change (frame.end_reachable || normal) = true at live
    by_cases prior : frame.end_reachable = true
    · exact (held frame (by simp [transition.beforeFrames]) prior).trans capacity
    · have dead : frame.end_reachable = false := Bool.eq_false_iff.mpr prior
      have current : normal = true := by simpa [dead] using live
      exact (region current).trans capacity

/-- Actual ELSE retains recorded exit-slot regions and accounts for a normal
THEN exit using the independently typed source result interval. -/
theorem compiler_else_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : before.frames.val = prior++[frame])
    (guardCode : ∀ guard, frame.if_pc = some guard → ∃ condition,
      before.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (unentered : frame.if_pc = none → before.reachable = false)
    (normal : before.reachable = true → frame.height.val+frame.results.val ≤ before.function.slot_count.val)
    (pcBound : before.function.code.val.length+1 ≤ U32.max)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have capacity := (compiler_else_stable_result ops law before after state bt (.Ok ()) called).capacity
  cases hasIf : frame.if_pc with
  | none =>
    have effect := compiler_else_unentered ops law before state bt frame prior frames (unentered hasIf) hasIf
    rw [called,WP.spec_ok] at effect
    obtain ⟨_,code,afterFrames⟩ := effect rfl
    intro selected member live
    rw [afterFrames] at member
    rcases List.mem_append.mp member with previous | current
    · exact (held selected (by rw [frames]; exact List.mem_append_left _ previous) live).trans capacity
    · have same : selected = {frame with kind := .Else,if_pc := none} := by simpa only [List.mem_singleton] using current
      subst selected
      exact (held frame (by simp [frames]) live).trans capacity
  | some guard =>
    obtain ⟨condition,original⟩ := guardCode guard hasIf
    obtain ⟨target,fixups,transition⟩ : ∃ target fixups,
        ElseTransition before after prior frame guard (alloc.vec.Vec.len before.function.code)
          condition core.num.U32.MAX target fixups before.reachable := by
      cases live : before.reachable with
      | false =>
        let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
        have targetAt : target.val = before.function.code.val.length := rfl
        have effect := compiler_else_dead ops law before state bt frame prior guard condition target frames live hasIf original targetAt
        rw [called,WP.spec_ok] at effect
        obtain ⟨_,code,afterFrames⟩ := effect rfl
        refine ⟨target,frame.fixups,?_⟩
        exact ⟨frames,by simpa using afterFrames,original,rfl,by simpa using targetAt,by simp,by simpa using code⟩
      | true =>
        let target : U32 := UScalar.ofNatCore (before.function.code.val.length+1) (by scalar_tac)
        have targetAt : target.val = before.function.code.val.length+1 := rfl
        obtain ⟨_,code,fixups,appended,afterFrames⟩ := compiler_else_live_success ops law before after state bt frame prior guard
          condition target frames live hasIf original targetAt called
        refine ⟨target,fixups,?_⟩
        exact ⟨frames,by simpa using afterFrames,original,rfl,by simpa using targetAt,by simpa using appended,by simpa using code⟩
    exact transition.exit_slots held capacity normal

end Exec.Code
