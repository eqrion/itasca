import Exec.Code.Local.Checking.ElseInstructionPrefix
import Exec.Code.Local.Checking.ScopeEntryInstructionPrefix
import Exec.Code.Local.Callbacks.Control.ElseSuccess
import Exec.Code.Local.Callbacks.Common.CompilerCloseMetadata

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Actual ELSE preserves all stored instruction checks on live, terminated,
and unentered arms. Guard syntax and physical frame geometry come from the
source prefix; numerical PC room is independent of callback success. -/
theorem compiler_else_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : before.frames.val = prior++[frame])
    (guardCode : ∀ guard, frame.if_pc = some guard → ∃ condition,
      before.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (unentered : frame.if_pc = none → before.reachable = false)
    (pcBound : before.function.code.val.length+1 ≤ U32.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_else_tables ops law before after state bt called)
    (compiler_else_stable_result ops law before after state bt (.Ok ()) called).capacity
    (compiler_else_code_mono ops law before after state bt called)
  cases hasIf : frame.if_pc with
  | none =>
    have effect := compiler_else_unentered ops law before state bt frame prior frames (unentered hasIf) hasIf
    rw [called,WP.spec_ok] at effect
    obtain ⟨_,code,afterFrames⟩ := effect rfl
    refine held.append growth ?_ [] (by simpa using congrArg alloc.vec.Vec.val code) (by simp)
    intro index owned
    obtain ⟨owner,member,site,position,kind⟩ := owned
    rw [frames] at member
    rcases List.mem_append.mp member with previous | current
    · refine ⟨owner,?_,site,position,kind⟩
      rw [afterFrames]
      exact List.mem_append_left _ previous
    · have same : owner = frame := by simpa only [List.mem_singleton] using current
      subst owner
      rcases kind with guard | branch
      · simp [hasIf] at guard
      · refine ⟨{frame with kind := .Else,if_pc := none},?_,site,position,Or.inr branch⟩
        rw [afterFrames]
        exact List.mem_append_right _ (List.mem_singleton_self _)
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
    exact transition.instruction_prefix hasIf held growth

end Itasca.Runtime.Code
