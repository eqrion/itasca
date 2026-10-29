import Itasca.Runtime.Compiler.Local.Checking.OpenInstructionPatch
import Itasca.Runtime.Compiler.Local.Checking.OpenInstructionFragment
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseTransition
import Itasca.Runtime.Compiler.Local.Checking.ScopeEntryInstructionPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseSuccess
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerCloseMetadata

/-!
Checked instruction prefixes through else patching. OpenInstructionPrefix.append_patch feeds ElseTransition preservation and the completed else callback.
-/

/-! ## Open Instruction Append Patch -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- ELSE appends a possible skip and patches an earlier guard. The two effects
can be checked together even though the guard's new target is the resulting
end rather than the old end. Pending ownership is required only off the patch. -/
theorem OpenInstructionPrefix.append_patch {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} (held : OpenInstructionPrefix before pending)
    (growth : InstructionCheckExtends before after) (sites : List Usize) (target : U32)
    (sitesInside : ∀ site ∈ sites, site.val < before.code.length)
    (fragment : List runtime.bytecode.Instr)
    (code : after.code.val = patchCode (before.code.val++fragment) sites target)
    (inside : target.val ≤ after.code.length)
    (owners : ∀ index, (∀ site ∈ sites, site.val ≠ index) → pending index → next index)
    (fresh : ∀ index instruction, fragment[index]? = some instruction →
      OpenInstructionCheck after next (before.code.length+index) instruction) :
    OpenInstructionPrefix after next := by
  intro index instruction found
  rw [code,patchCode_get] at found
  by_cases prior : index < before.code.val.length
  · split at found
    · rw [List.getElem?_append_left prior] at found
      cases original : before.code.val[index]? with
      | none => simp [original] at found
      | some old =>
        have same : retarget old target = instruction := by simpa [original] using found
        rw [← same]
        exact (held index old original).retarget growth target inside
    · rename_i unpatched
      rw [List.getElem?_append_left prior] at found
      exact (held index instruction found).grow growth (owners index (by simpa using unpatched))
  · have unpatched : ¬ ∃ site ∈ sites, site.val = index := by
      intro selected
      obtain ⟨site,member,equal⟩ := selected
      have bounded := sitesInside site member
      change site.val < before.code.val.length at bounded
      omega
    rw [if_neg unpatched,List.getElem?_append_right (by omega : before.code.val.length ≤ index)] at found
    have checked := fresh (index-before.code.val.length) instruction found
    have same : before.code.length+(index-before.code.val.length) = index := by
      change before.code.val.length+(index-before.code.val.length) = index
      omega
    simpa only [same] using checked

end Itasca.Runtime.Code

end

/-! ## Else Instruction Prefix -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

private theorem pending_else {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {prior frame guard site condition old noEntry fixups normal}
    (transition : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (hasIf : frame.if_pc = some guard) (index : Nat) (different : guard.val ≠ index)
    (owned : PendingInstructionSite before index) : PendingInstructionSite after index := by
  obtain ⟨owner,member,address,position,kind⟩ := owned
  rw [transition.beforeFrames] at member
  rcases List.mem_append.mp member with previous | current
  · refine ⟨owner,?_,address,position,kind⟩
    rw [transition.afterFrames]
    exact List.mem_append_left _ previous
  · have same : owner = frame := by simpa only [List.mem_singleton] using current
    subst owner
    rcases kind with guarded | branch
    · have equal : guard = address := Option.some.inj (hasIf.symm.trans guarded)
      exact False.elim (different (equal ▸ position))
    · refine ⟨{frame with kind := .Else,if_pc := none,end_reachable := frame.end_reachable || normal,fixups},?_,address,position,Or.inr ?_⟩
      · rw [transition.afterFrames]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · change address ∈ fixups.val
        rw [transition.fixupsEq]
        exact List.mem_append_left _ branch

/-- The actual physical ELSE update checks its new skip, patches the old guard,
and transfers every remaining pending fixup to the updated frame. -/
theorem ElseTransition.instruction_prefix {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {prior frame guard site condition old noEntry fixups normal}
    (transition : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (hasIf : frame.if_pc = some guard) (held : CompilerInstructionPrefix before)
    (growth : InstructionCheckExtends before.function after.function) : CompilerInstructionPrefix after := by
  let fragment : List runtime.bytecode.Instr := if normal then [.Jump core.num.U32.MAX] else []
  have guardInside := (List.getElem?_eq_some_iff.mp transition.guardCode).1
  have patch : patchCode (before.function.code.val++fragment) [guard] noEntry =
      (before.function.code.val++fragment).set guard.val (.JumpIfZero condition noEntry) := by
    have found := fetch_extend transition.guardCode fragment
    simp [patchCode,found,retarget]
  refine held.append_patch growth [guard] noEntry ?_ fragment ?_ ?_ ?_ ?_
  · intro selected member
    simp only [List.mem_singleton] at member
    subst selected
    exact guardInside
  · rw [patch]
    exact transition.codeEq
  · change noEntry.val ≤ after.function.code.val.length
    rw [transition.length]
  · intro index unpatched owned
    apply pending_else transition hasIf index (unpatched guard (by simp)) owned
  · intro index instruction found
    cases normal with
    | false => simp [fragment] at found
    | true =>
      cases index with
      | zero =>
        have same : .Jump core.num.U32.MAX = instruction := by simpa [fragment] using found
        rw [← same]
        apply OpenInstructionCheck.jump
        apply Or.inr
        unfold PendingInstructionSite
        rw [transition.afterFrames]
        refine ⟨_,List.mem_append_right _ (List.mem_singleton_self _),site,?_,Or.inr ?_⟩
        · simpa only [Nat.add_zero] using transition.sitePosition
        · change site ∈ fixups.val
          simp [transition.fixupsEq]
      | succ index => simp [fragment] at found

end Itasca.Runtime.Code

end

/-! ## Else Callback Instruction Prefix -/

section

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

end
