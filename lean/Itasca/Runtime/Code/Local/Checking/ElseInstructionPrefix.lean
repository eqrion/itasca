import Itasca.Runtime.Code.Local.Checking.OpenInstructionAppendPatch
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseTransition

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
