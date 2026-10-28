import Exec.Code.Local.Checking.OpenInstructionCompiler

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
