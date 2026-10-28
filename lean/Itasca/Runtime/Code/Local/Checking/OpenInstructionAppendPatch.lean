import Itasca.Runtime.Code.Local.Checking.OpenInstructionPatch
import Itasca.Runtime.Code.Local.Checking.OpenInstructionFragment

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
