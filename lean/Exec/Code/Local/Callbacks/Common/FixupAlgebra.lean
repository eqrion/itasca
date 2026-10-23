import Exec.Code.Local.Callbacks.Common.Fixups
namespace Exec.Code
open Aeneas.Std

theorem retarget_retarget (instruction : Bytecode) (first second : U32) :
    retarget (retarget instruction first) second = retarget instruction second := by
  cases instruction <;> rfl

theorem patchCode_get (code : List Bytecode) (sites : List Usize) (target : U32) (index : Nat) :
    (patchCode code sites target)[index]? =
      if ∃ site ∈ sites, site.val = index then (code[index]?).map (fun i => retarget i target)
      else code[index]? := by
  induction sites generalizing code with
  | nil => simp [patchCode]
  | cons site rest ih =>
    simp only [patchCode]
    split
    · rename_i instruction found
      rw [ih]
      by_cases equal : site.val = index
      · subst index
        have inside := (List.getElem?_eq_some_iff.mp found).1
        simp [inside, (List.getElem?_eq_some_iff.mp found).2, retarget_retarget]
      · simp [equal]
    · rename_i absent
      rw [ih]
      by_cases equal : site.val = index
      · subst index
        simp [absent]
      · simp [equal]

theorem patchCode_append_code (code suffix : List Bytecode) (sites : List Usize) (target : U32)
    (inside : ∀ site, site ∈ sites → site.val < code.length) :
    patchCode (code ++ suffix) sites target = patchCode code sites target ++ suffix := by
  apply List.ext_getElem?
  intro index
  rw [patchCode_get, List.getElem?_append, List.getElem?_append, patchCode_length]
  by_cases before : index < code.length
  · simp [before, patchCode_get]
  · have absent : ¬ ∃ site ∈ sites, site.val = index := by
      rintro ⟨site, member, position⟩
      have := inside site member
      omega
    simp [before, absent]

theorem patchCode_append_sites (code : List Bytecode) (left right : List Usize) (target : U32) :
    patchCode code (left ++ right) target = patchCode (patchCode code left target) right target := by
  induction left generalizing code with
  | nil => rfl
  | cons site rest ih => simp only [List.cons_append, patchCode]; exact ih _

/-- Appending a newly emitted branch and its fixup resolves just that new
branch after the already pending sites; preceding transfer or guard code stays
literal. This is the forward-branch update of the resolved compiler emitted. -/
theorem patchCode_new_branch (code emitted : List Bytecode) (sites : List Usize)
    (kind : BranchKind) (old target : U32) (site : Usize)
    (position : site.val = code.length + emitted.length)
    (inside : ∀ pc, pc ∈ sites → pc.val < code.length) :
    patchCode (code ++ emitted ++ [kind.instruction old]) (sites ++ [site]) target =
      patchCode code sites target ++ emitted ++ [kind.instruction target] := by
  rw [patchCode_append_sites]
  have prior := patchCode_append_code code (emitted ++ [kind.instruction old]) sites target inside
  rw [List.append_assoc, prior]
  have sitePosition : site.val = (patchCode code sites target ++ emitted).length := by
    simp [position, patchCode_length]
  simp only [patchCode, ← List.append_assoc]
  rw [sitePosition]
  simp only [List.getElem?_concat_length]
  have changed : retarget (kind.instruction old) target = kind.instruction target := by cases kind <;> rfl
  simp [changed]

end Exec.Code
