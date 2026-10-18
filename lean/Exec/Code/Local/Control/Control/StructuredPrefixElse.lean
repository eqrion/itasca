import Exec.Code.Local.Control.Control.StructuredPrefixControl
namespace Exec.Code
open Aeneas.Std

theorem StructuredDeadPrefix.ifElse_skip {emit types functions returns locals code labels front params results yes no bt pc yesExit noEntry exit cond}
    (signature : BlockSignature types bt params results)
    (condition : cond.val = slots locals + slots (front ++ params))
    (guard : code[pc]? = some (.JumpIfZero cond noEntry))
    (yesCode : StructuredCode emit types functions returns locals code
      (⟨front, results, results, exit, yesExit, [], [], false, false⟩ :: labels)
      (front ++ params) yes (pc + 1) yesExit (front ++ results))
    (skip : IfSkip code yesExit noEntry exit false)
    (noCode : StructuredCode emit types functions returns locals code
      (⟨front, results, results, exit, exit.val, [], [], false, false⟩ :: labels)
      (front ++ params) no noEntry.val exit.val (front ++ results)) :
    StructuredDeadPrefix emit types functions returns locals code labels (front ++ params ++ [.I32]) [.IFELSE bt yes no]
      pc exit.val := by
  intro suffix tail next final order bound
  have yesCode := yesCode.extend suffix
  have noCode := noCode.extend suffix
  have guard := fetch_extend guard suffix
  have skip := skip.extend suffix
  have yesOrder := yesCode.pc_le_next
  have skipOrder := skip.pc_le_next
  have noOrder := noCode.pc_le_next
  apply StructuredCode.ifElse (yesExit := yesExit) (exit := exit) (yesNormal := false) (yesBranch := false) (noNormal := false) (noBranch := false) signature condition guard ?_ skip ?_ (by simp)
    ⟨by omega, by omega, bound⟩
  · apply yesCode.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)
  · apply noCode.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

end Exec.Code

