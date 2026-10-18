import Exec.Code.Local.Relations.Common.Prefix
namespace Exec.Code
open Aeneas.Std

/-- Closing a block fills its inner source-continuation metadata from the
surrounding prefix hole, retaining literal normal and branch exit coordinates. -/
theorem CodePrefix.block {types functions returns locals code labels front params results body bt pc exit normalLive branchLive}
    (signature : BlockSignature types bt params results)
    (bodyCode : CodeRel types functions returns locals code
      (⟨front, results, results, exit, exit.val, [], [], normalLive, branchLive⟩ :: labels)
      (front ++ params) body pc exit.val (front ++ results)) :
    CodePrefix types functions returns locals code labels (front ++ params) [.BLOCK bt body]
      pc exit.val (front ++ results) := by
  intro suffix tail next final rest
  have bodyCode := bodyCode.extend suffix
  have order := rest.pc_le_next
  apply CodeRel.block (normalLive := normalLive) (branchLive := branchLive) signature ?_ (fun _ => rest) (fun _ => rest)
    ⟨bodyCode.pc_le_next.trans order, rest.next_le_length⟩
  apply bodyCode.relabel
  exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

theorem DeadCodePrefix.block {types functions returns locals code labels front params results body bt pc exit}
    (signature : BlockSignature types bt params results)
    (bodyCode : CodeRel types functions returns locals code
      (⟨front, results, results, exit, exit.val, [], [], false, false⟩ :: labels)
      (front ++ params) body pc exit.val (front ++ results)) :
    DeadCodePrefix types functions returns locals code labels (front ++ params) [.BLOCK bt body]
      pc exit.val := by
  intro suffix tail next final order bound
  have bodyCode := bodyCode.extend suffix
  apply CodeRel.block (normalExit := exit.val) (branchExit := exit) (normalLive := false) (branchLive := false) signature ?_ (by simp) (by simp) ⟨bodyCode.pc_le_next.trans order, bound⟩
  apply bodyCode.relabel
  exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

theorem CodePrefix.loop {types functions returns locals code labels front params results body bt entry exit normalLive}
    (signature : BlockSignature types bt params results)
    (head : code[entry.val]? = some .LoopHead)
    (bodyCode : CodeRel types functions returns locals code
      (⟨front, params, results, entry, exit, [.LOOP bt body], [], normalLive, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) exit (front ++ results)) :
    CodePrefix types functions returns locals code labels (front ++ params) [.LOOP bt body]
      entry.val exit (front ++ results) := by
  intro suffix tail next final rest
  have bodyCode := bodyCode.extend suffix
  have head := fetch_extend head suffix
  have bodyOrder := bodyCode.pc_le_next
  have order := rest.pc_le_next
  apply CodeRel.loop (normalLive := normalLive) signature head ?_ (fun _ => rest) ⟨by omega, rest.next_le_length⟩
  apply bodyCode.relabel
  exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

theorem DeadCodePrefix.loop {types functions returns locals code labels front params results body bt entry exit}
    (signature : BlockSignature types bt params results)
    (head : code[entry.val]? = some .LoopHead)
    (bodyCode : CodeRel types functions returns locals code
      (⟨front, params, results, entry, exit, [.LOOP bt body], [], false, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) exit (front ++ results)) :
    DeadCodePrefix types functions returns locals code labels (front ++ params) [.LOOP bt body] entry.val exit := by
  intro suffix tail next final order bound
  have bodyCode := bodyCode.extend suffix
  have head := fetch_extend head suffix
  have bodyOrder := bodyCode.pc_le_next
  apply CodeRel.loop (exit := exit) (normalLive := false) signature head ?_ (by simp) ⟨by omega, bound⟩
  apply bodyCode.relabel
  exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

theorem CodePrefix.ifElse {types functions returns locals code labels front params results yes no bt pc yesExit noEntry exit cond yesNormal yesBranch noNormal noBranch}
    (signature : BlockSignature types bt params results)
    (condition : cond.val = slots locals + slots (front ++ params))
    (guard : code[pc]? = some (.JumpIfZero cond noEntry))
    (yesCode : CodeRel types functions returns locals code
      (⟨front, results, results, exit, yesExit, [], [], yesNormal, yesBranch⟩ :: labels)
      (front ++ params) yes (pc + 1) yesExit (front ++ results))
    (skip : IfSkip code yesExit noEntry exit yesNormal)
    (noCode : CodeRel types functions returns locals code
      (⟨front, results, results, exit, exit.val, [], [], noNormal, noBranch⟩ :: labels)
      (front ++ params) no noEntry.val exit.val (front ++ results)) :
    CodePrefix types functions returns locals code labels (front ++ params ++ [.I32]) [.IFELSE bt yes no]
      pc exit.val (front ++ results) := by
  intro suffix tail next final rest
  have yesCode := yesCode.extend suffix
  have noCode := noCode.extend suffix
  have guard := fetch_extend guard suffix
  have skip := skip.extend suffix
  have yesOrder := yesCode.pc_le_next
  have skipOrder := skip.pc_le_next
  have noOrder := noCode.pc_le_next
  have order := rest.pc_le_next
  apply CodeRel.ifElse (yesNormal := yesNormal) (yesBranch := yesBranch) (noNormal := noNormal) (noBranch := noBranch) signature condition guard ?_ skip ?_ (fun _ => rest)
    ⟨by omega, by omega, rest.next_le_length⟩
  · apply yesCode.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)
  · apply noCode.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

theorem DeadCodePrefix.ifElse {types functions returns locals code labels front params results yes no bt pc yesExit noEntry exit cond}
    (signature : BlockSignature types bt params results)
    (condition : cond.val = slots locals + slots (front ++ params))
    (guard : code[pc]? = some (.JumpIfZero cond noEntry))
    (yesCode : CodeRel types functions returns locals code
      (⟨front, results, results, exit, yesExit, [], [], false, false⟩ :: labels)
      (front ++ params) yes (pc + 1) yesExit (front ++ results))
    (skip : Segment code yesExit [] noEntry.val)
    (noCode : CodeRel types functions returns locals code
      (⟨front, results, results, exit, exit.val, [], [], false, false⟩ :: labels)
      (front ++ params) no noEntry.val exit.val (front ++ results)) :
    DeadCodePrefix types functions returns locals code labels (front ++ params ++ [.I32]) [.IFELSE bt yes no]
      pc exit.val := by
  intro suffix tail next final order bound
  have yesCode := yesCode.extend suffix
  have noCode := noCode.extend suffix
  have guard := fetch_extend guard suffix
  have skip := skip.extend suffix
  have yesOrder := yesCode.pc_le_next
  have skipOrder := skip.pc_le_next
  have noOrder := noCode.pc_le_next
  apply CodeRel.ifElse (yesExit := yesExit) (exit := exit) (yesNormal := false) (yesBranch := false) (noNormal := false) (noBranch := false) signature condition guard ?_ (.emitted (by simpa using skip)) ?_ (by simp)
    ⟨by omega, by omega, bound⟩
  · apply yesCode.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)
  · apply noCode.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

end Exec.Code
