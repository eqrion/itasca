import Exec.Code.Local.Control.Common.StructuredCompletedPrefix
import Exec.Code.Local.Control.Control.StructuredElseSource
import Exec.Code.Local.Control.Common.StructuredParentPrefixPop
import Exec.Code.Local.Control.Control.StructuredPrefixElse
import Exec.Code.Local.Control.Control.UniversalCloseDeadElse
namespace Exec.Code
open Aeneas.Std

/-- END of an explicit ELSE obtains both arm relations from retained uniform
prefixes, resolves the shared exit, and retains a terminal outer source prefix. -/
theorem StructuredCompletedPrefix.close_else_dead {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredCompletedPrefix emit before types functions returns locals (parents ++ [parent]) child false)
    (completed : StructuredUniversalElse emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (condition noEntry : U32) (yes : List instr) (yesExit : Nat) (yesNormal : Bool)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Else) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (noBranches : frame.end_reachable = false) (yesDead : yesNormal = false)
    (form : child.form = .else_ bt condition yes yesExit noEntry yesNormal)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalTerminal emit after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) ∧
    StructuredUniversalElse emit after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patchCode_length]
  have advance : ∀ parentLabel labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (parentLabel :: labels) groups →
      ScopeLabel (parent.advance (.IFELSE bt yes child.source)) parentLabel →
      List.Forall₂ ScopeLabel parents.reverse labels →
      StructuredParentPrefixes emit types functions returns locals (resolvedCode after.function.code.val groups)
        parents labels (parent.advance (.IFELSE bt yes child.source)) ∧
      StructuredDeadPrefix emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parentLabel :: labels) parent.input (parent.source ++ [.IFELSE bt yes child.source])
        parent.bodyPc after.function.code.val.length ∧
      StructuredElseFrames emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parent.advance (.IFELSE bt yes child.source) :: parents.reverse) (parentLabel :: labels) := by
    intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], false, frame.end_reachable⟩
    have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact height
      · intro _; exact width
      · intro _; simpa [kind, label] using width
      · exact Nat.le_of_eq position.symm
      · intro _; exact Nat.le_of_eq position.symm
      · simp [kind]
      · simp [kind]
      · exact fun h => h
      · intros; rfl
      · simp [noGuard]
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [lengthEq] using plans
    have allPlans := FramePlans.push outer frame label 0#u32 future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨frame.fixups.val, target⟩ :: groups) := by
      simpa [frameGroups, noGuard, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, noCode⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes position rfl
    have allArms := completed label (parentLabel :: labels) _ normalized childShape allShapes
    have yesEvidence : StructuredElseEvidence emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child label := by
      cases allArms with
      | cons _ _ evidence _ => exact evidence
    simp only [StructuredElseEvidence, childEntered, ite_true, form] at yesEvidence
    obtain ⟨conditionSlot, guardFound, yesCode, skip, noStart⟩ := yesEvidence
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredDeadPrefix emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child.arguments [.IFELSE bt yes child.source] child.entry target.val := by
      have body : StructuredCode emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
          (label :: parentLabel :: labels) child.input child.source noEntry.val target.val
          (child.front ++ child.results) := by
        simpa only [noStart, position] using noCode
      have yesCode' := yesCode
      have body' := body
      simp only [label, noBranches, yesDead] at yesCode' body'
      have skip' : IfSkip (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups)) yesExit noEntry target false := by simpa only [label, yesDead] using skip
      simpa [SourceScope.arguments, SourceScope.input, form] using
        StructuredDeadPrefix.ifElse_skip signature conditionSlot guardFound yesCode' skip' body'
    have restored := parentSaved.resume_dead parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode]
    refine ⟨?_, ?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.IFELSE bt yes child.source)
    · simpa only [resolve, lengthEq, position] using restored
    · rw [resolve]
      have outerArms : StructuredElseFrames emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
          (parent :: parents.reverse) (parentLabel :: labels) := by
        simpa using allArms.outer
      exact outerArms.advance (.IFELSE bt yes child.source)
  refine ⟨⟨localsEq, ?_, ?_⟩, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original.patch frame.fixups.val target
  · intro label labels groups plans shape parentShapes
    have outcome := advance label labels groups plans shape parentShapes
    exact ⟨outcome.1, outcome.2.1⟩
  · intro label labels groups plans shape parentShapes
    exact (advance label labels groups plans shape parentShapes).2.2

end Exec.Code

