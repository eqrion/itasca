import Itasca.Runtime.Code.Local.Control.Table.StructuredElseSource
import Itasca.Runtime.Code.Local.Control.Table.StructuredCompletedPrefix
import Itasca.Runtime.Code.Local.Control.Table.StructuredIfEndPrefix
import Itasca.Runtime.Code.Local.Control.Table.StructuredParentPrefixPop
import Itasca.Runtime.Code.Local.Control.Common.UniversalTerminal
import Itasca.Runtime.Code.Local.Relations.Common.Prefix
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseSource
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseTransition
import Itasca.Runtime.Code.Local.Callbacks.Common.FramePlanPop
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedGuards
import Itasca.Runtime.Code.Local.Control.Common.UniversalRoot
import Itasca.Runtime.Code.Local.Relations.Common.PrefixZipper
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- END without ELSE resolves the guard at the shared exit. The missing arm
is the identity required by the source block signature. -/
theorem StructuredCompletedPrefix.close_if {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child normal}
    (invariant : StructuredCompletedPrefix (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child normal)
    (completed : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (guard : Usize) (condition old : U32)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Then) (guardEq : frame.if_pc = some guard)
    (guardCode : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (distinct : ∀ other ∈ after.frames.val, other.if_pc ≠ some guard)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode
      (before.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (layout : CompilerLayout after (child.front ++ child.results))
    (form : child.form = .then_ bt condition) (entry : child.entry = guard.val)
    (bodyStart : child.bodyPc = child.entry + 1)
    (conditionSlot : condition.val = slots locals + slots child.input)
    (sameTypes : child.params = child.results)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.IFELSE bt child.source [])) (child.front ++ child.results) ∧
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.IFELSE bt child.source [])) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patchCode_length]
  have advance : ∀ parentLabel labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (parentLabel :: labels) groups →
      ScopeLabel (parent.advance (.IFELSE bt child.source [])) parentLabel →
      List.Forall₂ ScopeLabel parents.reverse labels →
      StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        parents labels (parent.advance (.IFELSE bt child.source [])) ∧
      StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parentLabel :: labels) parent.input (parent.source ++ [.IFELSE bt child.source []])
        parent.bodyPc after.function.code.val.length (child.front ++ child.results) ∧
      StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parent.advance (.IFELSE bt child.source []) :: parents.reverse) (parentLabel :: labels) := by
    intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], normal, frame.end_reachable⟩
    have future : FrameFuture before.function.code.val.length locals frame label target := by
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
      · intro _; exact Nat.le_of_eq position.symm
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [lengthEq] using plans
    have allPlans := FramePlans.push outer frame label target future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups) := by
      simpa [frameGroups, guardEq, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, noCode⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes position rfl
    have allArms := completed label (parentLabel :: labels) _ normalized childShape allShapes
    have guardFound : (resolvedCode before.function.code.val
        (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups))[child.entry]? =
        some (.JumpIfZero condition target) := by
      rw [entry]
      have current := invariant.sites frame (by simp [frames])
      have away := outer.away_guard
        (fun f member => invariant.sites f (by rw [frames]; exact List.mem_append_left _ member))
        guardCode distinct
      exact resolvedCode_guard _ [] _ guard condition old target guardCode (by
        intro group member site atSite
        simp only [List.nil_append, List.mem_cons] at member
        rcases member with rfl | remaining
        · exact current.branches.not_guard guardCode site atSite
        · exact away group remaining site atSite)
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child.arguments [.IFELSE bt child.source []] child.entry target.val
        (child.front ++ child.results) := by
      have body : StructuredCode emit types functions returns locals
          (resolvedCode before.function.code.val (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups)) jumpTables
          (⟨child.front, child.params, child.params, target, target.val, [], [], normal, frame.end_reachable⟩ :: parentLabel :: labels)
          child.input child.source (child.entry + 1) target.val (child.front ++ child.params) := by
        simpa only [label, bodyStart, position, sameTypes] using noCode
      have sig : BlockSignature types bt child.params child.params := by simpa only [sameTypes] using signature
      simpa [SourceScope.arguments, SourceScope.input, form, sameTypes] using
        StructuredPrefix.ifEnd sig conditionSlot guardFound body
    have restored := parentSaved.resume parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode, patchCode, guardCode, retarget]
    refine ⟨?_, ?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.IFELSE bt child.source [])
    · simpa only [resolve, lengthEq, position] using restored
    · rw [resolve]
      have outerArms : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals
          (resolvedCode before.function.code.val (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups))
          (parent :: parents.reverse) (parentLabel :: labels) := by
        simpa using allArms.outer
      exact outerArms.advance (.IFELSE bt child.source [])
  refine ⟨⟨localsEq, layout, ?_, ?_⟩, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using (original.set_guard guard condition old target guardCode).patch frame.fixups.val target
  · intro label labels groups plans shape parentShapes
    have outcome := advance label labels groups plans shape parentShapes
    exact ⟨outcome.1, outcome.2.1⟩
  · intro label labels groups plans shape parentShapes
    exact (advance label labels groups plans shape parentShapes).2.2

end Itasca.Runtime.Code

