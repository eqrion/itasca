import Itasca.Runtime.Code.Local.Control.Table.StructuredUniversalCloseBlock
import Itasca.Runtime.Code.Local.Control.Common.UniversalRoot
import Itasca.Runtime.Code.Local.Relations.Common.PrefixZipper
import Itasca.Runtime.Code.Local.Relations.Common.Prefix
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- A block with neither a normal exit nor a recorded forward branch leaves
its parent terminal; omitted source tails remain justified by the body. -/
theorem StructuredUniversalTerminal.close_block_dead {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalTerminal (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Block) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (branchDead : frame.end_reachable = false)
    (form : child.form = .block bt) (entry : child.entry = child.bodyPc)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalTerminal (jumpTables := jumpTables) emit after types functions returns locals parents (parent.advance (.BLOCK bt child.source)) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patchCode_length]
  refine ⟨localsEq, ?_, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original.patch frame.fixups.val target
  · intro parentLabel labels groups plans shape parentShapes
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
    obtain ⟨saved, current⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes
    have bodyCode := current.finish target.val (child.front ++ child.results) (by omega) (by simp [resolvedCode_length, position])
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child.arguments [.BLOCK bt child.source] child.entry target.val := by
      have body : StructuredCode emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups)) jumpTables
          (label :: parentLabel :: labels) (child.front ++ child.params) child.source child.bodyPc
          target.val (child.front ++ child.results) := by
        simpa only [SourceScope.input, position] using bodyCode
      simpa [SourceScope.arguments, SourceScope.input, form, entry] using
        StructuredDeadPrefix.block signature (by simpa [label, branchDead] using body)
    have restored := parentSaved.resume_dead parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode]
    refine ⟨?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.BLOCK bt child.source)
    · simpa only [resolve, lengthEq, position, SourceScope.advance, SourceScope.input] using restored

/-- A recorded branch to a block exit restores the parent continuation even
when the last source path in the block is terminal. -/
theorem StructuredUniversalTerminal.close_block_resume {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalTerminal (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Block) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (layout : CompilerLayout after (child.front ++ child.results))
    (branchLive : frame.end_reachable = true)
    (form : child.form = .block bt) (entry : child.entry = child.bodyPc)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.BLOCK bt child.source)) (child.front ++ child.results) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patchCode_length]
  refine ⟨localsEq, layout, ?_, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original.patch frame.fixups.val target
  · intro parentLabel labels groups plans shape parentShapes
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
    obtain ⟨saved, current⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes
    have bodyCode := current.finish target.val (child.front ++ child.results) (by omega) (by simp [resolvedCode_length, position])
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child.arguments [.BLOCK bt child.source] child.entry target.val
        (child.front ++ child.results) := by
      have body : StructuredCode emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups)) jumpTables
          (label :: parentLabel :: labels) (child.front ++ child.params) child.source child.bodyPc
          target.val (child.front ++ child.results) := by
        simpa only [SourceScope.input, position] using bodyCode
      simpa [SourceScope.arguments, SourceScope.input, form, entry] using StructuredPrefix.block (branchLive := true) signature (by simpa [label, branchLive] using body)
    have restored := parentSaved.resume parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode]
    refine ⟨?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.BLOCK bt child.source)
    · simpa only [resolve, lengthEq, position, SourceScope.advance, SourceScope.input] using restored

end Itasca.Runtime.Code

