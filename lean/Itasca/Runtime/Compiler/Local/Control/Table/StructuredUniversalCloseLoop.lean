import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalCloseBlock
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedLiteral
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- LOOP END resumes its parent only from the normal body continuation. Loop
branches retain their backward target and never become forward END fixups. -/
theorem StructuredUniversalPrefix.close_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child
      (child.front ++ child.results))
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Loop) (noGuard : frame.if_pc = none) (noFixups : frame.fixups.val = [])
    (height : frame.height.val = slots locals + slots child.front)
    (inputs : frame.params.val = slots child.params) (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = before.function.code.val)
    (localsEq : compilerLocals after = locals)
    (layout : CompilerLayout after (child.front ++ child.results))
    (form : child.form = .loop bt) (entry : child.entry = frame.start_pc.val)
    (body : child.bodyPc = frame.start_pc.val + 1)
    (head : before.function.code.val[frame.start_pc.val]? = some .LoopHead)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.LOOP bt child.source)) (child.front ++ child.results) := by
  refine ⟨localsEq, layout, ?_, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original
  · intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.params, child.results, frame.start_pc,
      target.val, [.LOOP bt child.source], [], true, true⟩
    have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact height
      · intro _; exact width
      · intro _; simpa [kind, label] using inputs
      · exact Nat.le_of_eq position.symm
      · simp [kind]
      · intro _; rfl
      · intro _; rfl
      · intro _; rfl
      · simp [kind]
      · simp [noGuard]
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [codeEq] using plans
    have allPlans := FramePlans.push outer frame label 0#u32 future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨[], frame.start_pc⟩ :: groups) := by
      simpa [frameGroups, noGuard, noFixups, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, current⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes
    simp only [resolvedCode, patchCode] at saved current
    have bodyCode := current.finish (by simp [resolvedCode_length]) (by simp [NormalLive, label])
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode before.function.code.val groups)
        (parentLabel :: labels) child.arguments [.LOOP bt child.source] child.entry target.val
        (child.front ++ child.results) := by
      have bodyCode' : StructuredCode emit types functions returns locals (resolvedCode before.function.code.val groups) jumpTables
          (label :: parentLabel :: labels) (child.front ++ child.params) child.source
          (frame.start_pc.val + 1) target.val (child.front ++ child.results) := by
        simpa only [SourceScope.input, position, body] using bodyCode
      simpa [SourceScope.arguments, SourceScope.input, form, entry] using
        StructuredPrefix.loop signature (resolvedCode_loop_head _ groups _ head) bodyCode'
    have restored := parentSaved.resume parentEntered childEntered closed
    refine ⟨?_, ?_⟩
    · rw [codeEq]
      exact outerSaved.advance_current (.LOOP bt child.source)
    · simpa only [codeEq, position, SourceScope.advance, SourceScope.input] using restored

/-- A terminal loop body keeps its parent terminal; its live backward branch
target is independent of the dead normal exit. -/
theorem StructuredUniversalTerminal.close_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalTerminal (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Loop) (noGuard : frame.if_pc = none) (noFixups : frame.fixups.val = [])
    (height : frame.height.val = slots locals + slots child.front)
    (inputs : frame.params.val = slots child.params) (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = before.function.code.val)
    (localsEq : compilerLocals after = locals)
    (form : child.form = .loop bt) (entry : child.entry = frame.start_pc.val)
    (body : child.bodyPc = frame.start_pc.val + 1)
    (head : before.function.code.val[frame.start_pc.val]? = some .LoopHead)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalTerminal (jumpTables := jumpTables) emit after types functions returns locals parents (parent.advance (.LOOP bt child.source)) := by
  refine ⟨localsEq, ?_, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original
  · intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.params, child.results, frame.start_pc,
      target.val, [.LOOP bt child.source], [], false, true⟩
    have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact height
      · intro _; exact width
      · intro _; simpa [kind, label] using inputs
      · exact Nat.le_of_eq position.symm
      · simp [kind]
      · intro _; rfl
      · intro _; rfl
      · intro _; rfl
      · simp [kind]
      · simp [noGuard]
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [codeEq] using plans
    have allPlans := FramePlans.push outer frame label 0#u32 future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨[], frame.start_pc⟩ :: groups) := by
      simpa [frameGroups, noGuard, noFixups, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, current⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes
    simp only [resolvedCode, patchCode] at saved current
    have bodyCode := current.finish target.val (child.front ++ child.results) (by omega) (by simp [resolvedCode_length, position])
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode before.function.code.val groups)
        (parentLabel :: labels) child.arguments [.LOOP bt child.source] child.entry target.val := by
      have bodyCode' : StructuredCode emit types functions returns locals (resolvedCode before.function.code.val groups) jumpTables
          (label :: parentLabel :: labels) (child.front ++ child.params) child.source
          (frame.start_pc.val + 1) target.val (child.front ++ child.results) := by
        simpa only [SourceScope.input, position, body] using bodyCode
      simpa [SourceScope.arguments, SourceScope.input, form, entry] using
        StructuredDeadPrefix.loop signature (resolvedCode_loop_head _ groups _ head) bodyCode'
    have restored := parentSaved.resume_dead parentEntered childEntered closed
    refine ⟨?_, ?_⟩
    · rw [codeEq]
      exact outerSaved.advance_current (.LOOP bt child.source)
    · simpa only [codeEq, position, SourceScope.advance, SourceScope.input] using restored

end Itasca.Runtime.Code

