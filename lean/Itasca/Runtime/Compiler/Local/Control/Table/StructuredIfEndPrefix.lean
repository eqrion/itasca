import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalCloseDeadElse
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalTerminal
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper

/-!
Sections, each formerly its own module: StructuredUniversalCloseElse, StructuredUniversalRoot, StructuredUniversalCloseBlock, StructuredUniversalCloseDeadBlock, StructuredIfEndPrefix.
-/

/-! ## StructuredUniversalCloseElse -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- END of an explicit ELSE obtains both arm relations from retained uniform
prefixes, resolves the shared exit, and resumes the suspended outer source. -/
theorem StructuredCompletedPrefix.close_else {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child normal}
    (invariant : StructuredCompletedPrefix (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child normal)
    (completed : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (condition noEntry : U32) (yes : List instr) (yesExit : Nat) (yesNormal : Bool)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Else) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (layout : CompilerLayout after (child.front ++ child.results))
    (form : child.form = .else_ bt condition yes yesExit noEntry yesNormal)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) (child.front ++ child.results) ∧
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patch_code_length]
  have advance : ∀ parentLabel labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (parentLabel :: labels) groups →
      ScopeLabel (parent.advance (.IFELSE bt yes child.source)) parentLabel →
      List.Forall₂ ScopeLabel parents.reverse labels →
      StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        parents labels (parent.advance (.IFELSE bt yes child.source)) ∧
      StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parentLabel :: labels) parent.input (parent.source ++ [.IFELSE bt yes child.source])
        parent.bodyPc after.function.code.val.length (child.front ++ child.results) ∧
      StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parent.advance (.IFELSE bt yes child.source) :: parents.reverse) (parentLabel :: labels) := by
    intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], normal, frame.end_reachable⟩
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
    have yesEvidence : StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child label := by
      cases allArms with
      | cons _ _ evidence _ => exact evidence
    simp only [StructuredElseEvidence, childEntered, ite_true, form] at yesEvidence
    obtain ⟨conditionSlot, guardFound, yesCode, skip, noStart⟩ := yesEvidence
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child.arguments [.IFELSE bt yes child.source] child.entry target.val
        (child.front ++ child.results) := by
      have body : StructuredCode emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups)) jumpTables
          (label :: parentLabel :: labels) child.input child.source noEntry.val target.val
          (child.front ++ child.results) := by
        simpa only [noStart, position] using noCode
      simpa [SourceScope.arguments, SourceScope.input, form, label] using
        StructuredPrefix.if_else signature conditionSlot guardFound yesCode skip body
    have restored := parentSaved.resume parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode]
    refine ⟨?_, ?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.IFELSE bt yes child.source)
    · simpa only [resolve, lengthEq, position] using restored
    · rw [resolve]
      have outerArms : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
          (parent :: parents.reverse) (parentLabel :: labels) := by
        simpa using allArms.outer
      exact outerArms.advance (.IFELSE bt yes child.source)
  refine ⟨⟨localsEq, layout, ?_, ?_⟩, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original.patch frame.fixups.val target
  · intro label labels groups plans shape parentShapes
    have outcome := advance label labels groups plans shape parentShapes
    exact ⟨outcome.1, outcome.2.1⟩
  · intro label labels groups plans shape parentShapes
    exact (advance label labels groups plans shape parentShapes).2.2

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalRoot -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std
theorem StructuredUniversalPrefix.root_finish {jumpTables : List Aeneas.Std.U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals current}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit compiler types functions returns locals [] current returns)
    (frame : runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = [frame]) (kind : frame.kind = .Body) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals) (width : frame.results.val = slots returns)
    (position : target.val = compiler.function.code.val.length)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns) (start : current.bodyPc = 0) :
    StructuredCode emit types functions returns locals (patchCode compiler.function.code.val frame.fixups.val target) jumpTables
      [⟨[], returns, returns, target, target.val, [], [], true, frame.end_reachable⟩]
      [] current.source 0 target.val returns := by
  have plans := root_frame_plan compiler.function.code.val locals returns frame target true kind noGuard height width position
  rw [← frames] at plans
  have shape := root_scope_label current returns target true frame.end_reachable form front results
  have code := (invariant.prefixes _ [] _ plans shape .nil).2
  have finished := code.finish (by simp [resolved_code_length]) (by simp [NormalLive])
  simpa [resolvedCode, SourceScope.input, front, params, start, position] using finished

/-- A terminal root body closes at the actual final PC even when its result
signature is nonempty and the emitted unreachable epilogue returns zero words. -/
theorem StructuredUniversalTerminal.root_finish {jumpTables : List Aeneas.Std.U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals current}
    (invariant : StructuredUniversalTerminal (jumpTables := jumpTables) emit compiler types functions returns locals [] current)
    (frame : runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = [frame]) (kind : frame.kind = .Body) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals) (width : frame.results.val = slots returns)
    (position : target.val = compiler.function.code.val.length)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns) (start : current.bodyPc = 0) :
    StructuredCode emit types functions returns locals (patchCode compiler.function.code.val frame.fixups.val target) jumpTables
      [⟨[], returns, returns, target, target.val, [], [], false, frame.end_reachable⟩]
      [] current.source 0 target.val returns := by
  have plans := root_frame_plan compiler.function.code.val locals returns frame target false kind noGuard height width position
  rw [← frames] at plans
  have shape := root_scope_label current returns target false frame.end_reachable form front results
  have code := (invariant.prefixes _ [] _ plans shape .nil).2
  have finished := code.finish target.val returns (by omega) (by simp [resolved_code_length, position])
  simpa [resolvedCode, SourceScope.input, front, params, start, position] using finished

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalCloseBlock -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Exact BLOCK END patching removes its resolution group and resumes the
suspended parent. The completed body's relation is derived from the universal
prefix, rather than supplied as a correctness premise. -/
theorem StructuredUniversalPrefix.close_block {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child
      (child.front ++ child.results))
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Block) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (layout : CompilerLayout after (child.front ++ child.results))
    (form : child.form = .block bt) (entry : child.entry = child.bodyPc)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.BLOCK bt child.source)) (child.front ++ child.results) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patch_code_length]
  refine ⟨localsEq, layout, ?_, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original.patch frame.fixups.val target
  · intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], true, frame.end_reachable⟩
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
    have bodyCode := current.finish (by simp [resolved_code_length]) (by simp [NormalLive, label])
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
      simpa [SourceScope.arguments, SourceScope.input, form, entry] using StructuredPrefix.block signature body
    have restored := parentSaved.resume parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode]
    refine ⟨?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.BLOCK bt child.source)
    · simpa only [resolve, lengthEq, position, SourceScope.advance, SourceScope.input] using restored

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalCloseDeadBlock -/

section

namespace Itasca.Runtime.Compiler
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
    simp [codeEq, patch_code_length]
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
    have bodyCode := current.finish target.val (child.front ++ child.results) (by omega) (by simp [resolved_code_length, position])
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
    simp [codeEq, patch_code_length]
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
    have bodyCode := current.finish target.val (child.front ++ child.results) (by omega) (by simp [resolved_code_length, position])
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredIfEndPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- An implicit empty ELSE joins directly at the normal exit. Its input and
output stacks agree, so the compiler emits no skip instruction. -/
theorem StructuredPrefix.if_end {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels front params yes bt pc exit cond yesNormal yesBranch}
    (signature : BlockSignature types bt params params)
    (condition : cond.val = slots locals + slots (front ++ params))
    (guard : code[pc]? = some (.JumpIfZero cond exit))
    (yesCode : StructuredCode emit types functions returns locals code jumpTables
      (⟨front, params, params, exit, exit.val, [], [], yesNormal, yesBranch⟩ :: labels)
      (front ++ params) yes (pc + 1) exit.val (front ++ params)) :
    StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals code labels (front ++ params ++ [.I32]) [.IFELSE bt yes []]
      pc exit.val (front ++ params) := by
  exact StructuredPrefix.if_else (noNormal := true) (noBranch := false) signature condition guard yesCode (.direct rfl rfl)
    (.nil _ _ _ yesCode.next_le_length (NormalLive.cons rfl))

end Itasca.Runtime.Compiler

end
