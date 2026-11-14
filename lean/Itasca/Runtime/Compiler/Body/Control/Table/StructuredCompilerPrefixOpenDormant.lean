import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Compiler.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredFunction
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalCloseDeadElse

/-!
Sections, each formerly its own module: StructuredBranchIfLayout, StructuredCompilerPrefixTerminal, StructuredCompilerPrefixBranch, StructuredCompilerPrefixLoopBranch, StructuredCompilerPrefixOpenDormant.
-/

/-! ## StructuredBranchIfLayout -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem StructuredCompilerPrefix.branch_if_coordinates {jumpTables : List Aeneas.Std.U32} {A : Type}
    {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position stack}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype)
    (input : Sequence.stackTypes raw = stack ++ [.I32])
    (targetStack : stack = scope.front ++ discarded ++ scope.branchTypes) :
    ∃ index : Usize, ∃ frame : runtime.compiler.Frame, ∃ source condition : U32,
      before.frames.val[index.val]? = some frame ∧
      index.val + depth + 1 = before.frames.val.length ∧
      FrameScope locals before scope frame ∧
      frame.height.val = slots locals + slots scope.front ∧
      source.val = slots locals + slots (scope.front ++ discarded) ∧
      source.val + slots scope.branchTypes + 1 = before.height.val ∧
      before.before.val[before.before.val.length - 1]? = some condition ∧
      condition.val = slots locals + slots stack := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨index, frame, found, position, shape, _, height⟩ :=
    invariant.frames.selected_live invariant.entryChain entered depth scope selected
  have layout : CompilerLayout before (stack ++ [.I32]) := input ▸ retained.layout
  obtain ⟨condition, conditionAt, conditionSlot⟩ := layout.condition
  have grouped : CompilerLayout before (scope.front ++ discarded ++ (scope.branchTypes ++ [.I32])) := by
    simpa only [targetStack, List.append_assoc] using layout
  obtain ⟨source, sourcePosition, sourceWidth⟩ := branch_source_coordinate grouped retained.localsEq
  refine ⟨index, frame, source, condition, found, position, shape, height, sourcePosition, ?_, conditionAt, ?_⟩
  · simpa [slots_append, slots, width, Nat.add_assoc] using sourceWidth
  · simpa only [retained.localsEq] using conditionSlot

end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixTerminal -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefix.terminate {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition instruction emitted}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (dead : after.reachable = false)
    (ordinary : CompilerOrdinaryStable before after)
    (emission : TerminalEmission locals returns (Sequence.stackTypes raw) instruction emitted)
    (codeEq : after.function.code.val = before.function.code.val ++ [emitted])
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, ordinary.stable.fields.2.2.2.2.1]; exact retained.localsEq
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames) [emitted]
    codeEq (by rw [ordinary.controls])).advance instruction
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append, List.length_singleton]; omega
  exact ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance instruction,
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance instruction, (by intro live; simp [dead] at live),
    .terminal dead entered (retained.terminate emission codeEq ordinary.frames localsEq),
    invariant.arms.append retained.sites [emitted] instruction codeEq ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩

end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixBranch -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A forward branch carries the complete compiler invariant into terminal
source mode, retaining its selected scope and its actual appended fixup. -/
theorem StructuredCompilerPrefix.branch_forward {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (dead : after.reachable = false)
    (stable : CompilerStable before after) (maps : after.function.controls = before.function.controls)
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count old : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame) (forward : frame.kind ≠ .Loop)
    (framePosition : index + depth + 1 = before.frames.val.length)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (stackEq : Sequence.stackTypes raw = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (sitePosition : site.val = before.function.code.val.length + (if count = 0#u32 ∨ src = dst then 0 else 1))
    (appended : fixups.val = frame.fixups.val ++ [site])
    (codeEq : after.function.code.val = before.function.code.val ++ branchInstructions dst src count old)
    (framesEq : after.frames.val = before.frames.val.set index {frame with end_reachable := true, fixups})
    (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth))) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact retained.localsEq
  have frames := (invariant.frames.record_branch index frame fixups found forward framesEq
    (fun _ _ shape => shape.extend (branchInstructions dst src count old) codeEq (by rw [maps]))).advance (.BR (.mk_uN depth))
  have clean : DormantFrames after.frames.val := by
    rw [framesEq]
    exact invariant.frames.record_branch_dormant invariant.entryChain entered invariant.dormant index frame fixups found
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append]
    unfold branchInstructions
    split <;> simp
  exact ⟨invariant.metadata.trans stable, frames, invariant.entryChain.advance (.BR (.mk_uN depth)), clean, invariant.conditions.advance (.BR (.mk_uN depth)), (by intro live; simp [dead] at live),
    .terminal dead entered (retained.branch_forward frame index depth scope dst src count old site fixups found framePosition
      scopeAt discarded stackEq destination source width sitePosition appended codeEq framesEq localsEq),
    invariant.arms.branch_forward retained.sites frame index depth dst src count old site fixups found framePosition sitePosition appended codeEq framesEq,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) maps)
      (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩

theorem StructuredCompilerPrefix.branch_if_forward {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition stack}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (live : after.reachable = true)
    (stable : CompilerStable before after) (maps : after.function.controls = before.function.controls)
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count old condition resume : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame) (forward : frame.kind ≠ .Loop)
    (framePosition : index + depth + 1 = before.frames.val.length)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (inputStack : Sequence.stackTypes raw = stack ++ [.I32])
    (stackEq : stack = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (sitePosition : site.val = before.function.code.val.length + (if count = 0#u32 ∨ src = dst then 0 else 2))
    (appended : fixups.val = frame.fixups.val ++ [site])
    (codeEq : after.function.code.val = before.function.code.val ++ branchIfInstructions dst src count old condition resume)
    (framesEq : after.frames.val = before.frames.val.set index {frame with end_reachable := true, fixups})
    (sourceTypes : SourceStack nextRaw stack) (layout : CompilerLayout after stack)
    (conditionSlot : condition.val = slots locals + slots stack)
    (resumePosition : resume.val = before.function.code.val.length + (if count = 0#u32 ∨ src = dst then 1 else 3)) (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth))) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact retained.localsEq
  have frames := (invariant.frames.record_branch index frame fixups found forward framesEq
    (fun _ _ shape => shape.extend (branchIfInstructions dst src count old condition resume) codeEq (by rw [maps]))).advance (.BR_IF (.mk_uN depth))
  have clean : DormantFrames after.frames.val := by
    rw [framesEq]
    exact invariant.frames.record_branch_dormant invariant.entryChain entered invariant.dormant index frame fixups found
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append]
    unfold branchIfInstructions
    split <;> simp
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.advance (.BR_IF (.mk_uN depth)), clean, invariant.conditions.advance (.BR_IF (.mk_uN depth)), (fun _ => sourceTypes.concrete),
    .live live entered ?_,
    invariant.arms.branch_if_forward retained.sites frame index depth dst src count old condition resume site fixups found framePosition sitePosition appended codeEq framesEq,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) maps)
      (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
  have next := (inputStack ▸ retained).branch_if_forward frame index depth scope dst src count old condition resume site fixups
    found framePosition scopeAt discarded stackEq destination source width sitePosition appended codeEq framesEq localsEq
    layout conditionSlot resumePosition
  simpa only [sourceTypes.decoded] using next

end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixLoopBranch -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefix.branch_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (dead : after.reachable = false)
    (ordinary : CompilerOrdinaryStable before after)
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count : U32)
    (found : before.frames.val[index]? = some frame) (isLoop : frame.kind = .Loop)
    (framePosition : index + depth + 1 = before.frames.val.length)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (stackEq : Sequence.stackTypes raw = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (codeEq : after.function.code.val = before.function.code.val ++ branchInstructions dst src count frame.start_pc)
    (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth))) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, ordinary.stable.fields.2.2.2.2.1]; exact retained.localsEq
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames)
    (branchInstructions dst src count frame.start_pc) codeEq (by rw [ordinary.controls])).advance (.BR (.mk_uN depth))
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append]
    unfold branchInstructions
    split <;> simp
  exact ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance (.BR (.mk_uN depth)),
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance (.BR (.mk_uN depth)), (by intro live; simp [dead] at live),
    .terminal dead entered (retained.branch_loop frame index depth scope dst src count found framePosition isLoop
      scopeAt discarded stackEq destination source width codeEq ordinary.frames localsEq),
    invariant.arms.append retained.sites (branchInstructions dst src count frame.start_pc) (.BR (.mk_uN depth)) codeEq ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩

theorem StructuredCompilerPrefix.branch_if_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition stack}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (live : after.reachable = true)
    (ordinary : CompilerOrdinaryStable before after)
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count condition resume : U32)
    (found : before.frames.val[index]? = some frame) (isLoop : frame.kind = .Loop)
    (framePosition : index + depth + 1 = before.frames.val.length)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (inputStack : Sequence.stackTypes raw = stack ++ [.I32])
    (stackEq : stack = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (codeEq : after.function.code.val = before.function.code.val ++ branchIfInstructions dst src count frame.start_pc condition resume)
    (sourceTypes : SourceStack nextRaw stack) (layout : CompilerLayout after stack)
    (conditionSlot : condition.val = slots locals + slots stack) (resumePosition : resume.val = after.function.code.val.length) (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth))) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, ordinary.stable.fields.2.2.2.2.1]; exact retained.localsEq
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames)
    (branchIfInstructions dst src count frame.start_pc condition resume) codeEq (by rw [ordinary.controls])).advance (.BR_IF (.mk_uN depth))
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append]
    unfold branchIfInstructions
    split <;> simp
  refine ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance (.BR_IF (.mk_uN depth)),
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance (.BR_IF (.mk_uN depth)), (fun _ => sourceTypes.concrete),
    .live live entered ?_,
    invariant.arms.append retained.sites (branchIfInstructions dst src count frame.start_pc condition resume) (.BR_IF (.mk_uN depth)) codeEq ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩
  have next := (inputStack ▸ retained).branch_if_loop frame index depth scope dst src count condition resume
    found framePosition isLoop scopeAt discarded stackEq destination source width codeEq ordinary.frames localsEq
    layout conditionSlot resumePosition
  simpa only [sourceTypes.decoded] using next

end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixOpenDormant -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Opening source inside a terminal or omitted prefix retains only the saved
parent code. No executable relation is asserted for the new omitted child. -/
theorem StructuredCompilerPrefix.open_dormant {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (dead : before.reachable = false) (deadAfter : after.reachable = false)
    (child : SourceScope) (frame : runtime.compiler.Frame)
    (stable : CompilerStable before after)
    (aligned : ScopeFrameStack locals after (parents ++ [current]) child)
    (codeEq : after.function.code = before.function.code)
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (maps : after.function.controls.val.length = before.function.controls.val.length + 1)
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (clean : DormantFrame frame) (fresh : child.form.isElse = false)
    (childEntered : child.entered = false)
    (entry : child.entry = before.function.code.val.length)
    (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child nextRaw nextPosition := by
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]
    exact invariant.mode.locals
  have childCondition : ScopeCondition locals child := by
    unfold ScopeCondition
    split <;> simp [childEntered]
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by rw [codeEq]; omega
  refine ⟨invariant.metadata.trans stable, aligned,
    invariant.entryChain.push child (by simp [childEntered]),
    (by rw [framesEq]; exact invariant.dormant.push frame clean),
    invariant.conditions.push child childCondition, (by intro live; simp [deadAfter] at live), ?_,
    invariant.arms.open_plain invariant.mode.sites child frame [] fresh
      (by simp [codeEq]) framesEq noGuard noBranches,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    invariant.controlBudget.enter maps (by simp [framesEq]) consumed, cursor⟩
  apply StructuredPrefixMode.dormant deadAfter
  cases invariant.mode with
  | live reachable _ _ => simp [dead] at reachable
  | terminal _ parentEntered retained =>
    exact retained.open_dormant child frame codeEq framesEq noGuard noBranches localsEq parentEntered childEntered entry
  | dormant _ retained =>
    exact retained.open_dormant child frame codeEq framesEq noGuard noBranches localsEq childEntered entry

end Itasca.Runtime.Compiler

end
