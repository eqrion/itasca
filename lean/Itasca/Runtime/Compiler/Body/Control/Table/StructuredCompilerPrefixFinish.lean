import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalTerminal
import Itasca.Runtime.Compiler.Body.Lowering.Simd.SimdEmissionExclusion
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalCloseDeadElse
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredIfEndPrefix
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalCloseIf
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalEmpty
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredFunction

/-!
Sections, each formerly its own module: CumulativeTableExclusion, StructuredCompilerPrefix, StructuredPrefixDead, StructuredCompilerPrefixCompleted, StructuredCompilerPrefixElse, StructuredCompilerPrefixElseDormant, StructuredCompilerPrefixCloseElse, StructuredCompilerPrefixCloseBlock, StructuredCompilerPrefixCloseIf, StructuredCompilerPrefixCloseLoop, StructuredCompilerPrefixCloseDormant, StructuredCompilerPrefixEndEffects, StructuredCompilerPrefixAdvance, StructuredCompilerPrefixObserve, StructuredCompilerPrefixFinish.
-/

/-! ## CumulativeTableExclusion -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem StatefulEmission.not_branch_table {pairs C before instruction emitted after}
    (h : StatefulEmission pairs C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | instruction stack input output op => cases op <;> simp [SourceMachine.Stateful.Instruction.source]

theorem SimdEmission.not_branch_table {immediates constants C before instruction emitted after}
    (h : SimdEmission immediates constants C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  intro same
  have tag := h.allowed.source_tag
  simp only [same,SourceMachine.simdSourceTag] at tag
  contradiction

end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Reachability selects a retained executable prefix, a terminal prefix, or
an unentered subtree. No continuation is assumed for an omitted subtree. -/
inductive StructuredPrefixMode (jumpTables : List Aeneas.Std.U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (stack : List valtype) : Prop where
  | live (reachable : compiler.reachable = true) (entered : current.entered = true)
      (retained : StructuredUniversalPrefix (jumpTables := jumpTables) emit compiler types functions returns locals parents current stack)
  | terminal (reachable : compiler.reachable = false) (entered : current.entered = true)
      (retained : StructuredUniversalTerminal (jumpTables := jumpTables) emit compiler types functions returns locals parents current)
  | dormant (reachable : compiler.reachable = false)
      (retained : StructuredUniversalDormant (jumpTables := jumpTables) emit compiler types functions returns locals parents current)

/-- The retained compiler invariant at an actual source-reader boundary. Its
components concern source syntax, physical frames, emitted code, and byte/slot
accounting; none assumes execution correctness. -/
structure StructuredCompilerPrefix (jumpTables : List Aeneas.Std.U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (raw : List code.StackType) (position : Nat) : Prop where
  metadata : CompilerStable initial compiler
  frames : ScopeFrameStack locals compiler parents current
  entryChain : SourceEntryChain parents current
  dormant : DormantFrames compiler.frames.val
  conditions : ScopeConditions locals parents current
  known : compiler.reachable = true → ConcreteStack raw
  mode : StructuredPrefixMode (jumpTables := jumpTables) emit compiler types functions returns locals parents current (Sequence.stackTypes raw)
  arms : StructuredUniversalElse (jumpTables := jumpTables) emit compiler types functions returns locals parents current
  sources : SourceAligned compiler
  codeBudget : SourceCodeBudget compiler position
  controlBudget : SourceControlBudget compiler position
  cursor : compiler.next_source.val ≤ position

theorem StructuredCompilerPrefix.live {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) :
    current.entered = true ∧
      StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current (Sequence.stackTypes raw) := by
  cases invariant.mode with
  | live _ entered retained => exact ⟨entered, retained⟩
  | terminal dead _ _ => simp [reachable] at dead
  | dormant dead _ => simp [reachable] at dead

theorem StructuredCompilerPrefix.capacities {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (bound : position ≤ limits.MAX_MODULE_BYTES.val) :
    before.function.code.val.length < Usize.max ∧
      before.function.source_offsets.val.length < Usize.max ∧
      before.function.controls.val.length < Usize.max ∧ before.frames.val.length < Usize.max := by
  have code := invariant.codeBudget.code_capacity bound
  have controls := invariant.controlBudget.capacities bound
  exact ⟨code, by rw [invariant.sources]; exact code, controls⟩

theorem StructuredCompilerPrefix.ordinary {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition instruction emitted output}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true)
    (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLowered before after nextRaw emitted output)
    (emission : emit (Sequence.stackTypes raw) instruction [emitted] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition)
    (notTable : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback := by intro _ _ h; cases h) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames) [emitted]
    lowered.1.1 (by rw [ordinary.controls])).advance instruction
  have next := lowered.1.structured_universal_advance ordinary.frames retained emission notTable
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [lowered.1.1, List.length_append, List.length_singleton]; omega
  refine ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance instruction,
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance instruction, (fun _ => lowered.2.concrete),
    .live (lowered.1.2.2.2.1.trans reachable) entered ?_,
    invariant.arms.append retained.sites [emitted] instruction lowered.1.1 ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩
  simpa only [lowered.2.decoded] using next

end Itasca.Runtime.Compiler

end

/-! ## StructuredPrefixDead -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredPrefixMode.sites {jumpTables : List Aeneas.Std.U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (mode : StructuredPrefixMode (jumpTables := jumpTables) emit compiler types functions returns locals parents current stack) :
    ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame := by
  cases mode with
  | live _ _ retained => exact retained.sites
  | terminal _ _ retained => exact retained.sites
  | dormant _ retained => exact retained.sites

theorem StructuredPrefixMode.locals {jumpTables : List Aeneas.Std.U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (mode : StructuredPrefixMode (jumpTables := jumpTables) emit compiler types functions returns locals parents current stack) :
    compilerLocals compiler = locals := by
  cases mode with
  | live _ _ retained => exact retained.localsEq
  | terminal _ _ retained => exact retained.localsEq
  | dormant _ retained => exact retained.localsEq

/-- A successful ordinary callback in dead code retains the source suffix but
cannot create a new executable continuation. -/
theorem StructuredCompilerPrefix.skip {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (instruction : instr) (dead : before.reachable = false) (deadAfter : after.reachable = false)
    (ordinary : CompilerOrdinaryStable before after) (unchanged : after.function.code = before.function.code)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition := by
  have code : after.function.code.val = before.function.code.val ++ [] := by simpa only [List.append_nil, unchanged]
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames) []
    code (by rw [ordinary.controls])).advance instruction
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by rw [unchanged]; omega
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, ordinary.stable.fields.2.2.2.2.1]
    exact invariant.mode.locals
  refine ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance instruction,
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance instruction, (by simp [deadAfter]), ?_,
    invariant.arms.append invariant.mode.sites [] instruction code ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩
  cases invariant.mode with
  | live reachable _ _ => simp [dead] at reachable
  | terminal _ entered retained =>
    exact .terminal deadAfter entered (retained.skip instruction (congrArg (fun code => code.val) unchanged) ordinary.frames localsEq)
  | dormant _ retained => exact .dormant deadAfter (retained.skip instruction unchanged ordinary.frames localsEq)

end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixCompleted -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- An entered source arm ends either with its exact result stack or with the
retained terminal source prefix. The actual compiler bit selects its exit kind. -/
theorem StructuredCompilerPrefix.completed {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results) :
    StructuredCompletedPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current before.reachable := by
  cases invariant.mode with
  | live reachable _ retained =>
    rw [reachable]
    exact (stack reachable ▸ retained).completed
  | terminal dead _ retained =>
    rw [dead]
    exact retained.completed
  | dormant _ retained =>
    have impossible := retained.unentered
    simp [entered] at impossible

end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixElse -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- ELSE retains the completed then arm and restores the sibling's exact
source input, including the original guard coordinate and all outer plans. -/
theorem StructuredCompilerPrefix.begin_else {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (entered : current.entered = true) (live : after.reachable = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (guard site : Usize) (condition old noEntry : U32) (fixups : alloc.vec.Vec Usize)
    (change : ElseTransition before after prior frame guard site condition old noEntry fixups before.reachable)
    (bt : blocktype) (form : current.form = .then_ bt condition) (guardEq : frame.if_pc = some guard)
    (layout : CompilerLayout after current.input) (sourceTypes : SourceStack nextRaw current.input)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (current.begin_else bt condition before.function.code.val.length noEntry before.reachable) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts prior frame change.beforeFrames
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have conditionSlot : condition.val = slots locals + slots current.input := by
    have stored := invariant.conditions.current
    have offset : current.entered = true → condition.val = slots locals + slots current.input := by
      simpa only [ScopeCondition, form] using stored
    exact offset entered
  have entry : current.entry = guard.val := by
    have coordinate := shape.guard
    simpa [guardEq, SourceScope.guardPosition, form, entered] using coordinate.symm
  have body : current.bodyPc = current.entry + 1 := by
    simpa [SourceScope.bodyStart, form, entered] using shape.body
  have kind : frame.kind = .Then := by simpa [form, ScopeForm.kind] using shape.kind
  have distinct := invariant.frames.distinct_guard prior frame change.beforeFrames guard guardEq
  obtain ⟨next, arms⟩ := (invariant.completed entered stack).begin_else invariant.arms prior frame guard site condition old noEntry fixups
    change bt form entered entry body conditionSlot kind guardEq distinct localsEq layout
  have frames := invariant.frames.begin_else prior frame guard site condition old noEntry fixups before.reachable
    change bt form guardEq (by rw [maps])
  have clean : DormantFrames after.frames.val := by
    rw [change.afterFrames]
    have previous : DormantFrames (prior ++ [frame]) := change.beforeFrames ▸ invariant.dormant
    exact previous.replace_last _ (DormantFrame.entered (shape.entered.trans entered))
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [change.length, change.noPosition]
    split <;> omega
  refine ⟨invariant.metadata.trans stable, frames,
    invariant.entryChain.begin_else bt condition before.function.code.val.length noEntry before.reachable,
    clean, invariant.conditions.begin_else bt condition form before.function.code.val.length noEntry before.reachable,
    (fun _ => sourceTypes.concrete), .live live entered ?_, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport maps (by simp [change.afterFrames, change.beforeFrames])).advance (Nat.le_of_lt consumed), cursor⟩
  simpa only [sourceTypes.decoded] using next

end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixElseDormant -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- An ELSE reached inside an unentered IF changes the retained source arm
without assigning bytecode to either omitted arm. -/
theorem StructuredCompilerPrefix.begin_else_dormant {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (unentered : current.entered = false) (dead : after.reachable = false)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (beforeFrames : before.frames.val = prior ++ [frame])
    (afterFrames : after.frames.val = prior ++ [{frame with kind := .Else, if_pc := none}])
    (codeEq : after.function.code = before.function.code)
    (bt : blocktype) (condition noEntry : U32) (form : current.form = .then_ bt condition)
    (positionEq : noEntry.val = before.function.code.val.length)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (current.begin_else bt condition noEntry.val noEntry false) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts prior frame beforeFrames
  have kind : frame.kind = .Then := by simpa [form, ScopeForm.kind] using shape.kind
  have noGuard : frame.if_pc = none := by
    simpa [SourceScope.guardPosition, form, unentered] using shape.guard
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have retained : StructuredUniversalDormant (jumpTables := jumpTables) emit before types functions returns locals parents current := by
    cases invariant.mode with
    | live _ entered _ => simp [unentered] at entered
    | terminal _ entered _ => simp [unentered] at entered
    | dormant _ retained => exact retained
  obtain ⟨next, arms⟩ := retained.begin_else invariant.arms prior frame beforeFrames afterFrames kind noGuard
    codeEq localsEq bt condition noEntry noEntry.val false form
  have frames := invariant.frames.begin_else_dormant prior frame bt condition form noEntry positionEq
    beforeFrames afterFrames (congrArg (fun code => code.val) codeEq) (by rw [maps])
  have clean : DormantFrames after.frames.val := by
    rw [afterFrames]
    have previous : DormantFrames (prior ++ [frame]) := beforeFrames ▸ invariant.dormant
    apply previous.replace_last
    intro inactive
    exact previous frame (by simp) inactive
  refine ⟨invariant.metadata.trans stable, frames,
    invariant.entryChain.begin_else bt condition noEntry.val noEntry false, clean,
    invariant.conditions.begin_else bt condition form noEntry.val noEntry false, (by intro live; simp [dead] at live),
    .dormant dead next, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by simp [codeEq]) consumed,
    (invariant.controlBudget.transport maps (by simp [beforeFrames, afterFrames])).advance (Nat.le_of_lt consumed), cursor⟩
end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixCloseElse -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Closing an explicit ELSE joins the saved then arm and completed else
arm, preserving either a live or a terminal parent continuation. -/
theorem StructuredCompilerPrefix.close_else {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) child raw position)
    (entered : child.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = child.front ++ child.results)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (condition noEntry : U32) (yes : List instr) (yesExit : Nat) (yesNormal : Bool)
    (framesEq : before.frames.val = after.frames.val ++ [frame])
    (positionEq : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (form : child.form = .else_ bt condition yes yesExit noEntry yesNormal)
    (signature : BlockSignature types bt child.params child.results)
    (exit : after.reachable = (before.reachable || frame.end_reachable))
    (layout : CompilerLayout after (child.front ++ child.results))
    (sourceTypes : SourceStack nextRaw (child.front ++ child.results))
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts after.frames.val frame framesEq
  have kind : frame.kind = .Else := by simpa [form, ScopeForm.kind] using shape.kind
  have noGuard : frame.if_pc = none := by
    have guard := shape.guard
    simpa [form, SourceScope.guardPosition] using guard
  have parentEntered := invariant.entryChain.ancestor entered parent (by simp)
  have height := shape.height entered
  have width := shape.results
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have branches := (invariant.mode.sites frame (by simp [framesEq])).branches
  have yesClosed := shape.elseLive bt condition yes yesExit noEntry yesNormal form
  have completed := invariant.completed entered stack
  have result : StructuredPrefixMode (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) (Sequence.stackTypes nextRaw) ∧
      StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents (parent.advance (.IFELSE bt yes child.source)) := by
    cases normal : before.reachable with
    | true =>
      obtain ⟨next, arms⟩ := completed.close_else invariant.arms frame target bt condition noEntry yes yesExit yesNormal
        framesEq kind noGuard height width positionEq codeEq localsEq layout form parentEntered entered signature
      refine ⟨StructuredPrefixMode.live (current := parent.advance (.IFELSE bt yes child.source)) (by simp [exit, normal]) (by exact parentEntered) ?_, arms⟩
      simpa only [sourceTypes.decoded] using next
    | false =>
      cases marked : frame.end_reachable with
      | true =>
        obtain ⟨next, arms⟩ := completed.close_else invariant.arms frame target bt condition noEntry yes yesExit yesNormal
          framesEq kind noGuard height width positionEq codeEq localsEq layout form parentEntered entered signature
        refine ⟨StructuredPrefixMode.live (current := parent.advance (.IFELSE bt yes child.source)) (by simp [exit, normal, marked]) (by exact parentEntered) ?_, arms⟩
        simpa only [sourceTypes.decoded] using next
      | false =>
        have yesDead : yesNormal = false := by
          cases yesEq : yesNormal with
          | false => rfl
          | true => have impossible := yesClosed yesEq; simp [marked] at impossible
        obtain ⟨next, arms⟩ := (normal ▸ completed).close_else_dead invariant.arms frame target bt condition noEntry yes yesExit yesNormal
          framesEq kind noGuard height width positionEq codeEq localsEq marked yesDead form parentEntered entered signature
        exact ⟨StructuredPrefixMode.terminal (current := parent.advance (.IFELSE bt yes child.source)) (by simp [exit, normal, marked]) (by exact parentEntered) next, arms⟩
  have frames := (invariant.frames.close_branches frame target framesEq branches codeEq (by rw [maps])).advance (.IFELSE bt yes child.source)
  have clean : DormantFrames after.frames.val := (framesEq ▸ invariant.dormant).pop
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by simp [codeEq, patch_code_length]
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.pop.advance _, clean,
    invariant.conditions.pop.advance _, (fun _ => sourceTypes.concrete), result.1, result.2, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by omega) consumed,
    (invariant.controlBudget.transport maps (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixCloseBlock -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Closing an entered BLOCK restores either its live parent prefix or its
terminal parent prefix, according to the actual normal/branch exit flags. -/
theorem StructuredCompilerPrefix.close_block {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) child raw position)
    (entered : child.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = child.front ++ child.results)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (framesEq : before.frames.val = after.frames.val ++ [frame])
    (positionEq : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (form : child.form = .block bt)
    (signature : BlockSignature types bt child.params child.results)
    (exit : after.reachable = (before.reachable || frame.end_reachable))
    (layout : CompilerLayout after (child.front ++ child.results))
    (sourceTypes : SourceStack nextRaw (child.front ++ child.results))
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.BLOCK bt child.source)) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts after.frames.val frame framesEq
  have kind : frame.kind = .Block := by simpa [form, ScopeForm.kind] using shape.kind
  have noGuard : frame.if_pc = none := by
    have guard := shape.guard
    simpa [form, SourceScope.guardPosition] using guard
  have entry : child.entry = child.bodyPc := by
    simpa [form, SourceScope.bodyStart] using shape.body.symm
  have parentEntered := invariant.entryChain.ancestor entered parent (by simp)
  have height := shape.height entered
  have width := shape.results
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have branches := (invariant.mode.sites frame (by simp [framesEq])).branches
  let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], before.reachable, frame.end_reachable⟩
  have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
    refine ⟨fun _ => height, fun _ => width, ?_, Nat.le_of_eq positionEq.symm,
      fun _ => Nat.le_of_eq positionEq.symm, ?_, ?_, fun h => h, ?_, ?_⟩
    · intro _; simpa [kind, label] using width
    · simp [kind]
    · simp [kind]
    · intros; rfl
    · simp [noGuard]
  have labelShape : ScopeLabel child label := by
    refine ⟨rfl, ?_, rfl⟩
    simp [SourceScope.branchTypes, form, label]
  have arms := invariant.arms.pop frame label 0#u32 framesEq future labelShape
    (by simpa [frameGroups, noGuard, label, resolvedCode] using codeEq) (.BLOCK bt child.source)
  have frames := (invariant.frames.close_branches frame target framesEq branches codeEq (by rw [maps])).advance (.BLOCK bt child.source)
  have clean : DormantFrames after.frames.val := (framesEq ▸ invariant.dormant).pop
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by simp [codeEq, patch_code_length]
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.pop.advance _, clean,
    invariant.conditions.pop.advance _, (fun _ => sourceTypes.concrete), ?_, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by omega) consumed,
    (invariant.controlBudget.transport maps (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
  cases mode : invariant.mode with
  | live reachable childEntered retained =>
    have typed := stack reachable
    have next := (typed ▸ retained).close_block frame target bt framesEq kind noGuard height width
      positionEq codeEq localsEq layout form entry parentEntered entered signature
    refine StructuredPrefixMode.live (current := parent.advance (.BLOCK bt child.source)) (by simp [exit, reachable]) (by exact parentEntered) ?_
    simpa only [sourceTypes.decoded] using next
  | terminal dead childEntered retained =>
    cases branchesLive : frame.end_reachable with
    | false =>
      exact .terminal (by simp [exit, dead, branchesLive]) parentEntered
        (retained.close_block_dead frame target bt framesEq kind noGuard height width positionEq codeEq localsEq
          branchesLive form entry parentEntered entered signature)
    | true =>
      refine StructuredPrefixMode.live (current := parent.advance (.BLOCK bt child.source)) (by simp [exit, dead, branchesLive]) (by exact parentEntered) ?_
      have next := retained.close_block_resume frame target bt framesEq kind noGuard height width positionEq codeEq
        localsEq layout branchesLive form entry parentEntered entered signature
      simpa only [sourceTypes.decoded] using next
  | dormant dead retained =>
    have impossible := retained.unentered
    simp [entered] at impossible
end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixCloseIf -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A live-entered IF without ELSE restores the identity arm at END, so the
parent becomes live even when the then body itself ended in a branch. -/
theorem StructuredCompilerPrefix.close_if {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) child raw position)
    (entered : child.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = child.front ++ child.results)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype) (guard : Usize) (condition old : U32)
    (framesEq : before.frames.val = after.frames.val ++ [frame])
    (guardEq : frame.if_pc = some guard)
    (guardCode : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (positionEq : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode
      (before.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target)
    (form : child.form = .then_ bt condition)
    (signature : BlockSignature types bt child.params child.results)
    (sameTypes : child.params = child.results) (live : after.reachable = true)
    (layout : CompilerLayout after (child.front ++ child.results))
    (sourceTypes : SourceStack nextRaw (child.front ++ child.results))
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.IFELSE bt child.source [])) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts after.frames.val frame framesEq
  have kind : frame.kind = .Then := by simpa [form, ScopeForm.kind] using shape.kind
  have entry : child.entry = guard.val := by
    simpa [guardEq, SourceScope.guardPosition, form, entered] using shape.guard.symm
  have body : child.bodyPc = child.entry + 1 := by
    simpa [SourceScope.bodyStart, form, entered] using shape.body
  have parentEntered := invariant.entryChain.ancestor entered parent (by simp)
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have branches := (invariant.mode.sites frame (by simp [framesEq])).branches
  have distinct := invariant.frames.distinct_guard after.frames.val frame framesEq guard guardEq
  have conditionSlot : condition.val = slots locals + slots child.input := by
    have stored : child.entered = true → condition.val = slots locals + slots child.input := by
      simpa [ScopeCondition, form] using invariant.conditions.current
    exact stored entered
  obtain ⟨next, arms⟩ := (invariant.completed entered stack).close_if invariant.arms frame target bt
    guard condition old framesEq kind guardEq guardCode distinct (shape.height entered) shape.results positionEq codeEq
    localsEq layout form entry body conditionSlot sameTypes parentEntered entered signature
  have frames := (invariant.frames.close_guard frame guard condition old target framesEq guardEq guardCode
    branches codeEq (by rw [maps])).advance (.IFELSE bt child.source [])
  have clean : DormantFrames after.frames.val := (framesEq ▸ invariant.dormant).pop
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by simp [codeEq, patch_code_length]
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.pop.advance _, clean,
    invariant.conditions.pop.advance _, (fun _ => sourceTypes.concrete), ?_, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by omega) consumed,
    (invariant.controlBudget.transport maps (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
  refine StructuredPrefixMode.live live (by exact parentEntered) ?_
  simpa only [sourceTypes.decoded] using next
end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixCloseLoop -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Closing an entered LOOP preserves its normal reachability; backward
branches do not create a forward exit. -/
theorem StructuredCompilerPrefix.close_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) child raw position)
    (entered : child.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = child.front ++ child.results)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (framesEq : before.frames.val = after.frames.val ++ [frame])
    (positionEq : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = before.function.code.val)
    (form : child.form = .loop bt)
    (signature : BlockSignature types bt child.params child.results)
    (exit : after.reachable = before.reachable)
    (layout : CompilerLayout after (child.front ++ child.results))
    (sourceTypes : SourceStack nextRaw (child.front ++ child.results))
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.LOOP bt child.source)) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts after.frames.val frame framesEq
  have kind : frame.kind = .Loop := by simpa [form, ScopeForm.kind] using shape.kind
  have noGuard : frame.if_pc = none := by
    have guard := shape.guard
    simpa [form, SourceScope.guardPosition] using guard
  have entry : child.entry = frame.start_pc.val := by
    simpa [form, SourceScope.frameStart] using shape.start.symm
  have body : child.bodyPc = frame.start_pc.val + 1 := by
    simpa [form, SourceScope.bodyStart, entered, entry] using shape.body
  have head : before.function.code.val[frame.start_pc.val]? = some .LoopHead := by
    have actual : before.function.code.val[child.entry]? = some .LoopHead := by
      have hook : child.entered = true → before.function.code.val[child.entry]? = some .LoopHead := by
        simpa [ScopeEntryCode, form] using shape.entryCode
      exact hook entered
    simpa [entry] using actual
  obtain ⟨noFixups, ends⟩ := shape.loopClean bt form
  have parentEntered := invariant.entryChain.ancestor entered parent (by simp)
  have height := shape.height entered
  have width := shape.results
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have branches := (invariant.mode.sites frame (by simp [framesEq])).branches
  let label : LabelTarget := ⟨child.front, child.params, child.results, frame.start_pc, target.val, [.LOOP bt child.source], [], before.reachable, true⟩
  have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
    refine ⟨fun _ => height, fun _ => width, ?_, Nat.le_of_eq positionEq.symm, ?_,
      fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
    · intro _; simpa [kind, label] using shape.params
    · simp [kind]
    · simp [kind]
    · simp [noGuard]
  have labelShape : ScopeLabel child label := by
    refine ⟨rfl, ?_, rfl⟩
    simp [SourceScope.branchTypes, form, label]
  have arms := invariant.arms.pop frame label 0#u32 framesEq future labelShape
    (by simpa [frameGroups, noGuard, noFixups, label, resolvedCode, patchCode] using codeEq) (.LOOP bt child.source)
  have frames := (invariant.frames.close_branches frame target framesEq branches (by simpa [noFixups, patchCode] using codeEq) (by rw [maps])).advance (.LOOP bt child.source)
  have clean : DormantFrames after.frames.val := (framesEq ▸ invariant.dormant).pop
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by simp [codeEq, patch_code_length]
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.pop.advance _, clean,
    invariant.conditions.pop.advance _, (fun _ => sourceTypes.concrete), ?_, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by omega) consumed,
    (invariant.controlBudget.transport maps (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
  cases mode : invariant.mode with
  | live reachable childEntered retained =>
    have typed := stack reachable
    have next := (typed ▸ retained).close_loop frame target bt framesEq kind noGuard noFixups height shape.params width
      positionEq codeEq localsEq layout form entry body head parentEntered entered signature
    refine StructuredPrefixMode.live (current := parent.advance (.LOOP bt child.source)) (exit.trans reachable) (by exact parentEntered) ?_
    simpa only [sourceTypes.decoded] using next
  | terminal dead childEntered retained =>
    exact .terminal (exit.trans dead) parentEntered
      (retained.close_loop frame target bt framesEq kind noGuard noFixups height shape.params width positionEq codeEq localsEq
        form entry body head parentEntered entered signature)
  | dormant dead retained =>
    have impossible := retained.unentered
    simp [entered] at impossible
end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixCloseDormant -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- END of an unentered child emits no code and restores its parent's
terminal or dormant source cursor without inventing a body certificate. -/
theorem StructuredCompilerPrefix.close_dormant {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) child raw position)
    (unentered : child.entered = false) (dead : after.reachable = false)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (frame : runtime.compiler.Frame) (target : U32) (instruction : instr)
    (framesEq : before.frames.val = after.frames.val ++ [frame])
    (positionEq : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = before.function.code.val)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance instruction) nextRaw nextPosition := by
  classical
  obtain ⟨paired, shape⟩ := invariant.frames.parts after.frames.val frame framesEq
  have frameDead := shape.entered.trans unentered
  obtain ⟨noExit, noFixups⟩ := invariant.dormant frame (by simp [framesEq]) frameDead
  have noGuard : frame.if_pc = none := by
    have guard := shape.guard
    cases form : child.form <;> simpa [form, SourceScope.guardPosition, unentered] using guard
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  let label : LabelTarget := ⟨child.front, child.branchTypes, child.results,
    if frame.kind = .Loop then frame.start_pc else target, target.val, [], [], false, decide (frame.kind = .Loop)⟩
  have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
    refine ⟨?_, ?_, ?_, Nat.le_of_eq positionEq.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [frameDead]
    · simp [frameDead]
    · simp [frameDead]
    · intro kind; simpa [label, kind] using Nat.le_of_eq positionEq.symm
    · intro kind; simp [label, kind]
    · intro kind; simp [label, kind]
    · simp [noExit]
    · intro kind notThen; simp [label, kind]
    · simp [noGuard]
  have labelShape : ScopeLabel child label := ⟨rfl, rfl, rfl⟩
  have resolved : after.function.code.val = resolvedCode before.function.code.val (frameGroups frame label 0#u32) := by
    simpa [frameGroups, noGuard, noFixups, resolvedCode, patchCode] using codeEq
  have sites : ∀ other ∈ after.frames.val, FrameSites after.function.code.val other := by
    intro other member
    rw [codeEq]
    exact invariant.mode.sites other (by rw [framesEq]; exact List.mem_append_left _ member)
  have arms := invariant.arms.pop frame label 0#u32 framesEq future labelShape resolved instruction
  have frames := (invariant.frames.pop frame framesEq (fun scope other member previous =>
    previous.transport (by rw [maps]) (by rw [codeEq]) (by rw [codeEq]; exact previous.entryCode))).advance instruction
  have clean : DormantFrames after.frames.val := (framesEq ▸ invariant.dormant).pop
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.pop.advance _, clean,
    invariant.conditions.pop.advance _, (by intro live; simp [dead] at live), ?_, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by simp [codeEq]) consumed,
    (invariant.controlBudget.transport maps (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
  cases mode : invariant.mode with
  | live reachable entered retained => simp [unentered] at entered
  | terminal reachable entered retained => simp [unentered] at entered
  | dormant reachable retained =>
    cases parentEntered : parent.entered with
    | false => exact .dormant dead (retained.close_dormant frame label 0#u32 framesEq future labelShape resolved sites localsEq parentEntered instruction)
    | true =>
      exact StructuredPrefixMode.terminal (current := parent.advance instruction) dead (by exact parentEntered)
        (retained.close_terminal frame label 0#u32 framesEq future labelShape resolved sites localsEq parentEntered instruction)
end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixEndEffects -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Successful END exposes its actual frame removal and fixup effects from
retained scope geometry, without an assumed code transformation. -/
theorem StructuredCompilerPrefix.end_unguarded {jumpTables : List U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (nonBody : current.form.kind ≠ .Body) (noGuard : current.guardPosition = none)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (bound : position ≤ limits.MAX_MODULE_BYTES.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    ∃ frame target, before.frames.val = after.frames.val ++ [frame] ∧
      FrameScope locals before current frame ∧ target.val = before.function.code.val.length ∧
      after.reachable = scopeExitLive before.reachable frame ∧
      after.function.code.val = patchCode before.function.code.val frame.fixups.val target := by
  obtain ⟨prior, frame, frames, paired, shape⟩ := invariant.frames.split
  have priorBound : prior.length ≤ Usize.max := by have := before.frames.property; simp only [frames, List.length_append, List.length_singleton] at this; omega
  let rest := alloc.vec.Vec.from prior priorBound
  have restVal : rest.val = prior := by simp [rest]
  have noIf : frame.if_pc = none := by
    have same := shape.guard.trans noGuard
    simpa using same
  have nonRoot : frame.kind ≠ .Body := by simpa [shape.kind] using nonBody
  have fetchBound := invariant.codeBudget.fetch_bound bound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionEq : target.val = before.function.code.val.length := by simp [target]
  have sites := (invariant.mode.sites frame (by simp [frames])).branches.branches
  have effect := close_scope_effect ops law before state frame rest target (by simpa [restVal] using frames)
    nonRoot noIf positionEq sites shape.mapBound coordinate
  have call : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty = .ok (.Ok (), after) := accepted
  rw [call, WP.spec_ok] at effect
  have result := effect rfl
  dsimp only at result
  obtain ⟨popped, live, codeEq, closed⟩ := result
  exact ⟨frame, target, by simpa [popped, restVal] using frames, shape, positionEq, live, codeEq⟩

/-- The entered THEN frame supplies its exact unresolved guard; END resolves
it and the selected frame's forward branches at the same actual endpoint. -/
theorem StructuredCompilerPrefix.end_guarded {jumpTables : List U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (type : blocktype) (condition : U32) (form : current.form = .then_ type condition)
    (entered : current.entered = true)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (bound : position ≤ limits.MAX_MODULE_BYTES.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    ∃ frame target guard, before.frames.val = after.frames.val ++ [frame] ∧
      FrameScope locals before current frame ∧ target.val = before.function.code.val.length ∧
      frame.if_pc = some guard ∧ before.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX) ∧
      after.reachable = true ∧
      after.function.code.val = patchCode
        (before.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target := by
  obtain ⟨prior, frame, frames, paired, shape⟩ := invariant.frames.split
  have priorBound : prior.length ≤ Usize.max := by have := before.frames.property; simp only [frames, List.length_append, List.length_singleton] at this; omega
  let rest := alloc.vec.Vec.from prior priorBound
  have restVal : rest.val = prior := by simp [rest]
  have thenKind : frame.kind = .Then := by simpa [form, ScopeForm.kind] using shape.kind
  have guardPosition : frame.if_pc.map UScalar.val = some current.entry := by
    simpa [SourceScope.guardPosition, form, entered] using shape.guard
  cases hasGuard : frame.if_pc with
  | none => simp [hasGuard] at guardPosition
  | some guard =>
    have guardAt : guard.val = current.entry := by simpa [hasGuard] using guardPosition
    have hook : before.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX) := by
      have retained : current.entered = true → before.function.code.val[current.entry]? = some (.JumpIfZero condition core.num.U32.MAX) := by
        simpa [ScopeEntryCode, form] using shape.entryCode
      simpa [guardAt] using retained entered
    have fetchBound := invariant.codeBudget.fetch_bound bound
    let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
    have positionEq : target.val = before.function.code.val.length := by simp [target]
    have sites := (invariant.mode.sites frame (by simp [frames])).branches.branches
    have effect := close_guarded_scope_effect ops law before state frame rest target (by simpa [restVal] using frames)
      guard condition core.num.U32.MAX (by simp [thenKind]) hasGuard hook positionEq sites shape.mapBound coordinate
    have call : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty = .ok (.Ok (), after) := accepted
    rw [call, WP.spec_ok] at effect
    have result := effect rfl
    dsimp only at result
    obtain ⟨popped, live, codeEq, closed⟩ := result
    have entryReachable := shape.entered.trans entered
    exact ⟨frame, target, guard, by simpa [popped, restVal] using frames, shape, positionEq, hasGuard, hook,
      by simpa [scopeExitLive, thenKind, entryReachable] using live, codeEq⟩
end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixAdvance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefix.ordinary_empty {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition instruction output}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true)
    (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLoweredEmpty before after nextRaw output)
    (emission : emit (Sequence.stackTypes raw) instruction [] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition)
    (notTable : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback := by intro _ _ h; cases h) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have code : after.function.code.val = before.function.code.val ++ [] := by simpa using congrArg (fun code => code.val) lowered.1.1
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames) []
    code (by rw [ordinary.controls])).advance instruction
  have next := lowered.1.structured_universal_advance ordinary.frames retained emission notTable
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by rw [lowered.1.1]; omega
  refine ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance instruction,
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance instruction, (fun _ => lowered.2.concrete),
    .live (lowered.1.2.2.2.1.trans reachable) entered ?_,
    invariant.arms.append retained.sites [] instruction code ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩
  simpa only [lowered.2.decoded] using next

theorem StructuredCompilerPrefix.call {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition front params results index base}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true)
    (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLowered before after nextRaw (.Call index base) (front ++ results))
    (stack : Sequence.stackTypes raw = front ++ params)
    (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (arguments : base.val = slots locals + slots front)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (current.advance (.CALL (.mk_uN index.val))) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames) [.Call index base]
    lowered.1.1 (by rw [ordinary.controls])).advance (.CALL (.mk_uN index.val))
  have next := lowered.1.structured_universal_call ordinary.frames (stack ▸ retained) signature arguments
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [lowered.1.1, List.length_append, List.length_singleton]; omega
  refine ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance (.CALL (.mk_uN index.val)),
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance (.CALL (.mk_uN index.val)), (fun _ => lowered.2.concrete),
    .live (lowered.1.2.2.2.1.trans reachable) entered ?_,
    invariant.arms.append retained.sites [.Call index base] (.CALL (.mk_uN index.val)) lowered.1.1 ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩
  simpa only [lowered.2.decoded] using next

end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixObserve -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The real dead-opcode path observes the validator without emitting code.
The source instruction may still extend its typed omitted suffix. -/
theorem StructuredCompilerPrefix.dead_op {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (instruction : instr) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false)
    (consumed : position < state.pos.val)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) state.vals.val state.pos.val := by
  unfold runtime.compiler.lower.FunctionCompiler.op at accepted
  rw [if_neg (by simp only [dead, Bool.false_eq_true, not_false_eq_true])] at accepted
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  have ordinary := compiler_observe_ordinary_result ops law before after state (.Ok ()) accepted
  have sources := compiler_observe_sources ops law before after state (.Ok ()) accepted
  have cursor := compiler_observe_cursor ops law before after state (.Ok ()) accepted rfl
  have unchanged : after.function.code = before.function.code := by rw [frame]
  have deadAfter : after.reachable = false := by rw [frame]; exact dead
  exact invariant.skip instruction dead deadAfter ordinary unchanged sources consumed (by rw [cursor])

end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixFinish -/

section

/-!
Root source-code relation and final compiled-body prefix. The finish theorem applies the root relation to the actual retained epilogue.
-/

/-! ## Structured Compiler Prefix Root -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The last source END fixes all root targets and obtains the body relation
from the accumulated compiler prefix, including terminal nonvoid bodies. -/
theorem StructuredCompilerPrefix.root_relation {jumpTables : List Aeneas.Std.U32} {A : Type} {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler types functions returns locals [] current raw position)
    (entered : current.entered = true)
    (stack : compiler.reachable = true → Sequence.stackTypes raw = returns)
    (target : U32) (positionEq : target.val = compiler.function.code.val.length)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns) :
    ∃ frame, compiler.frames.val = [frame] ∧ frame.kind = .Body ∧ frame.if_pc = none ∧
      frame.height.val = slots locals ∧ frame.results.val = slots returns ∧
      frame.map.val < compiler.function.controls.val.length ∧
      BranchSites compiler.function.code.val frame.fixups.val ∧
      StructuredCode emit types functions returns locals (patchCode compiler.function.code.val frame.fixups.val target) jumpTables
        [⟨[], returns, returns, target, target.val, [], [], compiler.reachable, frame.end_reachable⟩]
        [] current.source 0 target.val returns := by
  obtain ⟨prior, frame, split, paired, shape⟩ := invariant.frames.split
  cases paired
  have frames : compiler.frames.val = [frame] := by simpa using split
  have kind : frame.kind = .Body := by simpa [form, ScopeForm.kind] using shape.kind
  have noGuard : frame.if_pc = none := by simpa [form, SourceScope.guardPosition] using shape.guard
  have height : frame.height.val = slots locals := by simpa [front, slots] using shape.height entered
  have width : frame.results.val = slots returns := by simpa [results] using shape.results
  have start : current.bodyPc = 0 := by
    have origin := shape.root form
    simpa [SourceScope.bodyStart, form, origin] using shape.body
  have branchSites := (invariant.mode.sites frame (by simp [frames])).branches.branches
  refine ⟨frame, frames, kind, noGuard, height, width, shape.mapBound, branchSites, ?_⟩
  cases invariant.mode with
  | live live entry retained =>
    have code := (stack live ▸ retained).root_finish frame target frames kind noGuard height width positionEq form front params results start
    simpa only [live] using code
  | terminal dead entry retained =>
    have code := retained.root_finish frame target frames kind noGuard height width positionEq form front params results start
    simpa only [dead] using code
  | dormant dead retained =>
    have impossible := retained.unentered
    simp [entered] at impossible
end Itasca.Runtime.Compiler

end

/-! ## Structured Compiler Prefix Finish -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual final END resolves the retained root certificate and emits its
literal epilogue. Source-byte accounting supplies the final fetch bound. -/
theorem StructuredCompilerPrefix.finish_body {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals [] current raw position)
    (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = returns)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (consumed : position < state.pos.val) (sourceBound : state.pos.val ≤ limits.MAX_MODULE_BYTES.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    ∃ target : U32, CompilerStable initial after ∧ after.frames.val = [] ∧
      StructuredCode emit types functions returns locals after.function.code.val jumpTables
        [functionRootLabel returns after.function target] [] current.source 0 target.val returns ∧
      (∃ src count, src.val = slots locals ∧ after.function.code.val[target.val]? = some (.Return src count)) ∧
      after.function.code.val.length = target.val + 1 ∧
      after.function.code.val.length ≤ U32.max := by
  have beforeBound := (Nat.le_of_lt consumed).trans sourceBound
  have fetchBound := invariant.codeBudget.fetch_bound beforeBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionEq : target.val = before.function.code.val.length := by simp [target]
  obtain ⟨frame, frames, bodyKind, noGuard, height, width, mapBound, branches, body⟩ :=
    invariant.root_relation entered stack target positionEq form front params results
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities beforeBound
  have emitCoordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    omega
  have call : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty = .ok (.Ok (), after) := accepted
  have effect := structured_close_function_body ops law before state frame (alloc.vec.Vec.new _) target
    (by simpa using frames) bodyKind noGuard positionEq branches mapBound coordinate codeFits sourceFits emitCoordinate
    types functions returns locals current.source width body
  rw [call, WP.spec_ok] at effect
  have result := effect rfl
  dsimp only at result
  obtain ⟨popped, relation, returnedCode, endpoint⟩ := result
  obtain ⟨count, returned⟩ := returnedCode
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by omega
  have bound := (invariant.codeBudget.advance growth consumed).fetch_bound sourceBound
  exact ⟨target, invariant.metadata.trans stable, by simp [popped], relation,
    ⟨frame.height, count, height, returned⟩, endpoint, Nat.le_of_lt bound⟩
end Itasca.Runtime.Compiler

end

end
