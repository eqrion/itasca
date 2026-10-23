import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Local.Control.Table.StructuredUniversalDormant
import Exec.Code.Local.Control.Table.StructuredElseEvidence
namespace Exec.Code
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

end Exec.Code
