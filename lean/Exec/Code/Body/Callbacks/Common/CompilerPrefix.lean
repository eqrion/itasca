import Exec.Code.Local.Callbacks.Control.ScopeConditions
import Exec.Code.Local.Relations.Common.DormantFrames
import Exec.Code.Body.Source.TypedLowering
import Exec.Code.Local.Callbacks.Common.CompilerOrdinaryMetadata
import Exec.Code.Local.Callbacks.Control.ScopeFrameStack
import Exec.Code.Local.Source.SourceControlBudget
import Exec.Code.Local.Source.SourceLengths
import Exec.Code.Local.Control.Common.UniversalDormant
import Exec.Code.Local.Callbacks.Control.ElseEvidence
import Exec.Code.Local.Control.Common.UniversalEmpty
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Reachability selects a retained executable prefix, a terminal prefix, or
an unentered subtree. No continuation is assumed for an omitted subtree. -/
inductive PrefixMode {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (stack : List valtype) : Prop where
  | live (reachable : compiler.reachable = true) (entered : current.entered = true)
      (retained : UniversalPrefix compiler types functions returns locals parents current stack)
  | terminal (reachable : compiler.reachable = false) (entered : current.entered = true)
      (retained : UniversalTerminal compiler types functions returns locals parents current)
  | dormant (reachable : compiler.reachable = false)
      (retained : UniversalDormant compiler types functions returns locals parents current)

/-- The retained compiler invariant at an actual source-reader boundary. Its
components concern source syntax, physical frames, emitted code, and byte/slot
accounting; none assumes execution correctness. -/
structure CompilerPrefix {A : Type} (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (raw : List code.StackType) (position : Nat) : Prop where
  metadata : CompilerStable initial compiler
  frames : ScopeFrameStack locals compiler parents current
  entryChain : SourceEntryChain parents current
  dormant : DormantFrames compiler.frames.val
  conditions : ScopeConditions locals parents current
  known : ConcreteStack raw
  mode : PrefixMode compiler types functions returns locals parents current (Sequence.stackTypes raw)
  arms : UniversalElse compiler types functions returns locals parents current
  sources : SourceAligned compiler
  codeBudget : SourceCodeBudget compiler position
  controlBudget : SourceControlBudget compiler position
  cursor : compiler.next_source.val ≤ position

theorem CompilerPrefix.live {A : Type} {initial before : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) :
    current.entered = true ∧
      UniversalPrefix before types functions returns locals parents current (Sequence.stackTypes raw) := by
  cases invariant.mode with
  | live _ entered retained => exact ⟨entered, retained⟩
  | terminal dead _ _ => simp [reachable] at dead
  | dormant dead _ => simp [reachable] at dead

theorem CompilerPrefix.capacities {A : Type} {initial before : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (bound : position ≤ limits.MAX_MODULE_BYTES.val) :
    before.function.code.val.length < Usize.max ∧
      before.function.source_offsets.val.length < Usize.max ∧
      before.function.controls.val.length < Usize.max ∧ before.frames.val.length < Usize.max := by
  have code := invariant.codeBudget.code_capacity bound
  have controls := invariant.controlBudget.capacities bound
  exact ⟨code, by rw [invariant.sources]; exact code, controls⟩

theorem CompilerPrefix.ordinary {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position nextRaw nextPosition instruction emitted output}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true)
    (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLowered before after nextRaw emitted output)
    (emission : LinearEmission locals (Sequence.stackTypes raw) instruction [emitted] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    CompilerPrefix initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames) [emitted]
    lowered.1.1 (by rw [ordinary.controls])).advance instruction
  have next := lowered.1.universal_advance ordinary.frames retained emission
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [lowered.1.1, List.length_append, List.length_singleton]; omega
  refine ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance instruction,
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance instruction, lowered.2.concrete,
    .live (lowered.1.2.2.2.1.trans reachable) entered ?_,
    invariant.arms.append retained.sites [emitted] instruction lowered.1.1 ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩
  simpa only [lowered.2.decoded] using next

end Exec.Code
