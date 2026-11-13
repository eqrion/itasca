import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrameStart
import Itasca.Runtime.Compiler.Local.Source.SourceEntry

/-!
Sections, each formerly its own module: CompilerPrefix, CompilerPrefixInitial, CompilerPrefixStart.
-/

/-! ## CompilerPrefix -/

section

/-!
Reachability selects a retained executable prefix, a terminal prefix, or an unentered subtree. No continuation is assumed for an omitted subtree.

Main declarations: `PrefixMode` and `CompilerPrefix`. A direct consumer is `Compiler.Body.Callbacks.Prefix.CompilerPrefixInitial`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## CompilerPrefixInitial -/

section

/-!
The root scope starts with an empty concrete operand stack and a live empty source prefix. All budgets and alignment are physical compiler facts.

Main declarations: `CompilerPrefix.initial`. A direct consumer is `Compiler.Body.Callbacks.Prefix.CompilerPrefixStart`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The root scope starts with an empty concrete operand stack and a live
empty source prefix. All budgets and alignment are physical compiler facts. -/
theorem CompilerPrefix.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (frames : ScopeFrameStack locals compiler [] (SourceScope.initial returns))
    (retained : UniversalPrefix compiler types functions returns locals [] (SourceScope.initial returns) [])
    (arms : UniversalElse compiler types functions returns locals [] (SourceScope.initial returns))
    (sources : SourceAligned compiler) (codeBudget : SourceCodeBudget compiler 0)
    (controlBudget : SourceControlBudget compiler 0) (cursor : compiler.next_source.val = 0)
    (reachable : compiler.reachable = true) :
    CompilerPrefix compiler compiler types functions returns locals [] (SourceScope.initial returns) [] 0 := by
  refine ⟨.refl _, frames, .root _ rfl, frames.dormant_initial rfl, ScopeConditions.initial, ?_, .live reachable rfl retained, arms, sources, codeBudget, controlBudget, ?_⟩
  · simp [ConcreteStack]
  · omega

end Itasca.Runtime.Compiler

end

/-! ## CompilerPrefixStart -/

section

/-!
Actual construction and successful function-start establish every component of the compiler prefix invariant, before the first source opcode is read.

Main declarations: `compiler_function_start_prefix`. A direct consumer is `Compiler.Body.Relations.Entry.EntryCompilerInitial`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual construction and successful function-start establish every component
of the compiler prefix invariant, before the first source opcode is read. -/
theorem compiler_function_start_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize) (types functions : List functype) (returns : List valtype)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (resultWidth : signature.result_slots.val = slots returns)
    (beginFits : batchStart.val + bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val + bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (), started)) :
    CompilerPrefix started started types functions returns (ctx.locals.val.map Itasca.Translate.valueType)
      [] (SourceScope.initial returns) [] 0 := by
  obtain ⟨frame, frames, shape, retained, arms, codeBudget, controlBudget, stack, live⟩ :=
    compiler_function_start_scope ops law signatures functionSlots budget batchStart initial started ctx
      typeIndex signature bodyBegin bodyEnd types functions returns lookup resultWidth beginFits endFits created accepted
  have sourceFrame := compiler_function_start_source_frame ops law initial started ctx typeIndex bodyBegin bodyEnd
    (.Ok ()) accepted
  have initialSources := compiler_new_sources ops signatures functionSlots budget batchStart
  rw [created, WP.spec_ok] at initialSources
  have newCursor : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart
      ⦃ out => out.next_source = 0#usize ⦄ := by
    simp [runtime.compiler.FunctionCompiler.new, WP.spec_ok]
  rw [created, WP.spec_ok] at newCursor
  exact CompilerPrefix.initial started types functions returns _ stack retained arms
    (sourceFrame.sources.aligned initialSources) codeBudget controlBudget
    (by rw [sourceFrame.cursor, newCursor]; rfl) live
end Itasca.Runtime.Compiler

end
