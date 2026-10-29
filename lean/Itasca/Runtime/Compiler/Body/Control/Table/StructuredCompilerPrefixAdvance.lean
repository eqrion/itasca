import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalCall
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalEmpty
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
