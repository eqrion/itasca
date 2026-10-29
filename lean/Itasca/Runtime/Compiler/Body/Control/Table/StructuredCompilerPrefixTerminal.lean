import Itasca.Runtime.Compiler.Body.Control.Table.StructuredPrefixDead
namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
