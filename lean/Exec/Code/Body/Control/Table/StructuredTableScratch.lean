import Exec.Code.Body.Control.Table.StructuredCompilerPrefixWithTables
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Collecting table labels changes only private scratch and allocation
accounting; it preserves the complete source/code invariant. -/
theorem StructuredCompilerPrefixWithTables.table_scratch {A : Type}
    {initial before : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals parents current raw position)
    (budget : runtime.compiler.Budget A) (depths : alloc.vec.Vec U32) :
    StructuredCompilerPrefixWithTables jumpTables emit initial {before with budget,table_depths := depths}
      types functions returns locals parents current raw position := by
  refine ⟨⟨invariant.metadata.metadata,invariant.metadata.capacity⟩,?_,invariant.entryChain,invariant.dormant,
    invariant.conditions,invariant.known,?_,invariant.arms,invariant.sources,invariant.codeBudget,
    ⟨invariant.controlBudget.maps,invariant.controlBudget.frames⟩,invariant.cursor⟩
  · refine ⟨invariant.frames.nested,?_⟩
    exact invariant.frames.frames.imp (fun _ _ frame =>
      ⟨frame.toScopeFrameShape,frame.mapBound,frame.entryBound,frame.bodyBound,frame.entryCode⟩)
  · cases invariant.mode with
    | live reachable entered retained =>
      exact .live reachable entered ⟨retained.localsEq,
        ⟨retained.layout.localSlots,retained.layout.localOffsets,retained.layout.operandOffsets,
          retained.layout.height,retained.layout.capacity⟩,retained.sites,retained.prefixes⟩
    | terminal reachable entered retained =>
      exact .terminal reachable entered ⟨retained.localsEq,retained.sites,retained.prefixes⟩
    | dormant reachable retained =>
      exact .dormant reachable ⟨retained.unentered,retained.localsEq,retained.sites,retained.prefixes⟩
end Exec.Code
