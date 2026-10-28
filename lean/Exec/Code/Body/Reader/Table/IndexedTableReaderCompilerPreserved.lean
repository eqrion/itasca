import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPoint
namespace Itasca.Runtime.Code
open Aeneas.Std

theorem IndexedTableReaderCompilerPointWasm2.preserved_step {A : Type}
    {emit initial before after types functions returns locals data env sourceLocals index ft st out}
    (point : @IndexedTableReaderCompilerPointWasm2 emit A initial before types functions returns locals data env sourceLocals index ft st)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (depths : after.table_depths = before.table_depths)
    (growth : before.function.code.val.length ≤ after.function.code.val.length)
    (step : ∀ future, StructuredReaderCompilerPointWasm2 ((CompilerTables.ofFunction before.function).append future).jumpTables (emit ((CompilerTables.ofFunction before.function).append future))
      initial before types functions returns locals data env sourceLocals index ft st →
      StructuredReaderCompilerPointWasm2 ((CompilerTables.ofFunction before.function).append future).jumpTables (emit ((CompilerTables.ofFunction before.function).append future))
      initial after types functions returns locals data env sourceLocals index ft out) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env sourceLocals index ft out := by
  refine ⟨⟨by simpa only [depths] using point.tables.depths, ?_⟩, ?_⟩
  · have targets := congrArg CompilerTables.jumpTables tables
    change after.function.jump_tables.val = before.function.jump_tables.val at targets
    simpa only [targets] using point.tables.targets.trans growth
  · intro future
    simpa only [tables] using step future (point.future future)
end Itasca.Runtime.Code
