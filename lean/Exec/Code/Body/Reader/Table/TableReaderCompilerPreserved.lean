import Exec.Code.Body.Reader.Table.TableReaderCompilerPoint
namespace Exec.Code
open Aeneas.Std

theorem TableReaderCompilerPointWasm1.preserved_step {A : Type}
    {emit initial before after types functions returns locals data env ctx bodyBt st out}
    (point : @TableReaderCompilerPointWasm1 emit A initial before types functions returns locals data env ctx bodyBt st)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (step : ∀ future, StructuredReaderCompilerPointWasm1 (emit ((CompilerTables.ofFunction before.function).append future))
      initial before types functions returns locals data env ctx bodyBt st →
      StructuredReaderCompilerPointWasm1 (emit ((CompilerTables.ofFunction before.function).append future))
      initial after types functions returns locals data env ctx bodyBt out) :
    TableReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  intro future
  simpa only [tables] using step future (point future)

theorem TableReaderCompilerPointWasm2.preserved_step {A : Type}
    {emit initial before after types functions returns locals data env sourceLocals index ft st out}
    (point : @TableReaderCompilerPointWasm2 emit A initial before types functions returns locals data env sourceLocals index ft st)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (step : ∀ future, StructuredReaderCompilerPointWasm2 (emit ((CompilerTables.ofFunction before.function).append future))
      initial before types functions returns locals data env sourceLocals index ft st →
      StructuredReaderCompilerPointWasm2 (emit ((CompilerTables.ofFunction before.function).append future))
      initial after types functions returns locals data env sourceLocals index ft out) :
    TableReaderCompilerPointWasm2 emit initial after types functions returns locals data env sourceLocals index ft out := by
  intro future
  simpa only [tables] using step future (point future)
end Exec.Code
