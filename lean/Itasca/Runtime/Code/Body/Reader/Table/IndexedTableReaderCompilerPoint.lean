import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderCompilerPoint
import Itasca.Runtime.Code.Local.Callbacks.Table.CompilerTableBoundary
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

structure IndexedTableReaderCompilerPointWasm2
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : Itasca.module.Env) (sourceLocals : alloc.vec.Vec Itasca.types.ValueType)
    (index : U32) (ft : Itasca.types.FuncType) (st : Itasca.code.BodyState) : Prop where
  tables : CompilerTableBoundary compiler
  future : ∀ more, StructuredReaderCompilerPointWasm2
    ((CompilerTables.ofFunction compiler.function).append more).jumpTables
    (emit ((CompilerTables.ofFunction compiler.function).append more))
    initial compiler types functions returns locals data env sourceLocals index ft st

theorem IndexedTableReaderCompilerPointWasm2.append_step {A : Type}
    {emit initial before after types functions returns locals data env sourceLocals index ft st out}
    (point : @IndexedTableReaderCompilerPointWasm2 emit A initial before types functions returns locals data env sourceLocals index ft st)
    (extra : CompilerTables)
    (tables : CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra)
    (boundary : CompilerTableBoundary after)
    (step : ∀ future, StructuredReaderCompilerPointWasm2
      ((CompilerTables.ofFunction after.function).append future).jumpTables
      (emit ((CompilerTables.ofFunction after.function).append future))
      initial before types functions returns locals data env sourceLocals index ft st →
      StructuredReaderCompilerPointWasm2
        ((CompilerTables.ofFunction after.function).append future).jumpTables
        (emit ((CompilerTables.ofFunction after.function).append future))
        initial after types functions returns locals data env sourceLocals index ft out) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env sourceLocals index ft out := by
  refine ⟨boundary, ?_⟩
  intro future
  apply step future
  simpa only [tables,CompilerTables.append_assoc] using point.future (extra.append future)
end Itasca.Runtime.Code
