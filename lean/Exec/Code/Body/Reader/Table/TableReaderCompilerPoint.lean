import Exec.Code.Local.Callbacks.Table.CompilerTables
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerPoint
namespace Exec.Code
open Aeneas Aeneas.Std

/-- The existing structured point, instantiated for every future extension of
all function-local tables. This supports pair, SIMD-immediate, constant, and jump-table
appends without changing the structural compiler relation. -/
def TableReaderCompilerPointWasm1
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : Itasca.module.Env) (ctx : Itasca.code.Context) (bodyBt : Itasca.code.BlockType)
    (st : Itasca.code.OpIterState) : Prop :=
  ∀ future, StructuredReaderCompilerPointWasm1
    (emit ((CompilerTables.ofFunction compiler.function).append future))
    initial compiler types functions returns locals data env ctx bodyBt st

def TableReaderCompilerPointWasm2
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : Itasca.module.Env) (sourceLocals : alloc.vec.Vec Itasca.types.ValueType)
    (index : U32) (ft : Itasca.types.FuncType) (st : Itasca.code.BodyState) : Prop :=
  ∀ future, StructuredReaderCompilerPointWasm2
    (emit ((CompilerTables.ofFunction compiler.function).append future))
    initial compiler types functions returns locals data env sourceLocals index ft st

theorem TableReaderCompilerPointWasm1.append_step {A : Type}
    {emit initial before after types functions returns locals data env ctx bodyBt st out}
    (point : @TableReaderCompilerPointWasm1 emit A initial before types functions returns locals data env ctx bodyBt st)
    (extra : CompilerTables)
    (tables : CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra)
    (step : ∀ future, StructuredReaderCompilerPointWasm1 (emit ((CompilerTables.ofFunction after.function).append future))
      initial before types functions returns locals data env ctx bodyBt st →
      StructuredReaderCompilerPointWasm1 (emit ((CompilerTables.ofFunction after.function).append future))
      initial after types functions returns locals data env ctx bodyBt out) :
    TableReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  intro future
  apply step future
  simpa only [tables,CompilerTables.append_assoc] using point (extra.append future)

theorem TableReaderCompilerPointWasm2.append_step {A : Type}
    {emit initial before after types functions returns locals data env sourceLocals index ft st out}
    (point : @TableReaderCompilerPointWasm2 emit A initial before types functions returns locals data env sourceLocals index ft st)
    (extra : CompilerTables)
    (tables : CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra)
    (step : ∀ future, StructuredReaderCompilerPointWasm2 (emit ((CompilerTables.ofFunction after.function).append future))
      initial before types functions returns locals data env sourceLocals index ft st →
      StructuredReaderCompilerPointWasm2 (emit ((CompilerTables.ofFunction after.function).append future))
      initial after types functions returns locals data env sourceLocals index ft out) :
    TableReaderCompilerPointWasm2 emit initial after types functions returns locals data env sourceLocals index ft out := by
  intro future
  apply step future
  simpa only [tables,CompilerTables.append_assoc] using point (extra.append future)
end Exec.Code
