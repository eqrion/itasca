import Exec.Code.Body.Reader.Table.StructuredReaderCompilerStateWithTables
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A running compiler point keeps a single exact source zipper existentially,
while fixing the source body, signature, local layout and actual machine state. -/
def StructuredReaderCompilerPointWithTablesWasm1 (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bodyBt : code.BlockType)
    (st : code.OpIterState) : Prop :=
  ∃ parents current savedParents savedCurrent,
    StructuredReaderCompilerStateWithTablesWasm1 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent

def StructuredReaderCompilerPointWithTablesWasm2 (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec Itasca.types.ValueType)
    (index : U32) (ft : Itasca.types.FuncType) (st : code.BodyState) : Prop :=
  ∃ parents current savedParents savedCurrent,
    StructuredReaderCompilerStateWithTablesWasm2 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent

theorem StructuredReaderCompilerStateWithTablesWasm1.point {jumpTables : List U32} {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm1 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent) :
    StructuredReaderCompilerPointWithTablesWasm1 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env ctx bodyBt st :=
  ⟨parents, current, savedParents, savedCurrent, state⟩

theorem StructuredReaderCompilerStateWithTablesWasm2.point {jumpTables : List U32} {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm2 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent) :
    StructuredReaderCompilerPointWithTablesWasm2 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st :=
  ⟨parents, current, savedParents, savedCurrent, state⟩
end Exec.Code
