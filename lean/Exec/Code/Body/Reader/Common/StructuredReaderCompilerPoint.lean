import Exec.Code.Body.Reader.Common.StructuredReaderCompilerState
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A running compiler point keeps a single exact source zipper existentially,
while fixing the source body, signature, local layout and actual machine state. -/
def StructuredReaderCompilerPointWasm1 (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bodyBt : code.BlockType)
    (st : code.OpIterState) : Prop :=
  ∃ parents current savedParents savedCurrent,
    StructuredReaderCompilerStateWasm1 emit initial compiler types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent

def StructuredReaderCompilerPointWasm2 (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec Itasca.types.ValueType)
    (index : U32) (ft : Itasca.types.FuncType) (st : code.BodyState) : Prop :=
  ∃ parents current savedParents savedCurrent,
    StructuredReaderCompilerStateWasm2 emit initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent

theorem StructuredReaderCompilerStateWasm1.point {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm1 emit initial compiler types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent) :
    StructuredReaderCompilerPointWasm1 emit initial compiler types functions returns locals data env ctx bodyBt st :=
  ⟨parents, current, savedParents, savedCurrent, state⟩

theorem StructuredReaderCompilerStateWasm2.point {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 emit initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent) :
    StructuredReaderCompilerPointWasm2 emit initial compiler types functions returns locals data env sourceLocals index ft st :=
  ⟨parents, current, savedParents, savedCurrent, state⟩
end Exec.Code
