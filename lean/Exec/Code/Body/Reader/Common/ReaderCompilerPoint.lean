import Exec.Code.Body.Reader.Common.ReaderCompilerState
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A running compiler point keeps a single exact source zipper existentially,
while fixing the source body, signature, local layout and actual machine state. -/
def ReaderCompilerPointWasm1 {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bodyBt : code.BlockType)
    (st : code.OpIterState) : Prop :=
  ∃ parents current savedParents savedCurrent,
    ReaderCompilerStateWasm1 initial compiler types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent

def ReaderCompilerPointWasm2 {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec Itasca.types.ValueType)
    (index : U32) (ft : Itasca.types.FuncType) (st : code.BodyState) : Prop :=
  ∃ parents current savedParents savedCurrent,
    ReaderCompilerStateWasm2 initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent

theorem ReaderCompilerStateWasm1.point {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial compiler types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent) :
    ReaderCompilerPointWasm1 initial compiler types functions returns locals data env ctx bodyBt st :=
  ⟨parents, current, savedParents, savedCurrent, state⟩

theorem ReaderCompilerStateWasm2.point {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm2 initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent) :
    ReaderCompilerPointWasm2 initial compiler types functions returns locals data env sourceLocals index ft st :=
  ⟨parents, current, savedParents, savedCurrent, state⟩
end Exec.Code
