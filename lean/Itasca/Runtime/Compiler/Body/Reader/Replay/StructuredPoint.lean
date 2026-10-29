import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredState

/-!
The structured source/compiler point extracted from a reader state.

Main declarations: `StructuredReaderCompilerPointWasm2`. A direct consumer is `Compiler.Body.Reader.Control.ElseCompilation`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

def StructuredReaderCompilerPointWasm2 (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec Itasca.types.ValueType)
    (index : U32) (ft : Itasca.types.FuncType) (st : code.BodyState) : Prop :=
  ∃ parents current savedParents savedCurrent,
    StructuredReaderCompilerStateWasm2 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent

theorem StructuredReaderCompilerStateWasm2.point {jumpTables : List U32} {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent) :
    StructuredReaderCompilerPointWasm2 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st :=
  ⟨parents, current, savedParents, savedCurrent, state⟩
end Itasca.Runtime.Code
