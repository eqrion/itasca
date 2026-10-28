import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderCompilerState
import Itasca.Runtime.Code.Body.Reader.Common.ReaderBoundaryInitial
import Itasca.Runtime.Code.Body.Control.Table.StructuredCompilerPrefixStart
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.initial {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) (types functions : List functype)
    (locals : List valtype) (data : Slice U8) (env : module.Env)
    (sourceLocals : alloc.vec.Vec Itasca.types.ValueType) (index : U32) (ft : Itasca.types.FuncType)
    (signature : env.types.val[index.val]? = some ft) (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (compiled : StructuredCompilerPrefix jumpTables emit compiler compiler types functions (ft.results.val.map Translate.valueType) locals
      [] (SourceScope.initial (ft.results.val.map Translate.valueType)) [] 0) :
    StructuredReaderCompilerStateWasm2 jumpTables emit compiler compiler types functions (ft.results.val.map Translate.valueType) locals
      data env sourceLocals index ft (Wasm2.initial index) []
      (SourceScope.initial (ft.results.val.map Translate.valueType)) []
      (Wasm2.Frames.Saved.fresh 0#usize .body (.TypeIndex index) ft.params.val ft.results.val) := by
  refine ⟨compiled, .initial data env sourceLocals index ft signature size,
    .initial (.TypeIndex index) 0#usize ft.params.val ft.results.val, ?_, .initial _, .initial _⟩
  exact ReaderReachability.initial _ _ _ _ rfl

end Itasca.Runtime.Code
