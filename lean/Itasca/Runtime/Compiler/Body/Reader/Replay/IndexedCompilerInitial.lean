import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredState
import Itasca.Runtime.Compiler.Body.Reader.Control.BoundaryInitial
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixStart

/-!
Initial structured compiler state for body replay.

Main declarations: `StructuredReaderCompilerStateWasm2.initial`. A direct consumer is `Compiler.Body.Relations.Table.PreparedTableInitial`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.initial {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) (types functions : List functype)
    (locals : List valtype) (data : Slice U8) (env : metadata.Env)
    (sourceLocals : alloc.vec.Vec Itasca.wasm_types.ValueType) (index : U32) (ft : Itasca.wasm_types.FuncType)
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

end Itasca.Runtime.Compiler
