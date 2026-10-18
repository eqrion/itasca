import Exec.Code.Body.Reader.Common.ReaderCompilerState
import Exec.Code.Body.Reader.Common.ReaderBoundaryInitial
import Exec.Code.Body.Callbacks.Common.CompilerPrefixStart
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Successful compiler startup can be paired with the exact fresh canonical
validator root, establishing the full state carried by the body fold. -/
theorem ReaderCompilerStateWasm1.initial {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) (types functions : List functype)
    (locals : List valtype) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (compiled : CompilerPrefix compiler compiler types functions (Control.resultTypes bt) locals
      [] (SourceScope.initial (Control.resultTypes bt)) [] 0) :
    ReaderCompilerStateWasm1 compiler compiler types functions (Control.resultTypes bt) locals data env ctx bt
      (Wasm1.Loop.initial bt) [] (SourceScope.initial (Control.resultTypes bt)) []
      (Wasm1.Frames.Saved.fresh (Wasm1.Loop.initial bt) .body bt) := by
  refine ⟨compiled, .initial data env ctx bt size, .initial bt _, ?_, .initial _⟩
  exact ReaderReachability.initial _ _ _ _ rfl

theorem ReaderCompilerStateWasm2.initial {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) (types functions : List functype)
    (locals : List valtype) (data : Slice U8) (env : module.Env)
    (sourceLocals : alloc.vec.Vec Itasca.types.ValueType) (index : U32) (ft : Itasca.types.FuncType)
    (signature : env.types.val[index.val]? = some ft) (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (compiled : CompilerPrefix compiler compiler types functions (ft.results.val.map Translate.valueType) locals
      [] (SourceScope.initial (ft.results.val.map Translate.valueType)) [] 0) :
    ReaderCompilerStateWasm2 compiler compiler types functions (ft.results.val.map Translate.valueType) locals
      data env sourceLocals index ft (Wasm2.initial index) []
      (SourceScope.initial (ft.results.val.map Translate.valueType)) []
      (Wasm2.Frames.Saved.fresh 0#usize .body (.TypeIndex index) ft.params.val ft.results.val) := by
  refine ⟨compiled, .initial data env sourceLocals index ft signature size,
    .initial (.TypeIndex index) 0#usize ft.params.val ft.results.val, ?_, .initial _⟩
  exact ReaderReachability.initial _ _ _ _ rfl

end Exec.Code
