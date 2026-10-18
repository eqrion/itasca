import Exec.Code.Local.Relations.Common.Function
import Itasca.Support.EnvTranslation
namespace Exec.Code
open Aeneas.Std

/-- A defined function's source syntax and complete retained code certificate
use the module's actual type/function metadata. Synthetic helpers are excluded. -/
def DefinedFunctionCode (env : Itasca.module.Env) (typeIndex : U32)
    (source : funccode) (compiled : runtime.bytecode.CompiledFunction) : Prop :=
  compiled.type_index = typeIndex ∧
    ∃ signature declared body epilogue,
      env.types.val[typeIndex.val]? = some signature ∧
      source = .FUNC (.mk_uN typeIndex.val) (declared.map local.LOCAL) body ∧
      FunctionCode (env.types.val.map Itasca.EnvTranslation.funcType)
        (env.func_types.val.map Itasca.EnvTranslation.funcType)
        (signature.params.val.map Itasca.Translate.valueType) declared
        (signature.results.val.map Itasca.Translate.valueType) body compiled epilogue

/-- The defined prefix of an executable module corresponds index-for-index to
source function declarations. The appended initializer functions have separate
certificates and do not enlarge the source function index space. -/
structure ModuleFunctions (module : runtime.compiler.ExecutableModule)
    (sources : List funccode) : Prop where
  count : sources.length = module.module.env.func_type_indices.val.length
  entry : ∀ (index : Nat) (typeIndex : U32),
    module.module.env.func_type_indices.val[index]? = some typeIndex →
      ∃ compiled source, module.functions.val[index]? = some compiled ∧
        sources[index]? = some source ∧ DefinedFunctionCode module.module.env typeIndex source compiled

/-- Appending synthetic code preserves every defined-function certificate. -/
theorem ModuleFunctions.extend {before after : runtime.compiler.ExecutableModule} {sources}
    (certificate : ModuleFunctions before sources)
    (source : after.module = before.module)
    (preserved : after.functions.val.take before.functions.val.length = before.functions.val) :
    ModuleFunctions after sources := by
  refine ⟨by simpa only [source] using certificate.count, ?_⟩
  intro index typeIndex found
  obtain ⟨compiled, src, foundCode, sourceLookup, code⟩ := certificate.entry index typeIndex (by simpa only [source] using found)
  refine ⟨compiled, src, ?_, sourceLookup, by simpa only [source] using code⟩
  have bound := (List.getElem?_eq_some_iff.mp foundCode).1
  have same := (List.getElem?_eq_some_iff.mp foundCode).2
  have retained := congrArg (fun list => list[index]?) preserved
  simpa [List.getElem?_take, bound, same] using retained
end Exec.Code
