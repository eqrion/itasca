import Exec.Code.Local.Relations.Common.Function
import Itasca.Support.EnvTranslation
import Exec.Code.Local.Lowering.Float.FloatCoreFunction
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
structure FloatCoreModuleFunctions (module : runtime.compiler.ExecutableModule)
    (sources : List funccode) : Prop where
  count : sources.length = module.module.env.func_type_indices.val.length
  entry : ∀ (index : Nat) (typeIndex : U32),
    module.module.env.func_type_indices.val[index]? = some typeIndex →
      ∃ compiled source, module.functions.val[index]? = some compiled ∧
        sources[index]? = some source ∧ DefinedFloatCoreFunctionCode module.module.env typeIndex source compiled

/-- Appending synthetic code preserves every defined-function certificate. -/
theorem FloatCoreModuleFunctions.extend {before after : runtime.compiler.ExecutableModule} {sources}
    (certificate : FloatCoreModuleFunctions before sources)
    (source : after.module = before.module)
    (preserved : after.functions.val.take before.functions.val.length = before.functions.val) :
    FloatCoreModuleFunctions after sources := by
  refine ⟨by simpa only [source] using certificate.count, ?_⟩
  intro index typeIndex found
  obtain ⟨compiled, src, foundCode, sourceLookup, code⟩ := certificate.entry index typeIndex (by simpa only [source] using found)
  refine ⟨compiled, src, ?_, sourceLookup, by simpa only [source] using code⟩
  have bound := (List.getElem?_eq_some_iff.mp foundCode).1
  have same := (List.getElem?_eq_some_iff.mp foundCode).2
  have retained := congrArg (fun list => list[index]?) preserved
  simpa [List.getElem?_take, bound, same] using retained
end Exec.Code
