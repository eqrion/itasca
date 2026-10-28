import Itasca.Runtime.Representation.FunctionCapacity
import Itasca.Runtime.Code.Body.Capacity.CapacityFoldWasm2
import Itasca.Runtime.Code.Body.Relations.Common.EntryCompilerInitial
import Itasca.Runtime.Code.Local.Callbacks.Common.Finish
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Source-indexed frame bounds retained for the defined function prefix. -/
structure ModuleCapacities (module : runtime.compiler.ExecutableModule)
    (sources : List funccode) : Prop where
  count : sources.length = module.module.env.func_type_indices.val.length
  entry : ∀ (index : Nat) (typeIndex : U32),
    module.module.env.func_type_indices.val[index]? = some typeIndex →
      ∃ compiled source, module.functions.val[index]? = some compiled ∧
        sources[index]? = some source ∧
        FunctionCapacity module.profile module.module.env typeIndex source compiled

theorem ModuleCapacities.extend {before after : runtime.compiler.ExecutableModule} {sources}
    (certificate : ModuleCapacities before sources)
    (source : after.module = before.module) (profile : after.profile = before.profile)
    (preserved : after.functions.val.take before.functions.val.length = before.functions.val) :
    ModuleCapacities after sources := by
  refine ⟨by simpa only [source] using certificate.count, ?_⟩
  intro index typeIndex found
  obtain ⟨compiled, src, foundCode, sourceLookup, code⟩ := certificate.entry index typeIndex
    (by simpa only [source] using found)
  refine ⟨compiled, src, ?_, sourceLookup, by simpa only [source, profile] using code⟩
  have bound := (List.getElem?_eq_some_iff.mp foundCode).1
  have same := (List.getElem?_eq_some_iff.mp foundCode).2
  have retained := congrArg (fun list => list[index]?) preserved
  simpa [List.getElem?_take, bound, same] using retained
end Itasca.Runtime.Code
