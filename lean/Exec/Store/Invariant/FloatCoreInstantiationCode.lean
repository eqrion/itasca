import Exec.Store.Invariant.InstantiationCode
import Exec.Store.Invariant.FloatCoreCompiledDefinitions
namespace Exec.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv
/-- The compiler's syntactic module certificate supplies fresh function bodies;
existing bodies keep their old certificate. Charging instance items changes no
field involved in code interpretation or function lookup. -/
theorem InstantiationCode.float_core_compiled {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (code : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (shape : Shape view before) (oldCompiled : Interp.FloatCoreCompiledFunctions oldCode before)
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (sources : List funccode) (certificate : Code.FloatCoreModuleFunctions inst.module sources)
    {tables memories} (cache : Cache inst.module.module.env tables memories) :
    Interp.FloatCoreCompiledFunctions (installCode oldCode before.instances.len.val sources) ready := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := code
  have compiled := float_core_compiled_functions_publish before staged oldCode shape retained oldCompiled inst sources
    found certificate cache entries table signatures
  exact compiled

end Exec.Store
