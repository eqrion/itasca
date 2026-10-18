import Exec.Store.Invariant.InstantiationCode
import Exec.Store.Invariant.ExecutableCompiledDefinitions
namespace Exec.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv
/-- The compiler's syntactic module certificate supplies fresh function bodies;
existing bodies keep their old certificate. Charging instance items changes no
field involved in code interpretation or function lookup. -/
theorem InstantiationCode.executable_compiled {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.Instance}
    (code : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (shape : Shape view before) (oldCompiled : Interp.StructuredMachine.CompiledFunctions Interp.Executable.emission oldCode before)
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (sources : List funccode) (certificate : Code.ExecutableModuleFunctions inst.module sources)
    (dataCount : ∀ count, inst.module.module.env.data_count = some count →
      count.val = inst.module.module.tail.data.val.length)
    {tables memories} (cache : Cache inst.module.module.env tables memories) :
    Interp.StructuredMachine.CompiledFunctions Interp.Executable.emission (installCode oldCode before.instances.len.val sources) ready := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := code
  have compiled := executable_compiled_functions_publish before staged oldCode shape retained oldCompiled inst sources
    found certificate dataCount cache entries table signatures
  exact compiled

end Exec.Store
