import Exec.Code.Local.Initializer.InitializerComplete
import Exec.Code.Body.Relations.Common.ExecutableModuleFunctions
import Exec.Code.Module.CollectFunctions
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
structure PendingExecutableModuleFunctions (env : Itasca.module.Env)
    (pending : List (Option runtime.bytecode.CompiledFunction)) (sources : List funccode) : Prop where
  count : sources.length = env.func_type_indices.val.length
  entry : ∀ (index : Nat) (typeIndex : U32), env.func_type_indices.val[index]? = some typeIndex →
    ∃ compiled source, pending[index]? = some (some compiled) ∧ sources[index]? = some source ∧
      DefinedExecutableFunctionCode env typeIndex source compiled

/-- Source-indexed compiler certificates survive actual dense collection. -/
theorem PendingExecutableModuleFunctions.collected {env pending sources}
    (certificate : PendingExecutableModuleFunctions env pending sources)
    (module : runtime.compiler.ExecutableModule) (sameEnv : module.module.env = env)
    (collected : pending = module.functions.val.map some) : ExecutableModuleFunctions module sources := by
  refine ⟨by simpa only [sameEnv] using certificate.count, ?_⟩
  intro index typeIndex found
  obtain ⟨compiled, source, codeFound, sourceFound, code⟩ := certificate.entry index typeIndex
    (by simpa only [sameEnv] using found)
  refine ⟨compiled, source, ?_, sourceFound, by simpa only [sameEnv] using code⟩
  rw [collected, List.getElem?_map] at codeFound
  cases actual : module.functions.val[index]? <;> simp_all
end Itasca.Runtime.Code
