import Exec.Store.Invariant.CompiledDefinitions

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Concrete code-address metadata produced by preparation and staging. The
provisional witness differs only in the committed resource counter, allowing
old code retention to use exact precharge vector prefixes. This contains no
assumption about execution of the installed functions. -/
def InstantiationCode {M : Type} (before ready : runtime.store.Store M)
    (inst : runtime.store.Instance) : Prop :=
  ∃ staged count, ready = {staged with instance_items := count} ∧
    StagedPrefix before staged ∧
    TypeEntries staged inst.module.module.env.types.val inst.types.val ∧
    Interp.FunctionTable staged inst (inst.module.module.env.func_types.val.map decodeFuncType) ∧
    StagedFunctionSignatures before staged before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)

theorem InstantiationCode.identity {M : Type} {before ready : runtime.store.Store M}
    {inst : runtime.store.Instance} (code : InstantiationCode before ready inst) : ready.id = before.id := by
  obtain ⟨staged, count, rfl, retained, _, _, _⟩ := code
  exact retained.identity

theorem InstantiationCode.type_entries {M : Type} {before ready : runtime.store.Store M}
    {inst : runtime.store.Instance} (code : InstantiationCode before ready inst) :
    TypeEntries ready inst.module.module.env.types.val inst.types.val := by
  obtain ⟨staged, count, rfl, _, entries, _, _⟩ := code
  exact entries

theorem InstantiationCode.function_table {M : Type} {before ready : runtime.store.Store M}
    {inst : runtime.store.Instance} (code : InstantiationCode before ready inst) :
    Interp.FunctionTable ready inst (inst.module.module.env.func_types.val.map decodeFuncType) := by
  obtain ⟨staged, count, rfl, _, _, table, _⟩ := code
  exact table

/-- The compiler's syntactic module certificate supplies fresh function bodies;
existing bodies keep their old certificate. Charging instance items changes no
field involved in code interpretation or function lookup. -/
theorem InstantiationCode.compiled {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.Instance}
    (code : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (shape : Shape view before) (oldCompiled : Interp.CompiledFunctions oldCode before)
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (sources : List funccode) (certificate : Code.ModuleFunctions inst.module sources)
    {tables memories} (cache : Cache inst.module.module.env tables memories) :
    Interp.CompiledFunctions (installCode oldCode before.instances.len.val sources) ready := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := code
  have compiled := compiled_functions_publish before staged oldCode shape retained oldCompiled inst sources
    found certificate cache entries table signatures
  exact compiled

end Exec.Store
