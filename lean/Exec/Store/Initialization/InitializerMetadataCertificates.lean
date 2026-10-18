import Exec.Store.Initialization.InitializerMetadata
import Exec.Store.Invariant.CompiledDefinitions

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

theorem InitializerFunctionMetadata.type_entries {M : Type}
    {store after : runtime.store.Store M} {inst next : runtime.store.Instance}
    (metadata : InitializerFunctionMetadata store inst after next)
    {source : List Itasca.types.FuncType} (entries : TypeEntries store source inst.types.val) :
    TypeEntries after source next.types.val := by
  simpa only [TypeEntries, metadata.signatures, metadata.typeMap] using entries

theorem InitializerFunctionMetadata.function_table {M : Type}
    {store after : runtime.store.Store M} {inst next : runtime.store.Instance}
    (metadata : InitializerFunctionMetadata store inst after next)
    {types : List functype} (table : Interp.FunctionTable store inst types) :
    Interp.FunctionTable after next types := by
  simpa only [Interp.FunctionTable, metadata.identity, metadata.functions,
    metadata.signatures, metadata.functionMap] using table

theorem InitializerFunctionMetadata.staged_functions {M : Type}
    {before store after : runtime.store.Store M} {inst next : runtime.store.Instance}
    (metadata : InitializerFunctionMetadata store inst after next) {index : Usize}
    {types : List Itasca.types.FuncType} (staged : StagedFunctionSignatures before store index types) :
    StagedFunctionSignatures before after index types := by
  simpa only [StagedFunctionSignatures, metadata.functions, metadata.signatures] using staged

/-- Complete initializer staging retains the preparation certificates needed
for every defined function. The metadata premise is established by the actual
global/element/data loops, rather than assuming their semantic correctness. -/
theorem compiled_functions_after_initializers {M : Type} {view : M → Slice U8}
    (before prepared after : runtime.store.Store M) (oldCode : CodeInterpretation)
    (shape : Shape view before) (retained : StagedPrefix before after)
    (oldCompiled : Interp.CompiledFunctions oldCode before)
    (seed inst : runtime.store.Instance) (sources : List funccode)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    (metadata : InitializerFunctionMetadata prepared seed after inst)
    (certificate : Code.ModuleFunctions seed.module sources)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (entries : TypeEntries prepared seed.module.module.env.types.val seed.types.val)
    (table : Interp.FunctionTable prepared seed (seed.module.module.env.func_types.val.map decodeFuncType))
    (staged : StagedFunctionSignatures before prepared before.instances.len
      (seed.module.module.env.func_types.val.drop (importedFuncs seed.module.module.env.imports.val).length)) :
    Interp.CompiledFunctions (installCode oldCode before.instances.len.val sources) after := by
  apply compiled_functions_publish before after oldCode shape retained oldCompiled inst sources found
  · simpa only [metadata.source] using certificate
  · simpa only [metadata.source] using cache
  · simpa only [metadata.source] using metadata.type_entries entries
  · simpa only [metadata.source] using metadata.function_table table
  · simpa only [metadata.source] using metadata.staged_functions staged

end Exec.Store
