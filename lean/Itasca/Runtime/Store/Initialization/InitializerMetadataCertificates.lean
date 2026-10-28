import Itasca.Runtime.Store.Initialization.InitializerMetadata
import Itasca.Runtime.Store.Invariant.FunctionSignatures
import Itasca.Runtime.Code.Local.Relations.Common.Function

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

theorem InitializerFunctionMetadata.type_entries {M : Type}
    {store after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata store inst after next)
    {source : List Itasca.types.FuncType} (entries : TypeEntries store source inst.types.val) :
    TypeEntries after source next.types.val := by
  simpa only [TypeEntries, metadata.signatures, metadata.typeMap] using entries

theorem InitializerFunctionMetadata.function_table {M : Type}
    {store after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata store inst after next)
    {types : List functype} (table : Interp.FunctionTable store inst types) :
    Interp.FunctionTable after next types := by
  simpa only [Interp.FunctionTable, metadata.identity, metadata.functions,
    metadata.signatures, metadata.functionMap] using table

theorem InitializerFunctionMetadata.staged_functions {M : Type}
    {before store after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata store inst after next) {index : Usize}
    {types : List Itasca.types.FuncType} (staged : StagedFunctionSignatures before store index types) :
    StagedFunctionSignatures before after index types := by
  simpa only [StagedFunctionSignatures, metadata.functions, metadata.signatures] using staged

end Itasca.Runtime.Store
