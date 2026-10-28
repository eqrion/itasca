import Exec.Store.Api.TableMemoryBindings
import Exec.Store.Initialization.InitializerMetadata

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem InitializerFunctionMetadata.table_bindings {M : Type}
    {before after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata before inst after next)
    (bindings : TableBindings before inst.module.module.env.table_types.val inst.tables.val) :
    TableBindings after next.module.module.env.table_types.val next.tables.val := by
  rw [metadata.source, metadata.tableMap]
  exact TableBindings.prefix bindings metadata.identity (by simp [metadata.tables])

theorem InitializerFunctionMetadata.memory_bindings {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata before inst after next)
    (bindings : MemoryBindings view before inst.module.module.env.mem_types.val inst.memories.val) :
    MemoryBindings view after next.module.module.env.mem_types.val next.memories.val := by
  rw [metadata.source, metadata.memoryMap]
  exact MemoryBindings.prefix bindings metadata.identity (by simp [metadata.memories])

end Itasca.Runtime.Store
