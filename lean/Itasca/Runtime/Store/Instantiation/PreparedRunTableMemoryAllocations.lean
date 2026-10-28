import Itasca.Runtime.Store.Instantiation.PreparedRun
import Itasca.Runtime.Store.Preparation.PreparationTableMemoryAllocations
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

/-- The retained actual preparation calls allocate the source-defined table and
memory suffixes, with exact null/zero contents and consecutive fresh addresses. -/
theorem PreparedRun.table_memory_allocations {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before)
    {tables memories} (cache : Cache module.module.env tables memories) :
    trace.prepared.tables.val.map decodeTable = before.tables.val.map decodeTable ++
      tables.map (fun ty => Spec.allocationTable (Itasca.EnvTranslation.tableType ty)) ∧
    trace.prepared.memories.val.map (decodeMemory view) = before.memories.val.map (decodeMemory view) ++
      memories.map (fun ty => Spec.allocationMemory (Itasca.EnvTranslation.memType ty)) ∧
    trace.inst.tables.val.map (fun address => address.index.val) =
      trace.seed.tables.val.map (fun address => address.index.val) ++ List.range' before.tables.length tables.length ∧
    trace.inst.memories.val.map (fun address => address.index.val) =
      trace.seed.memories.val.map (fun address => address.index.val) ++ List.range' before.memories.length memories.length ∧
    trace.prepared.tables.length = before.tables.length + tables.length ∧
    trace.prepared.memories.length = before.memories.length + memories.length := by
  exact preparation_table_memory_allocations memory allocator law view laws before trace.seed shape trace.maps
    (by simpa only [trace.source] using cache) before.instances.len trace.typed trace.functions trace.tabled trace.prepared
    trace.typeInst trace.funcInst trace.tableInst trace.inst trace.typeRun trace.functionRun trace.tableRun trace.memoryRun

/-- Table and memory allocation retain the exact function and signature
vectors and instance maps established by the preceding preparation stages. -/
theorem PreparedRun.preparation_metadata {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before)
    {tables memories} (cache : Cache module.module.env tables memories) :
    trace.prepared.funcs = trace.functions.funcs ∧ trace.prepared.types = trace.typed.types ∧
    trace.inst.funcs = trace.funcInst.funcs ∧ trace.inst.types = trace.typeInst.types ∧
    trace.inst.module = module := by
  obtain ⟨_, _, _, _, _, _, functions, types, functionMap, typeMap, source⟩ :=
    preparation_table_memory_allocations_metadata memory allocator law view laws before trace.seed shape trace.maps
      (by simpa only [trace.source] using cache) before.instances.len trace.typed trace.functions trace.tabled trace.prepared
      trace.typeInst trace.funcInst trace.tableInst trace.inst trace.typeRun trace.functionRun trace.tableRun trace.memoryRun
  exact ⟨functions, types, functionMap, typeMap, source.trans trace.source⟩
end Itasca.Runtime.Store
