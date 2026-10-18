import Exec.Store.Api.MemoryAllocationCauses
import Exec.Store.Api.TableAllocationCauses
namespace Exec.Store
open Aeneas Aeneas.Std

/-- The table budget counter is the sum of independently decoded source
reference-vector lengths, not a compiled storage estimate. -/
theorem Shape.decoded_table_elements {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (shape : Shape view store) (code : CodeInterpretation) :
    ((decodeStore view code store).TABLES.map fun table => table.REFS.length).sum = store.table_elements.val := by
  simp [decodeStore,decodeTable,List.map_map,Function.comp_def,shape.tableAccounting]

/-- The memory budget counter is exactly the decoded source byte total. -/
theorem Shape.decoded_memory_bytes {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (shape : Shape view store) (code : CodeInterpretation) :
    ((decodeStore view code store).MEMS.map fun memory => memory.BYTES.length).sum = store.memory_bytes.val := by
  simp [decodeStore,decodeMemory,decodeBytes,List.map_map,Function.comp_def,shape.memoryAccounting]

/-- Store object accounting includes source objects plus the retained canonical
signature and external-identity pools, which have no separate SpecTec vectors. -/
theorem decoded_object_count {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) :
    (decodeStore view code store).FUNCS.length + (decodeStore view code store).TABLES.length +
      (decodeStore view code store).MEMS.length + (decodeStore view code store).GLOBALS.length +
      store.externs.length + (store.types.val.map decodeFuncType).length = objectCount store := by
  simp [decodeStore,objectCount]

/-- A table allocation quota failure is a source-size inequality; allocator
refusals retain their exact concrete vector and request. -/
theorem TableAllocationCause.source_allocation {M A : Type} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {ty : Itasca.types.TableType}
    (view : M → Slice U8) (code : CodeInterpretation) (shape : Shape view store)
    (cause : TableAllocationCause allocator store ty .Allocation) :
    store.limits.max_table_elements.val <
        ((decodeStore view code store).TABLES.map fun table => table.REFS.length).sum + ty.limits.min.val ∨
      allocator.reserve (alloc.vec.Vec.new U64) (UScalar.cast .Usize ty.limits.min) =
        .ok (false,alloc.vec.Vec.new U64) ∨
      allocator.reserve store.tables 1#usize = .ok (false,store.tables) := by
  rwa [shape.decoded_table_elements code]

/-- Memory allocation budgets likewise refer to source bytes and the declared
initial page count. -/
theorem MemoryAllocationCause.source_allocation {M A : Type} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {ty : Itasca.types.MemType}
    (view : M → Slice U8) (code : CodeInterpretation) (shape : Shape view store)
    (cause : MemoryAllocationCause allocator store ty .Allocation) :
    store.limits.max_memory_bytes.val <
        ((decodeStore view code store).MEMS.map fun memory => memory.BYTES.length).sum + ty.limits.min.val * 65536 ∨
      allocator.reserve store.memories 1#usize = .ok (false,store.memories) := by
  rwa [shape.decoded_memory_bytes code]
end Exec.Store
