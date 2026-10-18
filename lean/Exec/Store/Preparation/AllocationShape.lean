import Exec.Store.Invariant.FunctionStaging
import Exec.Store.Api.MemoryStaging
import Exec.Store.Api.TableStaging

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Allocated values and resource counters during instantiation. Function/module
links and instance-item accounting are completed after the provisional instance
has received its maps; no execution property is included here. -/
structure AllocationShape {M : Type} (view : M → Slice U8) (store : runtime.store.Store M) : Prop where
  identity : 0 < store.id.val
  memories : ∀ memory ∈ store.memories.val, MemoryShape view memory
  tables : ∀ table ∈ store.tables.val, TableShape store table
  globals : ∀ global ∈ store.globals.val, GlobalShape store global
  elements : ∀ element ∈ store.elems.val, ∀ word ∈ element.refs.val, ReferenceShape store element.ty word
  canonicalTypes : (store.types.val.map decodeFuncType).Nodup
  objectLimit : objectCount store ≤ store.limits.max_objects.val
  signatureAccounting : store.signature_values.val = (store.types.val.map fun ty => ty.params.length + ty.results.length).sum
  signatureLimit : store.signature_values.val ≤ store.limits.max_signature_values.val
  memoryAccounting : store.memory_bytes.val = (store.memories.val.map fun memory => (view memory.buf).length).sum
  memoryLimit : store.memory_bytes.val ≤ store.limits.max_memory_bytes.val
  tableAccounting : store.table_elements.val = (store.tables.val.map fun table => table.elements.length).sum
  tableLimit : store.table_elements.val ≤ store.limits.max_table_elements.val

theorem Shape.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : Shape view store) : AllocationShape view store :=
  ⟨shape.identity, shape.memories, shape.tables, shape.globals, shape.elements,
    shape.canonicalTypes, shape.object_count_bound, shape.signatureAccounting, shape.signatureLimit,
    shape.memoryAccounting, shape.memoryLimit, shape.tableAccounting, shape.tableLimit⟩

theorem AllocationShape.replace_instances {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : AllocationShape view store) (instances : alloc.vec.Vec runtime.store.Instance) :
    AllocationShape view {store with instances} := by
  cases shape
  constructor <;> assumption

theorem AllocationShape.charge_instance_items {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : AllocationShape view store) (count : Usize) :
    AllocationShape view {store with instance_items := count} := by
  cases shape
  constructor <;> assumption

/-- Canonical type interning extends only its charged signature vector. -/
theorem InternEffect.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {ty result} (effect : InternEffect store ty result) (shape : AllocationShape view store) :
    AllocationShape view result.2 := by
  rcases effect with ⟨error, rfl⟩ | ⟨index, found, rfl⟩ |
    ⟨types, count, appended, fresh, room, counted, limited, rfl⟩
  · exact shape
  · exact shape
  · constructor
    · exact shape.identity
    · exact shape.memories
    · simpa only [TableShape, ReferenceShape] using shape.tables
    · simpa only [GlobalShape, ReferenceShape] using shape.globals
    · simpa only [ReferenceShape] using shape.elements
    · simp [appended, List.nodup_append, shape.canonicalTypes]
      intro existing member equal
      have same := decodeFuncType_injective equal
      subst existing
      exact fresh member
    · simp only [objectCount, alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
      unfold objectCount at room
      simp only [alloc.vec.Vec.length] at room
      omega
    · simp [appended, counted, shape.signatureAccounting, Nat.add_assoc]
    · exact limited
    · exact shape.memoryAccounting
    · exact shape.memoryLimit
    · exact shape.tableAccounting
    · exact shape.tableLimit

theorem TypeStageEffect.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst ty out} (effect : TypeStageEffect store inst ty out) (shape : AllocationShape view store) :
    AllocationShape view out.2.1 := by
  rcases effect with ⟨error, rfl⟩ | ⟨index, addresses, interned, mapped, success, next⟩
  · exact shape
  · exact interned.allocated shape

/-- A newly allocated function may name the provisional instance, while all
pre-existing references remain valid under the extended function vector. -/
theorem FunctionStageEffect.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst instanceIndex index signature out} (effect : FunctionStageEffect store inst instanceIndex index signature out)
    (shape : AllocationShape view store) : AllocationShape view out.2.1 := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, appended, mapped, room, rfl⟩
  · exact shape
  · have grown : store.funcs.length ≤ functions.length := by simp [appended]
    constructor
    · exact shape.identity
    · exact shape.memories
    · intro table member
      exact TableShape.mono store _ grown (by simp) table (shape.tables table member)
    · intro global member
      exact GlobalShape.mono store _ grown (by simp) global (shape.globals global member)
    · intro element member word contained
      exact ReferenceShape.mono store _ grown (by simp) _ _ (shape.elements element member word contained)
    · exact shape.canonicalTypes
    · simp only [objectCount, alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
      unfold objectCount at room
      simp only [alloc.vec.Vec.length] at room
      omega
    · exact shape.signatureAccounting
    · exact shape.signatureLimit
    · exact shape.memoryAccounting
    · exact shape.memoryLimit
    · exact shape.tableAccounting
    · exact shape.tableLimit

end Exec.Store
