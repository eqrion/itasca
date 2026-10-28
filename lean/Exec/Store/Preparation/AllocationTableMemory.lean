import Exec.Store.Api.TableStaging
import Exec.Store.Api.MemoryStaging
import Exec.Store.Invariant.BindingTyping
import Exec.Spec.Allocation
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

theorem decode_table_allocation (ty : types.TableType) (elements : alloc.vec.Vec U64)
    (zeros : elements.val = List.replicate ty.limits.min.val 0#u64) :
    decodeTable {elements, ty := ty.elem, maximum := ty.limits.max} =
      Spec.allocationTable (EnvTranslation.tableType ty) := by
  simp [decodeTable, alloc.vec.Vec.length, zeros, List.length_replicate, List.map_replicate,
    decodeRef, ↓reduceIte, decodeElemType_source,
    Spec.allocationTable, EnvTranslation.tableType, EnvTranslation.limitsType, decodeLimits]

theorem decode_memory_allocation {M : Type} (view : M → Slice U8) (ty : types.MemType) (buffer : M)
    (zeros : (view buffer).val = List.replicate (ty.limits.min.val * 65536) 0#u8) :
    decodeMemory view {buf := buffer, maximum := ty.limits.max} =
      Spec.allocationMemory (EnvTranslation.memType ty) := by
  simp only [decodeMemory, Slice.length, zeros, List.length_replicate, decodeBytes,
    List.map_replicate, Spec.allocationMemory, EnvTranslation.memType,
    EnvTranslation.limitsType, decodeLimits]
  norm_num [Ki]

theorem TableStageEffect.decoded {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out}
    (effect : TableStageEffect store inst ty out) (success : out.1 = .Ok ()) :
    out.2.1.tables.val.map decodeTable = store.tables.val.map decodeTable ++
      [Spec.allocationTable (EnvTranslation.tableType ty)] := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · cases success
  · simp only [appended, List.map_append, List.map_singleton, decode_table_allocation ty elements zeros]

theorem MemoryStageEffect.decoded {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out}
    (effect : MemoryStageEffect view store inst ty out) (success : out.1 = .Ok ()) :
    out.2.1.memories.val.map (decodeMemory view) = store.memories.val.map (decodeMemory view) ++
      [Spec.allocationMemory (EnvTranslation.memType ty)] := by
  rcases effect with ⟨error, rfl⟩ | ⟨memories, buffer, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · cases success
  · simp only [appended, List.map_append, List.map_singleton, decode_memory_allocation view ty buffer zeros]
end Itasca.Runtime.Store

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The decoded suffix allocated so far corresponds exactly to a source slice. -/
def AllocationPrefix {T U : Type} (allocate : T → U) (source : List T)
    (start : Nat) (original actual : List U) (position : Nat) : Prop :=
  actual = original ++ ((source.take position).drop start).map allocate

theorem AllocationPrefix.initial {T U : Type} (allocate : T → U) (source : List T)
    (start : Nat) (original : List U) : AllocationPrefix allocate source start original original start := by
  simp [AllocationPrefix]

theorem AllocationPrefix.append {T U : Type} {allocate : T → U} {source : List T}
    {start position : Nat} {original actual : List U}
    (hprefix : AllocationPrefix allocate source start original actual position)
    (prior : start ≤ position) (bound : position < source.length) :
    AllocationPrefix allocate source start original (actual ++ [allocate source[position]]) (position + 1) := by
  unfold AllocationPrefix at *
  rw [List.take_succ_eq_append_getElem bound, List.drop_append_of_le_length (by simp; omega), List.map_append]
  simpa [hprefix, List.append_assoc]

theorem AllocationPrefix.complete {T U : Type} {allocate : T → U} {source : List T}
    {start : Nat} {original actual : List U}
    (hprefix : AllocationPrefix allocate source start original actual source.length) :
    actual = original ++ (source.drop start).map allocate := by
  simpa [AllocationPrefix] using hprefix
end Itasca.Runtime.Store
