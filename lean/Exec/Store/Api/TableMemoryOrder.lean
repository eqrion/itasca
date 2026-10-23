import Exec.Store.Preparation.AllocationTableMemory
import Exec.Store.Invariant.AddressOrder
namespace Exec.Store
open Aeneas Aeneas.Std

theorem TableStageEffect.address_order {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} {start initial}
    (effect : TableStageEffect store inst ty out)
    (ordered : AddressOrder start initial store.tables.length (inst.tables.val.map fun address => address.index.val)) :
    AddressOrder start initial out.2.1.tables.length (out.2.2.tables.val.map fun address => address.index.val) := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, stored, mapped, limits, capacity, counter, budget, rfl⟩
  · exact ordered
  · simpa [stored, mapped] using ordered.append

theorem MemoryStageEffect.address_order {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} {start initial}
    (effect : MemoryStageEffect view store inst ty out)
    (ordered : AddressOrder start initial store.memories.length (inst.memories.val.map fun address => address.index.val)) :
    AddressOrder start initial out.2.1.memories.length (out.2.2.memories.val.map fun address => address.index.val) := by
  rcases effect with ⟨error, rfl⟩ | ⟨memories, buffer, addresses, count, zeros, stored, mapped, limits, capacity, counter, budget, rfl⟩
  · exact ordered
  · simpa [stored, mapped] using ordered.append
end Exec.Store
