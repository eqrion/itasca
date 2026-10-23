import Exec.Store.Invariant.Typing
import Exec.Store.Initialization.Data
import Exec.Store.Initialization.SegmentEffects
import Exec.Store.Initialization.BulkPreservation
namespace Exec.Store
open Aeneas Aeneas.Std

theorem SegmentBounds.same {M : Type} {before after : runtime.store.Store M}
    (bounded : SegmentBounds before) (elements : after.elems = before.elems) (datas : after.datas = before.datas) :
    SegmentBounds after := by
  constructor
  · simpa [elements] using bounded.elements
  · simpa [datas] using bounded.data

theorem SegmentBounds.element_drop {M : Type} (store : runtime.store.Store M)
    (bounded : SegmentBounds store) (address : Usize) (segment : runtime.store.ElemInst) :
    SegmentBounds {store with elems := store.elems.set address {segment with refs := alloc.vec.Vec.new U64}} := by
  constructor
  · intro element member
    simp only [alloc.vec.Vec.set_val_eq] at member
    have oldOrNew := List.mem_or_eq_of_mem_set member
    rcases oldOrNew with old | rfl
    · exact bounded.elements element old
    · simp
  · exact bounded.data

theorem SegmentBounds.data_drop {M : Type} (store : runtime.store.Store M)
    (bounded : SegmentBounds store) (address : Usize) (segment : runtime.store.DataInst) :
    SegmentBounds {store with datas := store.datas.set address {segment with bytes := alloc.vec.Vec.new U8}} := by
  constructor
  · exact bounded.elements
  · intro data member
    simp only [alloc.vec.Vec.set_val_eq] at member
    have oldOrNew := List.mem_or_eq_of_mem_set member
    rcases oldOrNew with old | rfl
    · exact bounded.data data old
    · simp

theorem TableInitializationEffect.bounds {M : Type} {store : runtime.store.Store M}
    {index table segment destination source count out}
    (effect : TableInitializationEffect store index table segment destination source count out)
    (bounded : SegmentBounds store) : SegmentBounds out.2 := by
  unfold TableInitializationEffect at effect
  split at effect
  · obtain ⟨words, rfl, _⟩ := effect
    exact bounded.same rfl rfl
  · rw [effect]; exact bounded

theorem MemoryInitializationEffect.bounds {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {index memory segment destination source count out}
    (effect : MemoryInitializationEffect view store index memory segment destination source count out)
    (bounded : SegmentBounds store) : SegmentBounds out.2 := by
  unfold MemoryInitializationEffect at effect
  split at effect
  · obtain ⟨buffer, rfl, _⟩ := effect
    exact bounded.same rfl rfl
  · rw [effect]; exact bounded

/-- Data staging copies the accepted source payload exactly, hence cannot grow
it beyond its binary vector count. Allocation refusal leaves all bounds intact. -/
theorem add_instance_data_bounds {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instIndex index : Usize) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bound : index.val < inst.module.module.tail.data.val.length)
    (room : store.datas.length < Usize.max) (mapRoom : inst.datas.length < Usize.max)
    (sourceBound : ∀ data ∈ inst.module.module.tail.data.val, data.init.length < 2^32)
    (bounded : SegmentBounds store) :
    runtime.store.instantiate.Store.add_instance_data memory allocator store instIndex index
      ⦃ out => SegmentBounds out.2 ⦄ := by
  have instanceBound : instIndex.val < store.instances.length := (List.getElem?_eq_some_iff.mp found).1
  have instanceRead : store.instances.val[instIndex.val] = inst := (List.getElem?_eq_some_iff.mp found).2
  apply WP.spec_mono (add_instance_data_effect memory allocator law store instIndex index instanceBound
    (by simpa only [instanceRead] using bound) room (by simpa only [instanceRead] using mapRoom))
  intro out effect
  rcases effect with ⟨error, rfl⟩ | ⟨bytes, datas, addresses, copied, appended, mapped, rfl⟩
  · exact bounded
  · constructor
    · exact bounded.elements
    · intro data member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact bounded.data data old
      · have source := sourceBound _ (List.getElem_mem bound)
        simpa only [alloc.vec.Vec.length, copied, instanceRead] using source
end Exec.Store
