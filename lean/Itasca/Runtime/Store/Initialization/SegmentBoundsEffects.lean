import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Store.Initialization.Data
import Itasca.Runtime.Store.Initialization.SegmentEffects
import Itasca.Runtime.Store.Initialization.BulkPreservation
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem SegmentBounds.same {M : Type} {before after : runtime.store.Store M}
    (bounded : SegmentBounds before) (elements : after.elems = before.elems) (datas : after.datas = before.datas) :
    SegmentBounds after := by
  constructor
  · simpa [elements] using bounded.elements
  · simpa [datas] using bounded.data

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
end Itasca.Runtime.Store
