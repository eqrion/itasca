import Itasca.Runtime.Representation.StoreInvariant

/-! Every stored element/data segment is retained by one instance map. This
reachable-store invariant supplies allocation bounds not implied by Shape
alone, which permits unreferenced raw segment entries. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

structure SegmentAccounting {M : Type} (store : runtime.store.Store M) : Prop where
  elements : store.elems.length = (store.instances.val.map fun inst => inst.elems.length).sum
  datas : store.datas.length = (store.instances.val.map fun inst => inst.datas.length).sum

theorem SegmentAccounting.element_bound {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (accounted : SegmentAccounting store) (shape : Shape view store) :
    store.elems.length ≤ store.instance_items.val := by
  rw [accounted.elements, shape.instanceAccounting]
  suffices ∀ values : List runtime.store.ModuleInst,
      (values.map fun inst => inst.elems.length).sum ≤ (values.map instanceItems).sum by exact this _
  intro values
  induction values with
  | nil => simp
  | cons head tail ih => simp only [List.map_cons, List.sum_cons]; unfold instanceItems at *; omega

theorem SegmentAccounting.data_bound {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (accounted : SegmentAccounting store) (shape : Shape view store) :
    store.datas.length ≤ store.instance_items.val := by
  rw [accounted.datas, shape.instanceAccounting]
  suffices ∀ values : List runtime.store.ModuleInst,
      (values.map fun inst => inst.datas.length).sum ≤ (values.map instanceItems).sum by exact this _
  intro values
  induction values with
  | nil => simp
  | cons head tail ih => simp only [List.map_cons, List.sum_cons]; unfold instanceItems at *; omega

/-- Public non-instantiation operations preserve segment accounting whenever
they leave the segment vectors and instance maps unchanged. -/
theorem SegmentAccounting.preserve {M : Type} {before after : runtime.store.Store M}
    (accounted : SegmentAccounting before) (elements : after.elems = before.elems)
    (datas : after.datas = before.datas) (instances : after.instances = before.instances) :
    SegmentAccounting after := by
  constructor
  · simpa only [elements, instances] using accounted.elements
  · simpa only [datas, instances] using accounted.datas

/-- An exact per-instance segment-map update accounts for the corresponding
append to each store segment vector. -/
theorem SegmentAccounting.update_instance {M : Type} {before after : runtime.store.Store M}
    (accounted : SegmentAccounting before) (index : Usize) (old next : runtime.store.ModuleInst)
    (found : before.instances.val[index.val]? = some old)
    (instances : after.instances = before.instances.set index next)
    (elementCount dataCount : Nat)
    (elements : after.elems.length = before.elems.length + elementCount)
    (datas : after.datas.length = before.datas.length + dataCount)
    (elementMap : next.elems.length = old.elems.length + elementCount)
    (dataMap : next.datas.length = old.datas.length + dataCount) : SegmentAccounting after := by
  have bound : index.val < before.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
  have read : before.instances.val[index.val] = old :=
    Option.some.inj ((List.getElem?_eq_getElem bound).symm.trans found)
  constructor
  · rw [elements, accounted.elements, instances, alloc.vec.Vec.set_val_eq, List.map_set, elementMap]
    have effect := sum_set_add (before.instances.val.map fun inst => inst.elems.length) index.val elementCount
      (by simpa using bound)
    simpa only [List.getElem_map, read] using effect.symm
  · rw [datas, accounted.datas, instances, alloc.vec.Vec.set_val_eq, List.map_set, dataMap]
    have effect := sum_set_add (before.instances.val.map fun inst => inst.datas.length) index.val dataCount
      (by simpa using bound)
    simpa only [List.getElem_map, read] using effect.symm

/-- Publishing a new instance with its segment vectors preserves exact segment
accounting, including the empty-map instance staged before initialization. -/
theorem SegmentAccounting.append_instance {M : Type} {before after : runtime.store.Store M}
    (accounted : SegmentAccounting before) (inst : runtime.store.ModuleInst)
    (instances : after.instances.val = before.instances.val ++ [inst])
    (elements : after.elems.length = before.elems.length + inst.elems.length)
    (datas : after.datas.length = before.datas.length + inst.datas.length) : SegmentAccounting after := by
  constructor
  · simp [elements, instances, accounted.elements]
  · simp [datas, instances, accounted.datas]

end Itasca.Runtime.Store
