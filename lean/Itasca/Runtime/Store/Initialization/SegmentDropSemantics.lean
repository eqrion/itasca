import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Spec.SegmentDrops
import Itasca.Runtime.Store.Initialization.BulkPreservation
import Itasca.Runtime.Store.Invariant.SourceSyntax

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem data_drop_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : Usize) (old : runtime.store.DataInst)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.datas.val[index.val]? = some address)
    (found : store.datas.val[address.val]? = some old) :
    decodeStore view code {store with datas := store.datas.set address ⟨alloc.vec.Vec.new U8⟩} =
      Spec.droppedDataStore (decodeStore view code store) ambient index.val := by
  have read : ambient.MODULE.DATAS[index.val]! = address.val := by
    rw [moduleEq]
    simp only [decodeInstance, List.getElem!_eq_getElem?_getD, List.getElem?_map, mapped, Option.map_some, Option.getD_some]
  have lists := Itasca.Runtime.Representation.map_set_modify decodeData (fun data => {data with BYTES := []}) store.datas.val address.val old
    ⟨alloc.vec.Vec.new U8⟩ found rfl
  unfold Spec.droppedDataStore
  rw [read]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq, lists]
  rfl

theorem element_drop_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : Usize) (old : runtime.store.ElemInst)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.elems.val[index.val]? = some address)
    (found : store.elems.val[address.val]? = some old) :
    decodeStore view code {store with elems := store.elems.set address {old with refs := alloc.vec.Vec.new U64}} =
      Spec.droppedElementStore (decodeStore view code store) ambient index.val := by
  have read : ambient.MODULE.ELEMS[index.val]! = address.val := by
    rw [moduleEq]
    simp only [decodeInstance, List.getElem!_eq_getElem?_getD, List.getElem?_map, mapped, Option.map_some, Option.getD_some]
  have lists := Itasca.Runtime.Representation.map_set_modify decodeElement (fun element => {element with REFS := []}) store.elems.val address.val old
    {old with refs := alloc.vec.Vec.new U64} found rfl
  unfold Spec.droppedElementStore
  rw [read]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq, lists]
  rfl

theorem data_drop_refines {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : Usize) (old : runtime.store.DataInst)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.datas.val[index.val]? = some address)
    (found : store.datas.val[address.val]? = some old) :
    StepH ⟨⟨decodeStore view code store,ambient⟩,[.DATA_DROP (.mk_uN index.val)]⟩ []
      ⟨⟨decodeStore view code {store with datas := store.datas.set address ⟨alloc.vec.Vec.new U8⟩},ambient⟩,[]⟩ := by
  rw [data_drop_decodes view code store inst ambient index address old moduleEq mapped found]
  apply Spec.data_drop_step _ _ _ (decodeStore_wf view code store shape sourceSyntax) ambientWf (by scalar_tac)
  · have bound := (List.getElem?_eq_some_iff.mp mapped).1
    simpa [moduleEq, decodeInstance] using bound
  · rw [← data_drop_decodes view code store inst ambient index address old moduleEq mapped found]
    exact decodeStore_wf view code _ (shape.data_drop address) (sourceSyntax.instances_eq rfl)

theorem element_drop_refines {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : Usize) (old : runtime.store.ElemInst)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.elems.val[index.val]? = some address)
    (found : store.elems.val[address.val]? = some old) :
    StepH ⟨⟨decodeStore view code store,ambient⟩,[.ELEM_DROP (.mk_uN index.val)]⟩ []
      ⟨⟨decodeStore view code {store with elems := store.elems.set address {old with refs := alloc.vec.Vec.new U64}},ambient⟩,[]⟩ := by
  rw [element_drop_decodes view code store inst ambient index address old moduleEq mapped found]
  apply Spec.element_drop_step _ _ _ (decodeStore_wf view code store shape sourceSyntax) ambientWf (by scalar_tac)
  · have bound := (List.getElem?_eq_some_iff.mp mapped).1
    simpa [moduleEq, decodeInstance] using bound
  · rw [← element_drop_decodes view code store inst ambient index address old moduleEq mapped found]
    exact decodeStore_wf view code _ (shape.element_drop address old) (sourceSyntax.instances_eq rfl)

end Itasca.Runtime.Store
