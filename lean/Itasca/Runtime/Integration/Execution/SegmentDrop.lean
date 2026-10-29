import Itasca.Runtime.Store.Initialization.SegmentDrop
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.SourceMachine.Stateful.Transition
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem stateful_data_drop_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (index : U32) (address : Usize)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.datas.val[index.val]? = some address) (issued : address.val < store.datas.length)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.DataDrop index) ⦃ out =>
      out = (.Ok (),{store with datas := store.datas.set address ⟨alloc.vec.Vec.new U8⟩}) ∧
      FrameStoreMetadata store out.2 ∧
      SourceMachine.Stateful.Transition state f rest after (.dataDrop index.val)
        (SourceMachine.advance {state with store := decodeStore view code out.2} {f with code := after} rest) ⦄ := by
  apply WP.spec_mono (bulk_data_drop memory store instIndex function base slots inst index address found mapped issued)
  rintro out rfl
  refine ⟨rfl,⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
  have actual := data_drop_decodes view code store inst f.toFrame index address store.datas.val[address.val]
    moduleEq mapped (List.getElem?_eq_getElem issued)
  rw [actual]
  simp [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.dataDrop,moduleEq,sourceStore,decodeInstance,decodeStore,
    List.getElem?_map,mapped,List.getElem?_eq_getElem issued]

theorem stateful_element_drop_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (index : U32) (address : Usize)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.elems.val[index.val]? = some address) (issued : address.val < store.elems.length)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.ElemDrop index) ⦃ out =>
      out = (.Ok (),{store with elems := store.elems.set address {store.elems.val[address.val] with refs := alloc.vec.Vec.new U64}}) ∧
      FrameStoreMetadata store out.2 ∧
      SourceMachine.Stateful.Transition state f rest after (.elemDrop index.val)
        (SourceMachine.advance {state with store := decodeStore view code out.2} {f with code := after} rest) ⦄ := by
  apply WP.spec_mono (bulk_element_drop memory store instIndex function base slots inst index address found mapped issued)
  rintro out rfl
  refine ⟨rfl,⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
  have actual := element_drop_decodes view code store inst f.toFrame index address store.elems.val[address.val]
    moduleEq mapped (List.getElem?_eq_getElem issued)
  rw [actual]
  simp [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.elementDrop,moduleEq,sourceStore,decodeInstance,decodeStore,
    List.getElem?_map,mapped,List.getElem?_eq_getElem issued]
end Itasca.Runtime.Integration
