import Exec.Interp.State.StatefulLookup
import Exec.Abs.Stateful.InitStore
namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt

theorem element_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (index : Nat) (type : reftype)
    (bindings : Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.ELEMS[index]?=some type) :
    ∃ address,inst.elems.val[index]?=some address ∧ address.val<store.elems.length := by
  have right := (List.getElem?_eq_some_iff.mp selected).1
  have left : index<(Store.decodeInstance store inst).ELEMS.length := by rw [bindings.elems.length_eq];exact right
  obtain ⟨object,found,typed⟩ := bindings.elems.get left right
  have mapped : (Store.decodeInstance store inst).ELEMS[index]?=some ((Store.decodeInstance store inst).ELEMS[index]) := List.getElem?_eq_getElem left
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  have issued := (List.getElem?_eq_some_iff.mp found).1
  simp only [List.get_eq_getElem,Store.decodeStore,List.length_map] at issued
  change address.val=(Store.decodeInstance store inst).ELEMS[index] at addressEq
  rw [←addressEq] at issued
  exact ⟨address,rawMapped,issued⟩

theorem data_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (index : Nat) (type : datatype)
    (bindings : Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.DATAS[index]?=some type) :
    ∃ address,inst.datas.val[index]?=some address ∧ address.val<store.datas.length := by
  have right := (List.getElem?_eq_some_iff.mp selected).1
  have left : index<(Store.decodeInstance store inst).DATAS.length := by rw [bindings.datas.length_eq];exact right
  obtain ⟨object,found,typed⟩ := bindings.datas.get left right
  have mapped : (Store.decodeInstance store inst).DATAS[index]?=some ((Store.decodeInstance store inst).DATAS[index]) := List.getElem?_eq_getElem left
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  have issued := (List.getElem?_eq_some_iff.mp found).1
  simp only [List.get_eq_getElem,Store.decodeStore,List.length_map] at issued
  change address.val=(Store.decodeInstance store inst).DATAS[index] at addressEq
  rw [←addressEq] at issued
  exact ⟨address,rawMapped,issued⟩
theorem decode_elem_type_injective {a b : Itasca.types.ElemType}
    (equal : Store.decodeElemType a=Store.decodeElemType b) : a=b := by
  cases a <;> cases b <;> simp_all [Store.decodeElemType]

theorem element_object_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (index : Nat) (type : reftype)
    (bindings : Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.ELEMS[index]?=some type) :
    ∃ address object,inst.elems.val[index]?=some address ∧ store.elems.val[address.val]?=some object ∧ Store.decodeElemType object.ty=type := by
  have right := (List.getElem?_eq_some_iff.mp selected).1
  have left : index<(Store.decodeInstance store inst).ELEMS.length := by rw [bindings.elems.length_eq];exact right
  obtain ⟨object,found,typed⟩ := bindings.elems.get left right
  have actualType := (Abs.Stateful.element_refs_typed typed).1
  have selectedEq := (List.getElem?_eq_some_iff.mp selected).2
  simp only [List.get_eq_getElem,selectedEq] at actualType
  have mapped : (Store.decodeInstance store inst).ELEMS[index]?=some ((Store.decodeInstance store inst).ELEMS[index]) := List.getElem?_eq_getElem left
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  simp only [Store.decodeStore,List.getElem?_map,List.get_eq_getElem] at found
  obtain ⟨rawObject,rawFound,objectEq⟩ := Option.map_eq_some_iff.mp found
  refine ⟨address,rawObject,rawMapped,by simpa only [addressEq,Store.decodeInstance] using rawFound,?_⟩
  rw [←objectEq] at actualType
  exact actualType
end Itasca.Runtime.Interp.Stateful
