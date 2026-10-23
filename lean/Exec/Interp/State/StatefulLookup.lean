import Exec.Interp.State.StatefulPrepare
import Exec.Abs.Stateful.TableTyping
import Exec.Representation.Store
namespace Exec.Interp.Stateful
open Aeneas Aeneas.Std SpecExt

theorem table_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (index : Nat) (type : tabletype)
    (bindings : Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.TABLES[index]?=some type) :
    ∃ address object, inst.tables.val[index]?=some address ∧ store.tables.val[address.index.val]?=some object ∧
      Store.decodeElemType object.ty=Abs.Stateful.tableElementType type := by
  obtain ⟨sourceAddress,sourceObject,mapped,found,objectType⟩ := Abs.Stateful.table_lookup bindings selected
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  simp only [Store.decodeStore,List.getElem?_map] at found
  obtain ⟨object,rawFound,objectEq⟩ := Option.map_eq_some_iff.mp found
  refine ⟨address,object,rawMapped,by simpa only [addressEq] using rawFound,?_⟩
  rw [←objectEq] at objectType
  exact objectType

theorem memory_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (type : memtype)
    (bindings : Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.MEMS[0]?=some type) :
    ∃ address object, inst.memories.val[0]?=some address ∧ store.memories.val[address.index.val]?=some object := by
  obtain ⟨sourceAddress,sourceObject,mapped,found⟩ := bindings.memory_lookup (List.getElem?_eq_some_iff.mp selected).1
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  simp only [Store.decodeStore,List.getElem?_map] at found
  obtain ⟨object,rawFound,objectEq⟩ := Option.map_eq_some_iff.mp found
  exact ⟨address,object,rawMapped,by simpa only [addressEq] using rawFound⟩

theorem function_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context) (index : Nat) (type : functype)
    (bindings : Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (selected : C.FUNCS[index]?=some type) :
    ∃ address, inst.funcs.val[index]?=some address ∧ address.index.val<store.funcs.length := by
  have right := (List.getElem?_eq_some_iff.mp selected).1
  have left : index<(Store.decodeInstance store inst).FUNCS.length := by rw [bindings.funcs.length_eq]; exact right
  obtain ⟨sourceFunction,found,sourceType⟩ := bindings.funcs.get left right
  have mapped : (Store.decodeInstance store inst).FUNCS[index]?=some ((Store.decodeInstance store inst).FUNCS[index]) := List.getElem?_eq_getElem left
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  have issued := (List.getElem?_eq_some_iff.mp found).1
  simp only [List.get_eq_getElem,Store.decodeStore,List.length_map] at issued
  change address.index.val=(Store.decodeInstance store inst).FUNCS[index] at addressEq
  rw [←addressEq] at issued
  exact ⟨address,rawMapped,issued⟩
end Exec.Interp.Stateful
