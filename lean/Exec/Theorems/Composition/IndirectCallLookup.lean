import Exec.Interp.State.StatefulLookup
import Exec.Interp.State.TableSource
import Exec.Representation.StoreInvariant

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

/-- Canonical source type bindings reconstruct the actual instance signature
index and its checked store lookup. -/
theorem signature_binding_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context)
    (shape : Store.Shape view store) (present : inst ∈ store.instances.val)
    (bindings : Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (index : Nat) (type : functype) (selected : C.TYPES[index]? = some type) :
    ∃ signature rawType, inst.types.val[index]? = some signature ∧
      store.types.val[signature.val]? = some rawType ∧ Store.decodeFuncType rawType = type := by
  rw [bindings.types] at selected
  change (inst.types.val.map (fun i => (store.types.val.map Store.decodeFuncType).getD i.val default))[index]? = some type at selected
  rw [List.getElem?_map] at selected
  obtain ⟨signature,mapped,decoded⟩ := Option.map_eq_some_iff.mp selected
  obtain ⟨_,_,_,_,_,_,_,typeBounds,_⟩ := shape.instances inst present
  have bound := typeBounds signature (List.mem_of_getElem? mapped)
  have found : store.types.val[signature.val]? = some store.types.val[signature.val] := List.getElem?_eq_getElem bound
  refine ⟨signature,store.types.val[signature.val],mapped,found,?_⟩
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_map,found,Option.map_some,Option.getD_some] using decoded

/-- The runtime type map and the generated `fun_type` select the same signature. -/
theorem signature_lookup_decodes {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (signature : Usize) (type : Itasca.types.FuncType)
    (moduleEq : ambient.MODULE = Store.decodeInstance store inst)
    (mapped : inst.types.val[index.val]? = some signature)
    (found : store.types.val[signature.val]? = some type) :
    fun_type ⟨Store.decodeStore view code store,ambient⟩ (.mk_uN index.val) = Store.decodeFuncType type := by
  simp [fun_type,moduleEq,Store.decodeInstance,proj_uN_0,List.getElem!_eq_getElem?_getD,
    List.getD_eq_getElem?_getD,mapped,found]

/-- Both independent namespaces of CALL_INDIRECT resolve to actual retained
objects, with exact source lookup equations. -/
theorem indirect_bindings_raw {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame) (C : context)
    (shape : Store.Shape view store) (present : inst ∈ store.instances.val)
    (bindings : Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C)
    (moduleEq : ambient.MODULE = Store.decodeInstance store inst)
    (typeIndex tableIndex : U32) (type : functype) (limits : limits)
    (typeSelected : C.TYPES[typeIndex.val]? = some type)
    (tableSelected : C.TABLES[tableIndex.val]? = some (.mk_tabletype limits .FUNCREF)) :
    ∃ signature rawType address object,
      inst.types.val[typeIndex.val]? = some signature ∧
      store.types.val[signature.val]? = some rawType ∧ Store.decodeFuncType rawType = type ∧
      inst.tables.val[tableIndex.val]? = some address ∧
      store.tables.val[address.index.val]? = some object ∧ object.ty = .FuncRef ∧
      fun_type ⟨Store.decodeStore view code store,ambient⟩ (.mk_uN typeIndex.val) = type ∧
      fun_table ⟨Store.decodeStore view code store,ambient⟩ (.mk_uN tableIndex.val) = Store.decodeTable object := by
  obtain ⟨signature,rawType,typeMapped,typeFound,typeEq⟩ :=
    signature_binding_raw view code store inst C shape present bindings typeIndex.val type typeSelected
  obtain ⟨address,object,tableMapped,tableFound,elementType⟩ :=
    Stateful.table_binding_raw view code store inst C tableIndex.val _ bindings tableSelected
  have rawFuncref : object.ty = .FuncRef := by
    cases h : object.ty <;> simp [h,Store.decodeElemType,Abs.Stateful.tableElementType] at elementType ⊢
  exact ⟨signature,rawType,address,object,typeMapped,typeFound,typeEq,tableMapped,tableFound,rawFuncref,
    (signature_lookup_decodes view code store inst ambient typeIndex signature rawType moduleEq typeMapped typeFound).trans typeEq,
    table_lookup_decodes view code store inst ambient tableIndex address object moduleEq tableMapped tableFound⟩

end Exec.Interp
