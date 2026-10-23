import Exec.Store.Api.TableCopyEffect
import Exec.Spec.TableCopySnapshot
import Exec.Store.Api.TableInitSemantics
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

theorem table_copy_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (targetIndex sourceIndex : U32) (address sourceAddress : runtime.TableAddr)
    (table sourceTable : runtime.store.TableInst) (destination source count : Nat) (words : alloc.vec.Vec U64)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[targetIndex.val]? = some address)
    (sourceMapped : inst.tables.val[sourceIndex.val]? = some sourceAddress)
    (target : store.tables.val[address.index.val]? = some table)
    (sourceFound : store.tables.val[sourceAddress.index.val]? = some sourceTable)
    (sameType : sourceTable.ty=table.ty)
    (inside : source+count ≤ sourceTable.elements.length ∧ destination+count ≤ table.elements.length)
    (copied : words.val = table.elements.val.setSlice! destination (sourceTable.elements.val.slice source (source+count))) :
    decodeStore view code {store with tables := store.tables.set address.index {table with elements := words}} =
      Spec.Segment.tableCopy (decodeStore view code store) ambient targetIndex.val sourceIndex.val destination source count := by
  have targetRead : ambient.MODULE.TABLES[targetIndex.val]! = address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
  have sourceRead : ambient.MODULE.TABLES[sourceIndex.val]! = sourceAddress.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,sourceMapped]
  have targetLookup : (decodeStore view code store).TABLES[address.index.val]! = decodeTable table := by
    simp [decodeStore,List.getElem!_eq_getElem?_getD,target]
  have sourceLookup : (decodeStore view code store).TABLES[sourceAddress.index.val]! = decodeTable sourceTable := by
    simp [decodeStore,List.getElem!_eq_getElem?_getD,sourceFound]
  have lengthEq : words.length=table.elements.length := by
    simpa only [alloc.vec.Vec.length,List.length_setSlice!] using congrArg List.length copied
  have refsEq : words.val.map (decodeRef table.ty) =
      (table.elements.val.map (decodeRef table.ty)).setSlice! destination
        ((sourceTable.elements.val.map (decodeRef sourceTable.ty)).slice source (source+count)) := by
    rw [sameType,←Spec.Segment.copyInto_eq_setSlice _ _ _ _ _ (by simpa using inside.1) (by simpa using inside.2)]
    rw [copied,←Spec.Segment.copyInto_eq_setSlice _ _ _ _ _ inside.1 inside.2]
    exact copyInto_map _ _ _ _ _ _ inside.1
  unfold Spec.Segment.tableCopy
  rw [targetRead,sourceRead,targetLookup,sourceLookup]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,List.map_set,decodeTable,lengthEq,refsEq,Spec.Segment.withRefs]
  rfl

end Exec.Store
