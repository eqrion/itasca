import Exec.Store.Api.TableCopyEffect
import Exec.Spec.TableCopySnapshot
import Exec.Store.Api.TableInitSemantics
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

theorem table_copy_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (targetIndex sourceIndex : U32) (address sourceAddress : runtime.TableAddr)
    (table sourceTable : runtime.store.Table) (destination source count : Nat) (words : alloc.vec.Vec U64)
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

theorem TableCopyEffect.refines {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (targetIndex sourceIndex : U32) (address sourceAddress : runtime.TableAddr)
    (table sourceTable : runtime.store.Table) (destination source count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : TableCopyEffect store address.index table sourceTable destination source count out)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[targetIndex.val]? = some address)
    (sourceMapped : inst.tables.val[sourceIndex.val]? = some sourceAddress)
    (target : store.tables.val[address.index.val]? = some table)
    (sourceFound : store.tables.val[sourceAddress.index.val]? = some sourceTable)
    (sameType : sourceTable.ty=table.ty)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (dstBound : destination.val < 2^32) (srcBound : source.val < 2^32) (countBound : count.val < 2^32) :
    StepsH ⟨⟨decodeStore view code store,ambient⟩,Spec.Segment.operands destination.val source.val count.val ++
      [.TABLE_COPY (.mk_uN targetIndex.val) (.mk_uN sourceIndex.val)]⟩ []
      ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ := by
  have targetRead : fun_table ⟨decodeStore view code store,ambient⟩ (.mk_uN targetIndex.val) = decodeTable table := by
    simp [fun_table,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,target]
  have sourceRead : fun_table ⟨decodeStore view code store,ambient⟩ (.mk_uN sourceIndex.val) = decodeTable sourceTable := by
    simp [fun_table,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,sourceMapped,sourceFound]
  have wf := decodeStore_wf view code store shape sourceSyntax
  unfold TableCopyEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨words,rfl,copied⟩ := effect
    simp only [segmentResult]
    rw [table_copy_decodes view code store inst ambient targetIndex sourceIndex address sourceAddress table sourceTable
      destination.val source.val count.val words moduleEq mapped sourceMapped target sourceFound sameType ⟨inside.2,inside.1⟩ copied]
    apply Spec.Segment.table_copy_steps _ _ _ _ _ _ _ wf ambientWf dstBound srcBound countBound (by scalar_tac) (by scalar_tac)
    · simpa [moduleEq,decodeInstance] using (List.getElem?_eq_some_iff.mp mapped).1
    · simpa [moduleEq,decodeInstance,decodeStore,List.getElem!_eq_getElem?_getD,mapped] using (List.getElem?_eq_some_iff.mp target).1
    · simpa [moduleEq,decodeInstance,decodeStore,List.getElem!_eq_getElem?_getD,sourceMapped] using (List.getElem?_eq_some_iff.mp sourceFound).1
    · constructor
      · simp only [targetRead,decodeTable,List.length_map]
        have h := (shape.tables table (List.mem_of_getElem? target)).1
        simp only [alloc.vec.Vec.length] at h
        scalar_tac
      · simp only [sourceRead,decodeTable,List.length_map]
        have h := (shape.tables sourceTable (List.mem_of_getElem? sourceFound)).1
        simp only [alloc.vec.Vec.length] at h
        scalar_tac
    · simpa [targetRead,sourceRead,decodeTable] using And.intro inside.2 inside.1
  · rename_i outside
    rw [effect]
    apply Spec.stepsH_single
    apply Spec.Segment.table_copy_trap _ _ _ _ _ _ _ wf ambientWf dstBound srcBound countBound (by scalar_tac) (by scalar_tac)
    simp only [targetRead,sourceRead,decodeTable,List.length_map]
    simp only [alloc.vec.Vec.length] at outside
    omega
end Exec.Store
