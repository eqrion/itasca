import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Spec.TableInitAlgebra
import Itasca.Runtime.Store.Api.TableInitLists
import Itasca.Runtime.Store.Invariant.Syntax
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Store.Initialization.BulkPreservation

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem table_init_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (tableIndex elementIndex : U32) (tableAddress : runtime.TableAddr) (elementAddress : Usize)
    (table : runtime.store.TableInst) (segment : runtime.store.ElemInst)
    (destination source count : Nat) (words : alloc.vec.Vec U64)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (tableMapped : inst.tables.val[tableIndex.val]? = some tableAddress)
    (elementMapped : inst.elems.val[elementIndex.val]? = some elementAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (resolved : store.elems.val[elementAddress.val]? = some segment)
    (sameType : table.ty = segment.ty)
    (inside : source+count ≤ segment.refs.length)
    (copied : words.val = copySegment table.elements.val segment.refs.val destination source count) :
    decodeStore view code {store with tables := store.tables.set tableAddress.index {table with elements := words}} =
      Spec.Segment.tableInit (decodeStore view code store) ambient tableIndex.val elementIndex.val destination source count := by
  have tableRead : ambient.MODULE.TABLES[tableIndex.val]! = tableAddress.index.val := by
    rw [moduleEq]
    simp [decodeInstance,List.getElem!_eq_getElem?_getD,tableMapped]
  have elementRead : fun_elem ⟨decodeStore view code store,ambient⟩ (.mk_uN elementIndex.val) = decodeElement segment := by
    simp [fun_elem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,elementMapped,resolved]
  have lengthEq : words.length = table.elements.length := by
    simpa only [alloc.vec.Vec.length] using (congrArg List.length copied).trans (copySegment_length _ _ _ _ _)
  have refsEq : words.val.map (decodeRef table.ty) =
      Spec.Segment.copyInto (table.elements.val.map (decodeRef table.ty))
        (segment.refs.val.map (decodeRef segment.ty)) destination source count := by
    rw [copied,copySegment_eq_copyInto,copyInto_map _ _ _ _ _ _ inside,sameType]
  have lists := Itasca.Runtime.Representation.map_set_modify decodeTable
    (fun t => {t with REFS := Spec.Segment.copyInto t.REFS (decodeElement segment).REFS destination source count})
    store.tables.val tableAddress.index.val table {table with elements := words} target
    (by simp only [decodeTable,decodeElement,lengthEq,refsEq])
  rw [Spec.Segment.tableInit_eq,tableRead,elementRead]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,lists]
  rfl

/-- The four segment instructions either finish or reduce to a source trap. -/
def segmentResult (status : core.result.Result Unit runtime.ExecError) : List admininstr :=
  match status with | .Ok _ => [] | .Err _ => [.TRAP]

theorem TableInitializationEffect.refines {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (tableIndex elementIndex : U32) (tableAddress : runtime.TableAddr) (elementAddress : Usize)
    (table : runtime.store.TableInst) (segment : runtime.store.ElemInst)
    (destination source count : U64) (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : TableInitializationEffect store tableAddress.index table segment destination source count out)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (tableMapped : inst.tables.val[tableIndex.val]? = some tableAddress)
    (elementMapped : inst.elems.val[elementIndex.val]? = some elementAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (resolved : store.elems.val[elementAddress.val]? = some segment)
    (sameType : table.ty = segment.ty)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (elementBound : segment.refs.length < 2^32)
    (dstBound : destination.val < 2^32) (srcBound : source.val < 2^32) (countBound : count.val < 2^32) :
    StepsH ⟨⟨decodeStore view code store,ambient⟩,Spec.Segment.operands destination.val source.val count.val ++
      [.TABLE_INIT (.mk_uN tableIndex.val) (.mk_uN elementIndex.val)]⟩ []
      ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ := by
  have tableRead : fun_table ⟨decodeStore view code store,ambient⟩ (.mk_uN tableIndex.val) = decodeTable table := by
    simp [fun_table,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,tableMapped,target]
  have elementRead : fun_elem ⟨decodeStore view code store,ambient⟩ (.mk_uN elementIndex.val) = decodeElement segment := by
    simp [fun_elem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,elementMapped,resolved]
  have wf := decodeStore_wf view code store shape sourceSyntax
  unfold TableInitializationEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨words,rfl,copied⟩ := effect
    simp only [segmentResult]
    rw [table_init_decodes view code store inst ambient tableIndex elementIndex tableAddress elementAddress
      table segment destination.val source.val count.val words moduleEq tableMapped elementMapped target resolved sameType inside.2 copied]
    apply Spec.Segment.table_init_steps _ _ _ _ _ _ _ wf ambientWf dstBound srcBound countBound
      (by scalar_tac) (by scalar_tac)
    · simpa [moduleEq,decodeInstance] using (List.getElem?_eq_some_iff.mp tableMapped).1
    · have addressRead : ambient.MODULE.TABLES[tableIndex.val]! = tableAddress.index.val := by
        simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,tableMapped]
      rw [addressRead]
      simpa [decodeStore] using (List.getElem?_eq_some_iff.mp target).1
    · rw [tableRead]
      have bound := (shape.tables table (List.mem_of_getElem? target)).1
      simp only [decodeTable,List.length_map]
      scalar_tac
    · simpa [elementRead,decodeElement] using elementBound
    · simpa [tableRead,elementRead,decodeTable,decodeElement] using And.intro inside.2 inside.1
  · rename_i outside
    rw [effect]
    apply Spec.stepsH_single
    apply Spec.Segment.table_init_trap _ _ _ _ _ _ _ wf ambientWf dstBound srcBound countBound
      (by scalar_tac) (by scalar_tac)
    simp only [tableRead,elementRead,decodeTable,decodeElement,List.length_map]
    simp only [alloc.vec.Vec.length] at outside
    omega

end Itasca.Runtime.Store
