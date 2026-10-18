import Exec.Interp.State.TableAccess
import Exec.Spec.TableAccess
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Exec.Store

/-- Exact source lookup for the runtime's resolved table address. -/
theorem table_lookup_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (index : U32) (address : runtime.TableAddr) (object : runtime.store.Table)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[index.val]? = some address)
    (found : store.tables.val[address.index.val]? = some object) :
    fun_table ⟨decodeStore view code store,ambient⟩ (.mk_uN index.val) = decodeTable object := by
  simp [fun_table,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]

/-- A raw element replacement is exactly the generated source table update. -/
theorem table_write_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (index position : U32) (address : runtime.TableAddr) (object : runtime.store.Table) (word : U64)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[index.val]? = some address)
    (found : store.tables.val[address.index.val]? = some object) :
    decodeStore view code {store with tables := store.tables.set address.index ({object with elements := object.elements.set (UScalar.cast .Usize position) word})} =
      Spec.Segment.tableWrite (decodeStore view code store) ambient index.val position.val (decodeRef object.ty word) := by
  have read : ambient.MODULE.TABLES[index.val]! = address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
  unfold Spec.Segment.tableWrite
  rw [read,List.modify_eq_set_getElem?]
  simp only [decodeStore,List.getElem?_map,found,Option.map_some]
  simp only [alloc.vec.Vec.set_val_eq,List.map_set,decodeTable,List.length_set,U32.cast_Usize_val_eq,← List.set_eq_modify,Option.map_some,Option.getD_some]
  simp [alloc.vec.Vec.length,alloc.vec.Vec.set_val_eq]
  intro function member
  rfl

/-- Concrete lookup and bounds exactly select the generated read rule. -/
theorem table_read_source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (index position : U32) (address : runtime.TableAddr) (object : runtime.store.Table)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[index.val]? = some address)
    (found : store.tables.val[address.index.val]? = some object)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient) :
    StepH ⟨⟨decodeStore view code store,ambient⟩,[Spec.Segment.i32 position.val,.TABLE_GET (.mk_uN index.val)]⟩ []
      ⟨⟨decodeStore view code store,ambient⟩,if position.val < object.elements.length then
        [admininstr_ref (decodeRef object.ty object.elements.val[position.val]!)] else [.TRAP]⟩ := by
  have source := Spec.table_get_step (decodeStore view code store) ambient index.val position.val storeWf ambientWf (by scalar_tac) (by scalar_tac)
  rw [table_lookup_decodes view code store inst ambient index address object moduleEq mapped found] at source
  by_cases inside : position.val < object.elements.length
  · simpa [decodeTable,inside,_root_.getElem!_pos,alloc.vec.Vec.length] using source
  · simpa [decodeTable,inside,alloc.vec.Vec.length] using source

/-- A successful raw table write has the source TABLE_SET step. -/
theorem table_write_source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (index position : U32) (address : runtime.TableAddr) (object : runtime.store.Table) (word : U64)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[index.val]? = some address)
    (found : store.tables.val[address.index.val]? = some object)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient)
    (inside : position.val < object.elements.length) :
    StepH ⟨⟨decodeStore view code store,ambient⟩,
      [Spec.Segment.i32 position.val,admininstr_ref (decodeRef object.ty word),.TABLE_SET (.mk_uN index.val)]⟩ []
      ⟨⟨decodeStore view code {store with tables := store.tables.set address.index ({object with elements := object.elements.set (UScalar.cast .Usize position) word})},ambient⟩,[]⟩ := by
  rw [table_write_decodes view code store inst ambient index position address object word moduleEq mapped found]
  apply Spec.Segment.table_write_step _ _ _ _ _ storeWf ambientWf (by scalar_tac) (by scalar_tac)
  · simpa [moduleEq,decodeInstance] using (List.getElem?_eq_some_iff.mp mapped).1
  · rw [table_lookup_decodes view code store inst ambient index address object moduleEq mapped found]
    simpa [decodeTable] using inside
end Exec.Interp
