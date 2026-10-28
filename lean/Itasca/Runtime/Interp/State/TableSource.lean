import Itasca.Runtime.Interp.State.TableAccess
import Itasca.Runtime.Spec.TableAccess
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store

/-- Exact source lookup for the runtime's resolved table address. -/
theorem table_lookup_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : runtime.TableAddr) (object : runtime.store.TableInst)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[index.val]? = some address)
    (found : store.tables.val[address.index.val]? = some object) :
    fun_table ⟨decodeStore view code store,ambient⟩ (.mk_uN index.val) = decodeTable object := by
  simp [fun_table,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]

/-- A raw element replacement is exactly the generated source table update. -/
theorem table_write_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index position : U32) (address : runtime.TableAddr) (object : runtime.store.TableInst) (word : U64)
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

end Itasca.Runtime.Interp
