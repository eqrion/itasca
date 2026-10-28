import Itasca.Runtime.Store.Api.TableFillEffect
import Itasca.Runtime.Store.Api.TableFillLists
import Itasca.Runtime.Store.Api.TableInitSemantics
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

private theorem fill_map_set_modify {T U : Type} (decode : T → U) (change : U → U)
    (values : List T) (index : Nat) (old replacement : T)
    (found : values[index]? = some old) (same : decode replacement = change (decode old)) :
    (values.set index replacement).map decode = (values.map decode).modify index change := by
  induction values generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst old
      simpa using same
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      simpa using ih index found

theorem table_fill_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (tableIndex : U32) (address : runtime.TableAddr) (table : runtime.store.TableInst)
    (destination count : Nat) (value : U64) (words : alloc.vec.Vec U64)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[tableIndex.val]? = some address)
    (target : store.tables.val[address.index.val]? = some table)
    (filled : words.val = fillTableWords table.elements.val destination value count) :
    decodeStore view code {store with tables := store.tables.set address.index {table with elements := words}} =
      Spec.Segment.tableFill (decodeStore view code store) ambient tableIndex.val destination (decodeRef table.ty value) count := by
  have tableRead : ambient.MODULE.TABLES[tableIndex.val]! = address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
  have lengthEq : words.length = table.elements.length := by
    simpa only [alloc.vec.Vec.length] using (congrArg List.length filled).trans (fillTableWords_length _ _ _ _)
  have refsEq : words.val.map (decodeRef table.ty) =
      Spec.Segment.fillInto (table.elements.val.map (decodeRef table.ty)) destination (decodeRef table.ty value) count := by
    rw [filled,fillTableWords_eq,Spec.Segment.fillInto_map]
  have lists := fill_map_set_modify decodeTable
    (fun t => {t with REFS := Spec.Segment.fillInto t.REFS destination (decodeRef table.ty value) count})
    store.tables.val address.index.val table {table with elements := words} target
    (by simp only [decodeTable,lengthEq,refsEq])
  rw [Spec.Segment.tableFill_eq,tableRead]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,lists]
  rfl

end Itasca.Runtime.Store
