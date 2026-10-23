import Exec.Store.Api.TableFillEffect
import Exec.Store.Api.TableFillLists
import Exec.Store.Api.TableInitSemantics
namespace Exec.Store
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

/-- Actual bounds-checked table fill implements the generated sequence of
per-element writes, or the generated bounds trap without a partial write. -/
theorem TableFillEffect.refines {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (tableIndex : U32) (address : runtime.TableAddr) (table : runtime.store.TableInst)
    (destination value count : U64) (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : TableFillEffect store address.index table destination value count out)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[tableIndex.val]? = some address)
    (target : store.tables.val[address.index.val]? = some table)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (dstBound : destination.val < 2^32) (countBound : count.val < 2^32) :
    StepsH ⟨⟨decodeStore view code store,ambient⟩,
      Spec.Segment.fillOperands destination.val (decodeRef table.ty value) count.val ++ [.TABLE_FILL (.mk_uN tableIndex.val)]⟩ []
      ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ := by
  have tableRead : fun_table ⟨decodeStore view code store,ambient⟩ (.mk_uN tableIndex.val) = decodeTable table := by
    simp [fun_table,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,target]
  have wf := decodeStore_wf view code store shape sourceSyntax
  unfold TableFillEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨words,rfl,filled⟩ := effect
    simp only [segmentResult]
    rw [table_fill_decodes view code store inst ambient tableIndex address table destination.val count.val value words moduleEq mapped target filled]
    apply Spec.Segment.table_fill_steps _ _ _ _ _ _ wf ambientWf dstBound countBound (by scalar_tac)
    · simpa [moduleEq,decodeInstance] using (List.getElem?_eq_some_iff.mp mapped).1
    · have addressRead : ambient.MODULE.TABLES[tableIndex.val]! = address.index.val := by
        simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
      rw [addressRead]
      simpa [decodeStore] using (List.getElem?_eq_some_iff.mp target).1
    · rw [tableRead]
      have bound := (shape.tables table (List.mem_of_getElem? target)).1
      simp only [decodeTable,List.length_map]
      scalar_tac
    · simpa [tableRead,decodeTable] using inside
  · rename_i outside
    rw [effect]
    apply Spec.stepsH_single
    apply Spec.Segment.table_fill_trap _ _ _ _ _ _ wf ambientWf dstBound countBound (by scalar_tac)
    simp only [tableRead,decodeTable,List.length_map]
    simp only [alloc.vec.Vec.length] at outside
    omega
end Exec.Store
