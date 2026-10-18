import Exec.Theorems.Composition.Stateful.StatefulBulk
import Exec.Store.Api.TableFillSemantics
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem stateful_table_fill_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand tableId : U32) (inst : runtime.store.Instance) (address : runtime.TableAddr)
    (object : runtime.store.Table) (destination value count : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.tables.val[tableId.val]? = some address) (target : store.tables.val[address.index.val]? = some object)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (valueSlot : slots.val[base.val+operand.val+1]? = some value)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[Abs.integerVal .I32 (bulkWord destination).val,
      val_ref (decodeRef object.ty value),Abs.integerVal .I32 (bulkWord count).val]) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.TableFill operand tableId) ⦃ out =>
      TableFillEffect store address.index object (bulkWord destination) value (bulkWord count) out ∧
      FrameStoreMetadata store out.2 ∧
      Abs.Stateful.Transition state f rest after (.tableFill tableId.val)
        (statefulBulkResult view code state f rest after front out) ⦄ := by
  apply WP.spec_mono (bulk_table_fill memory store instIndex function base slots operand tableId inst address object
    destination value count found mapped target destinationSlot valueSlot countSlot)
  intro out effect
  refine ⟨effect,?_⟩
  unfold TableFillEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨words,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult]
    rw [table_fill_decodes view code store inst f.toFrame tableId address object _ _ value words
      moduleEq mapped target filled]
    simp only [Abs.Stateful.evaluate,Abs.Stateful.tableFill,values,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at inside
    simp [
      decodeTable,bulk_integer_decoded,Abs.Stateful.asReference_value,inside,alloc.vec.Vec.length]
  · rename_i outside
    rw [effect]
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult,Abs.Stateful.evaluate,Abs.Stateful.tableFill,values,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at outside
    simp [
      decodeTable,bulk_integer_decoded,Abs.Stateful.asReference_value,outside,alloc.vec.Vec.length]
end Exec.Theorems
