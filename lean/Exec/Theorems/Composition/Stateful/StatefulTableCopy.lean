import Exec.Theorems.Composition.Stateful.StatefulBulk
import Exec.Store.Api.TableCopySemantics
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem stateful_table_copy_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand entry tableId sourceId : U32) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) (address sourceAddress : runtime.TableAddr)
    (object sourceObject : runtime.store.TableInst) (destination source count : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some compiled)
    (descriptor : compiled.indirect.val[entry.val]? = some (tableId,sourceId))
    (sourceMapped : inst.tables.val[sourceId.val]? = some sourceAddress)
    (sourceFound : store.tables.val[sourceAddress.index.val]? = some sourceObject)
    (sameType : sourceObject.ty=object.ty)
    (mapped : inst.tables.val[tableId.val]? = some address) (target : store.tables.val[address.index.val]? = some object)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (sources : f.vals = front++[Abs.integerVal .I32 (bulkWord destination).val,
      Abs.integerVal .I32 (bulkWord source).val,Abs.integerVal .I32 (bulkWord count).val]) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.TableCopy operand entry) ⦃ out =>
      TableCopyEffect store address.index object sourceObject (bulkWord destination) (bulkWord source) (bulkWord count) out ∧
      FrameStoreMetadata store out.2 ∧
      Abs.Stateful.Transition state f rest after (.tableCopy tableId.val sourceId.val)
        (statefulBulkResult view code state f rest after front out) ⦄ := by
  apply WP.spec_mono (bulk_table_copy memory store instIndex function base slots inst compiled operand entry tableId sourceId
    sourceAddress address object sourceObject destination source count found functionFound descriptor sourceMapped sourceFound
    mapped target destinationSlot sourceSlot countSlot)
  intro out effect
  refine ⟨effect,?_⟩
  unfold TableCopyEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨words,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult]
    rw [table_copy_decodes view code store inst f.toFrame tableId sourceId address sourceAddress object sourceObject _ _ _ words
      moduleEq mapped sourceMapped target sourceFound sameType ⟨inside.2,inside.1⟩ filled]
    simp only [Abs.Stateful.evaluate,Abs.Stateful.tableCopy,sources,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,sourceMapped,sourceFound,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at inside
    simp [
      decodeTable,bulk_integer_decoded,Abs.Stateful.asReference_value,inside,And.comm,alloc.vec.Vec.length]
  · rename_i outside
    rw [effect]
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult,Abs.Stateful.evaluate,Abs.Stateful.tableCopy,sources,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,sourceMapped,sourceFound,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at outside
    simp [
      decodeTable,bulk_integer_decoded,Abs.Stateful.asReference_value,outside,And.comm,alloc.vec.Vec.length]
    intro destinationFits sourceFits
    have impossible := outside destinationFits
    omega
end Exec.Theorems
