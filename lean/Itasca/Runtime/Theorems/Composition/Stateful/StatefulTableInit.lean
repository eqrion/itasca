import Itasca.Runtime.Theorems.Composition.Stateful.StatefulBulk
import Itasca.Runtime.Store.Api.TableInitSemantics
import Itasca.Runtime.Store.Initialization.BulkTableAt
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem stateful_table_init_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand entry tableId elementId : U32) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) (address : runtime.TableAddr) (elementAddress : Usize)
    (object : runtime.store.TableInst) (segment : runtime.store.ElemInst) (destination source count : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some compiled)
    (descriptor : compiled.indirect.val[entry.val]? = some (elementId,tableId))
    (sourceMapped : inst.elems.val[elementId.val]? = some elementAddress)
    (sourceFound : store.elems.val[elementAddress.val]? = some segment)
    (sameType : object.ty=segment.ty)
    (mapped : inst.tables.val[tableId.val]? = some address) (target : store.tables.val[address.index.val]? = some object)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (sources : f.vals = front++[Abs.integerVal .I32 (bulkWord destination).val,
      Abs.integerVal .I32 (bulkWord source).val,Abs.integerVal .I32 (bulkWord count).val]) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.TableInit operand entry) ⦃ out =>
      TableInitializationEffect store address.index object segment (bulkWord destination) (bulkWord source) (bulkWord count) out ∧
      FrameStoreMetadata store out.2 ∧
      Abs.Stateful.Transition state f rest after (.tableInit tableId.val elementId.val)
        (statefulBulkResult view code state f rest after front out) ⦄ := by
  apply WP.spec_mono (bulk_table_init_at memory store instIndex function base slots inst compiled operand entry elementId tableId
    elementAddress address object segment destination source count found functionFound descriptor sourceMapped sourceFound
    mapped target destinationSlot sourceSlot countSlot)
  intro out effect
  refine ⟨effect,?_⟩
  unfold TableInitializationEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨words,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult]
    rw [table_init_decodes view code store inst f.toFrame tableId elementId address elementAddress object segment _ _ _ words
      moduleEq mapped sourceMapped target sourceFound sameType inside.2 filled]
    simp only [Abs.Stateful.evaluate,Abs.Stateful.tableInit,sources,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,sourceMapped,sourceFound,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at inside
    simp [
      decodeTable,decodeElement,bulk_integer_decoded,Abs.Stateful.asReference_value,inside,And.comm,alloc.vec.Vec.length]
  · rename_i outside
    rw [effect]
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult,Abs.Stateful.evaluate,Abs.Stateful.tableInit,sources,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,sourceMapped,sourceFound,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at outside
    simp [
      decodeTable,decodeElement,bulk_integer_decoded,Abs.Stateful.asReference_value,outside,And.comm,alloc.vec.Vec.length]
    intro destinationFits sourceFits
    have impossible := outside destinationFits
    omega
end Itasca.Runtime.Theorems
