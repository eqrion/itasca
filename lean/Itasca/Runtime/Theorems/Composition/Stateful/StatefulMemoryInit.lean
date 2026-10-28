import Itasca.Runtime.Theorems.Composition.Stateful.StatefulBulk
import Itasca.Runtime.Store.Api.MemoryInitSemantics
import Itasca.Runtime.Store.Initialization.BulkMemoryAt
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem stateful_memory_init_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand dataId : U32) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr) (dataAddress : Usize)
    (object : runtime.store.MemInst M) (segment : runtime.store.DataInst) (destination source count : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (target : store.memories.val[address.index.val]? = some object)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (dataMapped : inst.datas.val[dataId.val]? = some dataAddress)
    (resolved : store.datas.val[dataAddress.val]? = some segment)
    (memoryBound : (view object.buf).length ≤ 2^32) (dataBound : segment.bytes.length ≤ 2^32)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (sources : f.vals = front++[Abs.integerVal .I32 (bulkWord destination).val,
      Abs.integerVal .I32 (bulkWord source).val,Abs.integerVal .I32 (bulkWord count).val]) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.MemoryInit operand dataId) ⦃ out =>
      MemoryInitializationEffect view store address.index object segment (bulkWord destination) (bulkWord source) (bulkWord count) out ∧
      FrameStoreMetadata store out.2 ∧
      Abs.Stateful.Transition state f rest after (.memoryInit dataId.val)
        (statefulBulkResult view code state f rest after front out) ⦄ := by
  apply WP.spec_mono (bulk_memory_init_at memory view laws store instIndex function base slots inst operand dataId
    dataAddress address object segment destination source count found dataMapped resolved mapped target
    destinationSlot sourceSlot countSlot)
  intro out effect
  refine ⟨effect,?_⟩
  unfold MemoryInitializationEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨buffer,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult]
    rw [memory_init_decodes view code store inst f.toFrame dataId address dataAddress object segment _ _ _ buffer
      moduleEq mapped dataMapped target resolved memoryBound dataBound ⟨inside.2,inside.1⟩ filled]
    simp only [Abs.Stateful.evaluate,Abs.Stateful.memoryInit,sources,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,dataMapped,resolved,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at inside
    simp [
      decodeMemory,decodeData,decodeBytes,bulk_integer_decoded,inside,And.comm,U32.cast_U64_val_eq]
  · rename_i outside
    rw [effect]
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult,Abs.Stateful.evaluate,Abs.Stateful.memoryInit,sources,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,dataMapped,resolved,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at outside
    simp [
      decodeMemory,decodeData,decodeBytes,bulk_integer_decoded,And.comm,outside]
    intro destinationFits sourceFits
    have impossible := outside destinationFits
    omega
end Itasca.Runtime.Theorems
