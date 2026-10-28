import Itasca.Runtime.Theorems.Composition.Stateful.StatefulBulk
import Itasca.Runtime.Store.Api.MemoryFillSemantics
import Itasca.Runtime.Store.Api.MemoryFillMutation
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem stateful_memory_fill_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand : U32) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (destination value count : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (target : store.memories.val[address.index.val]? = some object)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (valueSlot : slots.val[base.val+operand.val+1]? = some value)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (memoryBound : (view object.buf).length ≤ 2^32)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[Abs.integerVal .I32 (bulkWord destination).val,
      Abs.integerVal .I32 (bulkWord value).val,Abs.integerVal .I32 (bulkWord count).val]) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.MemoryFill operand) ⦃ out =>
      MemoryFillEffect view store address.index object (bulkWord destination) (bulkWord count)
        (UScalar.cast .U8 (UScalar.cast .U32 value)) out ∧
      FrameStoreMetadata store out.2 ∧
      Abs.Stateful.Transition state f rest after .memoryFill
        (statefulBulkResult view code state f rest after front out) ⦄ := by
  apply WP.spec_mono (bulk_memory_fill memory view laws store instIndex function base slots operand inst address object
    destination value count found mapped target destinationSlot valueSlot countSlot)
  intro out effect
  refine ⟨effect,(effect.mutation view store address object _ _ _ out).1,{},trivial,?_⟩
  unfold MemoryFillEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨buffer,rfl,filled⟩ := effect
    simp only [statefulBulkResult]
    rw [memory_fill_decodes view code store inst f.toFrame address object _ _ (UScalar.cast .U32 value) buffer
      moduleEq mapped target memoryBound inside filled]
    simp only [Abs.Stateful.evaluate,Abs.Stateful.memoryFill,values,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at inside
    simp [
      decodeMemory,decodeBytes,bulk_integer_decoded,inside,U32.cast_U64_val_eq]
  · rename_i outside
    rw [effect]
    simp only [statefulBulkResult,Abs.Stateful.evaluate,Abs.Stateful.memoryFill,values,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at outside
    simp [
      decodeMemory,decodeBytes,bulk_integer_decoded,outside]
end Itasca.Runtime.Theorems
