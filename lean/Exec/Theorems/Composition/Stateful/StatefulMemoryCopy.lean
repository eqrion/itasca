import Exec.Theorems.Composition.Stateful.StatefulBulk
import Exec.Store.Api.MemoryCopySemantics
import Exec.Store.Api.MemoryCopyMutation
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem stateful_memory_copy_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand : U32) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (destination source count : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (target : store.memories.val[address.index.val]? = some object)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (sources : f.vals = front++[Abs.integerVal .I32 (bulkWord destination).val,
      Abs.integerVal .I32 (bulkWord source).val,Abs.integerVal .I32 (bulkWord count).val]) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.MemoryCopy operand) ⦃ out =>
      MemoryCopyEffect view store address.index object (bulkWord destination) (bulkWord source) (bulkWord count) out ∧
      FrameStoreMetadata store out.2 ∧
      Abs.Stateful.Transition state f rest after .memoryCopy
        (statefulBulkResult view code state f rest after front out) ⦄ := by
  apply WP.spec_mono (bulk_memory_copy memory view laws store instIndex function base slots operand inst address object
    destination source count found mapped target destinationSlot sourceSlot countSlot)
  intro out effect
  refine ⟨effect,(effect.mutation view store address object _ _ _ out).1,{},trivial,?_⟩
  unfold MemoryCopyEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨buffer,rfl,filled⟩ := effect
    simp only [statefulBulkResult]
    rw [memory_copy_decodes view code store inst f.toFrame address object _ _ _ buffer
      moduleEq mapped target ⟨inside.2,inside.1⟩ filled]
    simp only [Abs.Stateful.evaluate,Abs.Stateful.memoryCopy,sources,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at inside
    simp [
      decodeMemory,decodeBytes,bulk_integer_decoded,inside,And.comm,U32.cast_U64_val_eq]
  · rename_i outside
    rw [effect]
    simp only [statefulBulkResult,Abs.Stateful.evaluate,Abs.Stateful.memoryCopy,sources,Abs.Stateful.popThree_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,
      Option.map_some,bulk_integer_decoded,Abs.Stateful.asReference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at outside
    simp [
      decodeMemory,decodeBytes,bulk_integer_decoded,And.comm,outside]
    intro destinationFits sourceFits
    have impossible := outside destinationFits
    omega
end Exec.Theorems
