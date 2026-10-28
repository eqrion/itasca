import Exec.Theorems.Api.StatefulGrowthChoice
import Exec.Interp.Memory.MemoryGrow
import Exec.Store.Api.MemoryGrowSource
import Exec.Interp.Relations.FrameStoreMetadata
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem stateful_memory_growth {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (delta : U32) (out : U32 × runtime.store.Store M)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (shape : MemoryShape view object) (sourceStore : state.store = decodeStore view code store)
    (moduleEq : f.module = decodeInstance store inst) (values : f.vals = front++[Abs.integerVal .I32 delta.val])
    (effect : MemoryGrowth view code store address.index delta out) :
    FrameStoreMetadata store out.2 ∧
    Abs.Stateful.Transition state f rest after .memoryGrow
      (Abs.advance {state with store:=decodeStore view code out.2}
        {f with code:=after,vals:=front++[Abs.integerVal .I32 out.1.val]} rest) := by
  have sourceMapped : f.module.MEMS[0]? = some address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem?_map,mapped]
  have sourceFound : state.store.MEMS[address.index.val]? = some (decodeMemory view object) := by
    simp [sourceStore,decodeStore,List.getElem?_map,issued]
  have decoded : Abs.integer .I32 (Abs.integerVal .I32 delta.val)=some delta.val :=
    Abs.integer_accepts .I32 _ (by change delta.val<2^32;scalar_tac)
  rcases effect with ⟨failed,same,changed⟩ | ⟨old,buffer,count,lookup,bytes,used,limit,capacity,maximum,size,changed⟩
  · refine ⟨?_,{},Abs.Stateful.Selection.refusal_allowed _ _ _,?_⟩
    · rcases changed with same | ⟨old,buffer,lookup,viewEq,same⟩
      · rw [same]; exact .refl _
      · rw [same]; exact ⟨rfl,rfl,rfl,rfl⟩
    · rw [failed,same,←sourceStore]
      simp only [Abs.Stateful.evaluate,Abs.Stateful.memoryGrow,values,Abs.pop_append,sourceMapped,sourceFound,decoded]
      rfl
  · have oldEq : old=object := Option.some.inj (lookup.symm.trans issued)
    subst old
    have grown := decode_memory_growth view object buffer delta shape bytes capacity maximum
    have actual : decodeStore view code out.2 =
        {state.store with MEMS:=state.store.MEMS.set address.index.val (decodeMemory view {object with buf:=buffer})} := by
      rw [changed,sourceStore]
      simp only [decodeStore,alloc.vec.Vec.set_val_eq,List.map_set]
      rfl
    refine ⟨by rw [changed];exact ⟨rfl,rfl,rfl,rfl⟩,
      {memory:=some (decodeMemory view {object with buf:=buffer})},
      stateful_memory_choice state f front delta.val address.index.val _ _ values sourceMapped sourceFound (.grown grown),?_⟩
    rw [actual,size]
    simp only [Abs.Stateful.evaluate,Abs.Stateful.memoryGrow,values,Abs.pop_append,sourceMapped,sourceFound,decoded]
    simp only [decodeMemory,decodeBytes,List.length_map]

theorem stateful_memory_grow_effect {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (amount : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (amountSlot : exec.slots.val[base.val+dst.val]? = some amount)
    (shapes : ∀ object ∈ store.memories.val, MemoryShape view object)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[Abs.integerVal .I32 (UScalar.cast .U32 amount).val]) :
    runtime.interp.execute_memory_grow memory exec store instanceIndex base dst ⦃ out =>
      out.1 = .Ok () ∧ FrameStoreMetadata store out.2.2 ∧ ∃ result : U32,
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 result)) ∧
        MemoryGrowth view code store address.index (UScalar.cast .U32 amount) (result,out.2.2) ∧
        Abs.Stateful.Transition state f rest after .memoryGrow
          (Abs.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} rest) ⦄ := by
  have primitive := memory_grow_effect memory view laws code store address.index (UScalar.cast .U32 amount)
    (List.getElem?_eq_some_iff.mp issued).1
    (fun object member => (shapes object member).length_bound) (fun object member => (shapes object member).1)
  apply WP.spec_mono (memory_grow_handler memory exec store instanceIndex base dst inst address amount
    found mapped amountSlot _ primitive)
  rintro out ⟨result,success,growth,slots⟩
  obtain ⟨metadata,transition⟩ := stateful_memory_growth view code store inst address object (UScalar.cast .U32 amount)
    (result,out.2.2) state f rest after front mapped issued (shapes object (List.mem_of_getElem? issued)) sourceStore moduleEq values growth
  exact ⟨success,metadata,result,slots,growth,transition⟩
end Itasca.Runtime.Theorems
