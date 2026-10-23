import Exec.Theorems.Api.StatefulGrowthMatching
import Exec.Theorems.Api.GrowthChoiceMatching
import Exec.Theorems.Api.StatefulGrowthChoice
import Exec.Interp.Memory.MemoryGrow
import Exec.Store.Api.MemoryGrowSource
import Exec.Interp.Relations.FrameStoreMetadata
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem stateful_memory_growth_chosen {choices : Exec.Spec.SourceChoices} (occurrence : Nat) {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (delta : U32) (out : U32 × runtime.store.Store M)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (shape : MemoryShape view object) (sourceStore : state.store = decodeStore view code store)
    (moduleEq : f.module = decodeInstance store inst) (values : f.vals = front++[Abs.integerVal .I32 delta.val])
    (effect : MemoryGrowth view code store address.index delta out)
    (matched : choices.memory occurrence (decodeMemory view object) delta.val=memoryGrowthReply view address.index out) :
    FrameStoreMetadata store out.2 ∧
    Abs.Stateful.ChosenTransition choices occurrence state f rest after .memoryGrow
      (Abs.advance {state with store:=decodeStore view code out.2}
        {f with code:=after,vals:=front++[Abs.integerVal .I32 out.1.val]} rest) := by
  have sourceMapped : f.module.MEMS[0]? = some address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem?_map,mapped]
  have sourceFound : state.store.MEMS[address.index.val]? = some (decodeMemory view object) := by
    simp [sourceStore,decodeStore,List.getElem?_map,issued]
  have decoded : Abs.integer .I32 (Abs.integerVal .I32 delta.val)=some delta.val :=
    Abs.integer_accepts .I32 _ (by change delta.val<2^32;scalar_tac)
  rcases effect with ⟨failed,same,changed⟩ | ⟨old,buffer,count,lookup,bytes,used,limit,capacity,maximum,size,changed⟩
  · refine ⟨?_,{},Abs.Stateful.Selection.refusal_allowed _ _ _,?_,?_⟩
    · rcases changed with same | ⟨old,buffer,lookup,viewEq,same⟩
      · rw [same]; exact .refl _
      · rw [same]; exact ⟨rfl,rfl,rfl,rfl⟩
    · apply stateful_memory_match choices occurrence state f front delta.val address.index.val _ _ values sourceMapped sourceFound
      simpa only [memoryGrowthReply,failed,show core.num.U32.MAX.val=2^32-1 by decide,ite_true] using matched
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
      stateful_memory_choice state f front delta.val address.index.val _ _ values sourceMapped sourceFound (.grown grown),?_,?_⟩
    · apply stateful_memory_match choices occurrence state f front delta.val address.index.val _ _ values sourceMapped sourceFound
      have below : (view object.buf).length/65536 ≠ 2^32-1 := by
        have bound := shape.2.1
        omega
      rw [memoryGrowthReply,if_neg (by simpa only [size] using below)] at matched
      simpa [changed,alloc.vec.Vec.set_val_eq,List.getElem?_set,
        (List.getElem?_eq_some_iff.mp issued).1] using matched
    · rw [actual,size]
      simp only [Abs.Stateful.evaluate,Abs.Stateful.memoryGrow,values,Abs.pop_append,sourceMapped,sourceFound,decoded]
      simp only [decodeMemory,decodeBytes,List.length_map]

end Exec.Theorems
