import Exec.Theorems.Api.StatefulMemoryGrowthChosen
import Exec.Theorems.Api.GrowthChoiceMatching
import Exec.Interp.Memory.MemoryGrow
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem stateful_memory_grow_effect_chosen {choices : Exec.Spec.SourceChoices} (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst : U32) (inst : runtime.store.Instance)
    (address : runtime.MemoryAddr) (object : runtime.store.Memory M) (amount : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (amountSlot : exec.slots.val[base.val+dst.val]? = some amount)
    (shapes : ∀ object ∈ store.memories.val, MemoryShape view object)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[Abs.integerVal .I32 (UScalar.cast .U32 amount).val]) :
    runtime.interp.admin_memory_grow memory hooks floats allocator exec store instanceIndex base dst ⦃ out =>
      out.1 = .Ok () ∧ FrameStoreMetadata store out.2.2 ∧ ∃ result : U32,
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 result)) ∧
        MemoryGrowth view code store address.index (UScalar.cast .U32 amount) (result,out.2.2) ∧
        Abs.Stateful.ChosenTransition choices occurrence state f rest after .memoryGrow
          (Abs.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} rest) ⦄ := by
  have primitive := memory_grow_effect memory view laws code store address.index (UScalar.cast .U32 amount)
    (List.getElem?_eq_some_iff.mp issued).1
    (fun object member => (shapes object member).length_bound) (fun object member => (shapes object member).1)
  have chosenPrimitive : runtime.store.Store.grow_memory_index memory store address.index (UScalar.cast .U32 amount) ⦃ out => MemoryGrowth view code store address.index (UScalar.cast .U32 amount) out ∧ choices.memory occurrence (decodeMemory view object) (UScalar.cast .U32 amount).val=memoryGrowthReply view address.index out ⦄ := by
    obtain ⟨out,actual,effect⟩ := WP.spec_imp_exists primitive
    rw [actual,WP.spec_ok]
    exact ⟨effect,compatible.memoryReply occurrence store address.index (UScalar.cast .U32 amount) object out issued actual⟩
  apply WP.spec_mono (memory_grow_handler memory hooks floats allocator exec store instanceIndex base dst inst address amount
    found mapped amountSlot _ chosenPrimitive)
  rintro out ⟨result,success,⟨growth,matched⟩,slots⟩
  obtain ⟨metadata,transition⟩ := stateful_memory_growth_chosen occurrence view code store inst address object (UScalar.cast .U32 amount)
    (result,out.2.2) state f rest after front mapped issued (shapes object (List.mem_of_getElem? issued)) sourceStore moduleEq values growth matched
  exact ⟨success,metadata,result,slots,growth,transition⟩
end Exec.Theorems
