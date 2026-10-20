import Exec.Theorems.Api.GrowthChoiceMatching
import Exec.Theorems.Api.StatefulMemoryGrowChosenEffect
import Exec.Theorems.Api.StatefulTableGrowChosenEffect
import Exec.Interp.State.StatefulOperandSlots
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp
theorem stateful_memory_grow_slots_chosen {choices : Exec.Spec.SourceChoices} (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (dst : U32) (inst : runtime.store.Instance)
    (address : runtime.MemoryAddr) (object : runtime.store.Memory M) (amount : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (amountSlot : exec.slots.val[raw.base.val+dst.val]? = some amount)
    (shapes : ∀ object ∈ store.memories.val, MemoryShape view object)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[Abs.integerVal .I32 (UScalar.cast .U32 amount).val])
    (frameSlots : FrameSlots exec raw f)
    (position : dst.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType)) :
    runtime.interp.admin_memory_grow memory hooks floats allocator exec store raw.instance raw.base dst ⦃ out =>
      out.1 = .Ok () ∧ FrameStoreMetadata store out.2.2 ∧ ∃ result : U32,
        SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 result)) ∧
        MemoryGrowth view code store address.index (UScalar.cast .U32 amount) (result,out.2.2) ∧
        FrameSlots out.2.1 raw {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} ∧
        Abs.Stateful.ChosenTransition choices occurrence state f rest after .memoryGrow
          (Abs.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} rest) ⦄ := by
  apply WP.spec_mono (stateful_memory_grow_effect_chosen occurrence memory hooks floats allocator view laws code compatible exec store raw.instance raw.base dst inst address object amount state f rest after front found mapped issued amountSlot shapes sourceStore moduleEq values)
  rintro out ⟨success,metadata,result,written,growth,transition⟩
  refine ⟨success,metadata,result,written,growth,
    Stateful.frame_write_result frameSlots values position (List.getElem?_eq_some_iff.mp amountSlot).1 written ?_,transition⟩
  simp [Code.encodeValue,Abs.integerVal,numtype_Inn,U32.cast_U64_val_eq]

theorem stateful_table_grow_slots_chosen {choices : Exec.Spec.SourceChoices} (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (dst table : U32) (inst : runtime.store.Instance)
    (address : runtime.TableAddr) (object : runtime.store.Table) (reference amount : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (referenceSlot : exec.slots.val[raw.base.val+dst.val]? = some reference)
    (amountSlot : exec.slots.val[raw.base.val+dst.val+1]? = some amount)
    (sizes : ∀ object ∈ store.tables.val, object.elements.length ≤ U32.max)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[val_ref (decodeRef object.ty reference),Abs.integerVal .I32 (UScalar.cast .U32 amount).val])
    (frameSlots : FrameSlots exec raw f)
    (position : dst.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType)) :
    runtime.interp.admin_table_grow memory hooks floats allocator exec store raw.instance raw.base dst table ⦃ out =>
      out.1 = .Ok () ∧ FrameStoreMetadata store out.2.2 ∧ ∃ result : U32,
        SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 result)) ∧
        TableGrowth store address.index (UScalar.cast .U32 amount) reference (result,out.2.2) ∧
        FrameSlots out.2.1 raw {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} ∧
        Abs.Stateful.ChosenTransition choices occurrence state f rest after (.tableGrow table.val)
          (Abs.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} rest) ⦄ := by
  apply WP.spec_mono (stateful_table_grow_effect_chosen occurrence memory hooks floats allocator allocation view code compatible exec store raw.instance raw.base dst table inst address object reference amount state f rest after front found mapped issued referenceSlot amountSlot sizes sourceStore moduleEq values)
  rintro out ⟨success,metadata,result,written,growth,transition⟩
  refine ⟨success,metadata,result,written,growth,
    Stateful.frame_write_result frameSlots values position (List.getElem?_eq_some_iff.mp referenceSlot).1 written ?_,transition⟩
  simp [Code.encodeValue,Abs.integerVal,numtype_Inn,U32.cast_U64_val_eq]

end Exec.Theorems
