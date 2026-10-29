import Itasca.Runtime.Integration.Api.StatefulMemoryGrow
import Itasca.Runtime.Integration.Api.StatefulTableGrow
import Itasca.Runtime.Interp.State.StatefulOperandSlots
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp
theorem stateful_memory_grow_slots {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (amount : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (amountSlot : exec.slots.val[raw.base.val+dst.val]? = some amount)
    (shapes : ∀ object ∈ store.memories.val, MemoryShape view object)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[Abs.integerVal .I32 (UScalar.cast .U32 amount).val])
    (frameSlots : FrameSlots exec raw f)
    (position : dst.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType)) :
    runtime.interp.execute_memory_grow memory exec store raw.instance raw.base dst ⦃ out =>
      out.1 = .Ok () ∧ FrameStoreMetadata store out.2.2 ∧ ∃ result : U32,
        SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 result)) ∧
        MemoryGrowth view code store address.index (UScalar.cast .U32 amount) (result,out.2.2) ∧
        FrameSlots out.2.1 raw {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} ∧
        Abs.Stateful.Transition state f rest after .memoryGrow
          (Abs.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} rest) ⦄ := by
  apply WP.spec_mono (stateful_memory_grow_effect memory view laws code exec store raw.instance raw.base dst inst address object amount state f rest after front found mapped issued amountSlot shapes sourceStore moduleEq values)
  rintro out ⟨success,metadata,result,written,growth,transition⟩
  refine ⟨success,metadata,result,written,growth,
    Stateful.frame_write_result frameSlots values position (List.getElem?_eq_some_iff.mp amountSlot).1 written ?_,transition⟩
  simp [Code.encodeValue,Abs.integerVal,numtype_Inn,U32.cast_U64_val_eq]

theorem stateful_table_grow_slots {M A : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (dst table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (reference amount : U64)
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
    runtime.interp.execute_table_grow memory allocator exec store raw.instance raw.base dst table ⦃ out =>
      out.1 = .Ok () ∧ FrameStoreMetadata store out.2.2 ∧ ∃ result : U32,
        SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 result)) ∧
        TableGrowth store address.index (UScalar.cast .U32 amount) reference (result,out.2.2) ∧
        FrameSlots out.2.1 raw {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} ∧
        Abs.Stateful.Transition state f rest after (.tableGrow table.val)
          (Abs.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} rest) ⦄ := by
  apply WP.spec_mono (stateful_table_grow_effect memory allocator allocation view code exec store raw.instance raw.base dst table inst address object reference amount state f rest after front found mapped issued referenceSlot amountSlot sizes sourceStore moduleEq values)
  rintro out ⟨success,metadata,result,written,growth,transition⟩
  refine ⟨success,metadata,result,written,growth,
    Stateful.frame_write_result frameSlots values position (List.getElem?_eq_some_iff.mp referenceSlot).1 written ?_,transition⟩
  simp [Code.encodeValue,Abs.integerVal,numtype_Inn,U32.cast_U64_val_eq]

end Itasca.Runtime.Theorems
