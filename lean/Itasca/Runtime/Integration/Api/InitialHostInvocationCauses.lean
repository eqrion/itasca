import Itasca.Runtime.SourceMachine.Stateful.Bound
import Itasca.Runtime.Interp.Memory.MemoryGrow
import Itasca.Runtime.Store.Api.TableGrowSource
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.State.StatefulIntegerOperands
import Itasca.Runtime.Interp.State.StatefulSegmentLookup
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Integration.Host.HostDispatchCauses
import Itasca.Runtime.Interp.Invocation.Recording

/-!
Sections, each formerly its own module: StatefulGrowthChoice, StatefulMemoryGrow, StatefulTableGrow, StatefulGrowthSlots, StatefulMemoryGrowExecution, StatefulTableGrowExecution, InitialHostInvocationCauses.
-/

/-! ## StatefulGrowthChoice -/

section

namespace Itasca.Runtime.Integration
open SpecExt

theorem stateful_memory_choice (state : SourceMachine.AState) (f : SourceMachine.AFrame) (front : List val)
    (delta address : Nat) (object : meminst) (choice : Option meminst)
    (values : f.vals = front++[SourceMachine.integerVal .I32 delta])
    (mapped : f.module.MEMS[0]? = some address) (found : state.store.MEMS[address]? = some object)
    (grown : SourceMachine.Stateful.MemoryGrowthChoice object delta choice) :
    SourceMachine.Stateful.Selection.Allowed {memory:=choice} .memoryGrow state.store f := by
  intro otherFront otherDelta otherAddress otherObject otherValues otherMapped otherFound
  have addresses : otherAddress=address := Option.some.inj (otherMapped.symm.trans mapped)
  subst otherAddress
  have objects : otherObject=object := Option.some.inj (otherFound.symm.trans found)
  subst otherObject
  have equal := congrArg SourceMachine.pop (otherValues.symm.trans values)
  simp only [SourceMachine.pop_append,Option.some.injEq,Prod.mk.injEq] at equal
  have deltaEq : otherDelta=delta := by simpa [SourceMachine.integerVal,numtype_Inn] using equal.2
  simpa only [deltaEq] using grown

theorem stateful_table_choice (state : SourceMachine.AState) (f : SourceMachine.AFrame) (front : List val)
    (index delta address : Nat) (reference : ref) (object : tableinst) (choice : Option tableinst)
    (values : f.vals = front++[val_ref reference,SourceMachine.integerVal .I32 delta])
    (mapped : f.module.TABLES[index]? = some address) (found : state.store.TABLES[address]? = some object)
    (grown : SourceMachine.Stateful.TableGrowthChoice object delta reference choice) :
    SourceMachine.Stateful.Selection.Allowed {table:=choice} (.tableGrow index) state.store f := by
  intro otherFront otherReference otherDelta otherAddress otherObject otherValues otherMapped otherFound
  have addresses : otherAddress=address := Option.some.inj (otherMapped.symm.trans mapped)
  subst otherAddress
  have objects : otherObject=object := Option.some.inj (otherFound.symm.trans found)
  subst otherObject
  have equal := congrArg SourceMachine.pop (otherValues.symm.trans values)
  rw [show otherFront++[val_ref otherReference,SourceMachine.integerVal .I32 otherDelta] =
    (otherFront++[val_ref otherReference])++[SourceMachine.integerVal .I32 otherDelta] by simp,
    show front++[val_ref reference,SourceMachine.integerVal .I32 delta] =
    (front++[val_ref reference])++[SourceMachine.integerVal .I32 delta] by simp] at equal
  simp only [SourceMachine.pop_append,Option.some.injEq,Prod.mk.injEq] at equal
  have deltaEq : otherDelta=delta := by simpa [SourceMachine.integerVal,numtype_Inn] using equal.2
  have refs := congrArg SourceMachine.pop equal.1
  simp only [SourceMachine.pop_append,Option.some.injEq,Prod.mk.injEq] at refs
  have refEq : otherReference=reference := by
    have decoded := congrArg SourceMachine.Stateful.asReference refs.2
    simpa only [SourceMachine.Stateful.as_reference_value,Option.some.injEq] using decoded
  simpa only [deltaEq,refEq] using grown
end Itasca.Runtime.Integration

end

/-! ## StatefulMemoryGrow -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem stateful_memory_growth {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (delta : U32) (out : U32 × runtime.store.Store M)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (shape : MemoryShape view object) (sourceStore : state.store = decodeStore view code store)
    (moduleEq : f.module = decodeInstance store inst) (values : f.vals = front++[SourceMachine.integerVal .I32 delta.val])
    (effect : MemoryGrowth view code store address.index delta out) :
    FrameStoreMetadata store out.2 ∧
    SourceMachine.Stateful.Transition state f rest after .memoryGrow
      (SourceMachine.advance {state with store:=decodeStore view code out.2}
        {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 out.1.val]} rest) := by
  have sourceMapped : f.module.MEMS[0]? = some address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem?_map,mapped]
  have sourceFound : state.store.MEMS[address.index.val]? = some (decodeMemory view object) := by
    simp [sourceStore,decodeStore,List.getElem?_map,issued]
  have decoded : SourceMachine.integer .I32 (SourceMachine.integerVal .I32 delta.val)=some delta.val :=
    SourceMachine.integer_accepts .I32 _ (by change delta.val<2^32;scalar_tac)
  rcases effect with ⟨failed,same,changed⟩ | ⟨old,buffer,count,lookup,bytes,used,limit,capacity,maximum,size,changed⟩
  · refine ⟨?_,{},SourceMachine.Stateful.Selection.refusal_allowed _ _ _,?_⟩
    · rcases changed with same | ⟨old,buffer,lookup,viewEq,same⟩
      · rw [same]; exact .refl _
      · rw [same]; exact ⟨rfl,rfl,rfl,rfl⟩
    · rw [failed,same,←sourceStore]
      simp only [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.memoryGrow,values,SourceMachine.pop_append,sourceMapped,sourceFound,decoded]
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
    simp only [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.memoryGrow,values,SourceMachine.pop_append,sourceMapped,sourceFound,decoded]
    simp only [decodeMemory,decodeBytes,List.length_map]

theorem stateful_memory_grow_effect {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (amount : U64)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (amountSlot : exec.slots.val[base.val+dst.val]? = some amount)
    (shapes : ∀ object ∈ store.memories.val, MemoryShape view object)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[SourceMachine.integerVal .I32 (UScalar.cast .U32 amount).val]) :
    runtime.interp.execute_memory_grow memory exec store instanceIndex base dst ⦃ out =>
      out.1 = .Ok () ∧ FrameStoreMetadata store out.2.2 ∧ ∃ result : U32,
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 result)) ∧
        MemoryGrowth view code store address.index (UScalar.cast .U32 amount) (result,out.2.2) ∧
        SourceMachine.Stateful.Transition state f rest after .memoryGrow
          (SourceMachine.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} rest) ⦄ := by
  have primitive := memory_grow_effect memory view laws code store address.index (UScalar.cast .U32 amount)
    (List.getElem?_eq_some_iff.mp issued).1
    (fun object member => (shapes object member).length_bound) (fun object member => (shapes object member).1)
  apply WP.spec_mono (memory_grow_handler memory exec store instanceIndex base dst inst address amount
    found mapped amountSlot _ primitive)
  rintro out ⟨result,success,growth,slots⟩
  obtain ⟨metadata,transition⟩ := stateful_memory_growth view code store inst address object (UScalar.cast .U32 amount)
    (result,out.2.2) state f rest after front mapped issued (shapes object (List.mem_of_getElem? issued)) sourceStore moduleEq values growth
  exact ⟨success,metadata,result,slots,growth,transition⟩
end Itasca.Runtime.Integration

end

/-! ## StatefulTableGrow -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem stateful_table_growth {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (table : U32) (address : runtime.TableAddr)
    (object : runtime.store.TableInst) (delta : U32) (reference : U64) (out : U32 × runtime.store.Store M)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[val_ref (decodeRef object.ty reference),SourceMachine.integerVal .I32 delta.val])
    (effect : TableGrowth store address.index delta reference out) :
    FrameStoreMetadata store out.2 ∧
    SourceMachine.Stateful.Transition state f rest after (.tableGrow table.val)
      (SourceMachine.advance {state with store:=decodeStore view code out.2}
        {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 out.1.val]} rest) := by
  have sourceMapped : f.module.TABLES[table.val]? = some address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem?_map,mapped]
  have sourceFound : state.store.TABLES[address.index.val]? = some (decodeTable object) := by
    simp [sourceStore,decodeStore,List.getElem?_map,issued]
  have decoded : SourceMachine.integer .I32 (SourceMachine.integerVal .I32 delta.val)=some delta.val :=
    SourceMachine.integer_accepts .I32 _ (by change delta.val<2^32;scalar_tac)
  have splitValues : f.vals = (front++[val_ref (decodeRef object.ty reference)])++[SourceMachine.integerVal .I32 delta.val] := by
    simpa only [List.append_assoc,List.singleton_append] using values
  rcases effect with ⟨failed,same⟩ | ⟨old,elements,count,lookup,words,capacity,used,limit,maximum,changed⟩
  · refine ⟨by rw [same];exact .refl _,{},SourceMachine.Stateful.Selection.refusal_allowed _ _ _,?_⟩
    rw [failed,same,←sourceStore]
    simp only [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.tableGrow,splitValues,SourceMachine.pop_append,sourceMapped,sourceFound,
      decoded,SourceMachine.Stateful.as_reference_value]
    rfl
  · have oldEq : old=object := Option.some.inj (lookup.symm.trans issued)
    subst old
    have grown := decode_table_growth object elements delta reference words capacity maximum
    have actual : decodeStore view code out.2 =
        {state.store with TABLES:=state.store.TABLES.set address.index.val (decodeTable {object with elements})} := by
      rw [changed,sourceStore]
      simp only [decodeStore,alloc.vec.Vec.set_val_eq,List.map_set]
      rfl
    have size : out.1.val=object.elements.length := by
      rw [changed]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      change object.elements.length < 2^32
      scalar_tac
    refine ⟨by rw [changed];exact ⟨rfl,rfl,rfl,rfl⟩,
      {table:=some (decodeTable {object with elements})},
      stateful_table_choice state f front table.val delta.val address.index.val _ _ _ values sourceMapped sourceFound (.grown grown),?_⟩
    rw [actual,size]
    simp only [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.tableGrow,splitValues,SourceMachine.pop_append,sourceMapped,sourceFound,
      decoded,SourceMachine.Stateful.as_reference_value]
    simp only [decodeTable,List.length_map]

theorem stateful_table_grow_effect {M A : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (reference amount : U64)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (referenceSlot : exec.slots.val[base.val+dst.val]? = some reference)
    (amountSlot : exec.slots.val[base.val+dst.val+1]? = some amount)
    (sizes : ∀ object ∈ store.tables.val, object.elements.length ≤ U32.max)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[val_ref (decodeRef object.ty reference),SourceMachine.integerVal .I32 (UScalar.cast .U32 amount).val]) :
    runtime.interp.execute_table_grow memory allocator exec store instanceIndex base dst table ⦃ out =>
      out.1 = .Ok () ∧ FrameStoreMetadata store out.2.2 ∧ ∃ result : U32,
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 result)) ∧
        TableGrowth store address.index (UScalar.cast .U32 amount) reference (result,out.2.2) ∧
        SourceMachine.Stateful.Transition state f rest after (.tableGrow table.val)
          (SourceMachine.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} rest) ⦄ := by
  have primitive := table_grow_effect memory allocator allocation store address.index (UScalar.cast .U32 amount) reference
    (List.getElem?_eq_some_iff.mp issued).1 sizes
  apply WP.spec_mono (table_grow_handler memory allocator exec store instanceIndex base dst table inst address reference amount
    found mapped referenceSlot amountSlot _ primitive)
  rintro out ⟨result,success,growth,slots⟩
  obtain ⟨metadata,transition⟩ := stateful_table_growth view code store inst table address object (UScalar.cast .U32 amount) reference
    (result,out.2.2) state f rest after front mapped issued sourceStore moduleEq values growth
  exact ⟨success,metadata,result,slots,growth,transition⟩
end Itasca.Runtime.Integration

end

/-! ## StatefulGrowthSlots -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp
theorem stateful_memory_grow_slots {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (amount : U64)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (amountSlot : exec.slots.val[raw.base.val+dst.val]? = some amount)
    (shapes : ∀ object ∈ store.memories.val, MemoryShape view object)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[SourceMachine.integerVal .I32 (UScalar.cast .U32 amount).val])
    (frameSlots : FrameSlots exec raw f)
    (position : dst.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType)) :
    runtime.interp.execute_memory_grow memory exec store raw.instance raw.base dst ⦃ out =>
      out.1 = .Ok () ∧ FrameStoreMetadata store out.2.2 ∧ ∃ result : U32,
        SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 result)) ∧
        MemoryGrowth view code store address.index (UScalar.cast .U32 amount) (result,out.2.2) ∧
        FrameSlots out.2.1 raw {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} ∧
        SourceMachine.Stateful.Transition state f rest after .memoryGrow
          (SourceMachine.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} rest) ⦄ := by
  apply WP.spec_mono (stateful_memory_grow_effect memory view laws code exec store raw.instance raw.base dst inst address object amount state f rest after front found mapped issued amountSlot shapes sourceStore moduleEq values)
  rintro out ⟨success,metadata,result,written,growth,transition⟩
  refine ⟨success,metadata,result,written,growth,
    Stateful.frame_write_result frameSlots values position (List.getElem?_eq_some_iff.mp amountSlot).1 written ?_,transition⟩
  simp [Compiler.encodeValue,SourceMachine.integerVal,numtype_Inn,U32.cast_U64_val_eq]

theorem stateful_table_grow_slots {M A : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (dst table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (reference amount : U64)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (referenceSlot : exec.slots.val[raw.base.val+dst.val]? = some reference)
    (amountSlot : exec.slots.val[raw.base.val+dst.val+1]? = some amount)
    (sizes : ∀ object ∈ store.tables.val, object.elements.length ≤ U32.max)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[val_ref (decodeRef object.ty reference),SourceMachine.integerVal .I32 (UScalar.cast .U32 amount).val])
    (frameSlots : FrameSlots exec raw f)
    (position : dst.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType)) :
    runtime.interp.execute_table_grow memory allocator exec store raw.instance raw.base dst table ⦃ out =>
      out.1 = .Ok () ∧ FrameStoreMetadata store out.2.2 ∧ ∃ result : U32,
        SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 result)) ∧
        TableGrowth store address.index (UScalar.cast .U32 amount) reference (result,out.2.2) ∧
        FrameSlots out.2.1 raw {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} ∧
        SourceMachine.Stateful.Transition state f rest after (.tableGrow table.val)
          (SourceMachine.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} rest) ⦄ := by
  apply WP.spec_mono (stateful_table_grow_effect memory allocator allocation view code exec store raw.instance raw.base dst table inst address object reference amount state f rest after front found mapped issued referenceSlot amountSlot sizes sourceStore moduleEq values)
  rintro out ⟨success,metadata,result,written,growth,transition⟩
  refine ⟨success,metadata,result,written,growth,
    Stateful.frame_write_result frameSlots values position (List.getElem?_eq_some_iff.mp referenceSlot).1 written ?_,transition⟩
  simp [Compiler.encodeValue,SourceMachine.integerVal,numtype_Inn,U32.cast_U64_val_eq]

end Itasca.Runtime.Integration

end

/-! ## StatefulMemoryGrowExecution -/

section

/-!
Memory growth dispatch and structured execution. Shared growth-slot adapters and handler effects remain below both memory and table growth constructions.
-/

/-! ## Stateful Memory Grow Dispatch -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_memory_grow_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (C : context)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (first second a entry : U32)
    (signature : SourceMachine.Stateful.Signature C .memoryGrow input output)
    (bindings : SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (shapes : ∀ object∈store.memories.val,MemoryShape view object)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Compiler.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Compiler.valueType value))
    (position : first.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType)) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Compiler.statefulInstruction .memoryGrow first second a entry) ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ output=[.I32] ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ result : U32,
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+first.val) (UScalar.cast .U64 result)) ∧
      (∃ address delta,address.val<store.memories.length ∧ MemoryGrowth view code store address delta (result,out.2.2.1)) ∧
      FrameSlots out.2.1 raw {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} ∧
      SourceMachine.Stateful.Transition state f rest after .memoryGrow
        (SourceMachine.advance {state with store:=decodeStore view code out.2.2.1}
          {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} rest) ⦄ := by
  cases signature with
  | memoryGrow type selected =>
    obtain ⟨value,rfl⟩ := List.length_eq_one_iff.mp (by simpa only [List.length_map,List.length_singleton] using congrArg List.length operandTypes)
    have valueType : Compiler.valueType value=.I32 := by simpa using operandTypes
    have valueTyped := typed value (by simp)
    rw [valueType] at valueTyped
    obtain ⟨bits,rfl,bitsBound⟩ := SourceMachine.integer_val_inv (ty:=.I32) valueTyped
    let delta : U32 := UScalar.ofNatCore bits (by change bits<2^32;exact bitsBound)
    let amount := UScalar.cast .U64 delta
    have amountValue : amount.val=bits := by simp [amount,delta]
    have deltaValue : (UScalar.cast .U32 amount).val=bits := by simp [amount,delta];exact bitsBound
    have encoded : Compiler.encodeValues [SourceMachine.integerVal .I32 bits]=[bits] := rfl
    have amountSlot := frame_read_scalar slots values position encoded 0 (by simp) amount (by simpa using amountValue)
    simp only [Nat.add_zero] at amountSlot
    obtain ⟨address,object,mapped,issued⟩ := memory_binding_raw view code store inst C type bindings selected
    obtain ⟨out,run,success,metadata,result,written,growth,represented,transition⟩ := WP.spec_imp_exists
      (stateful_memory_grow_slots memory view laws code exec store raw first inst address object amount
        state f rest after front found mapped issued amountSlot shapes sourceStore moduleEq
        (by simpa only [deltaValue] using values) slots position)
    simp only [Compiler.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨success,rfl,trivial,metadata,result,written,⟨address.index,_,(List.getElem?_eq_some_iff.mp issued).1,growth⟩,represented,transition⟩
end Itasca.Runtime.Integration

end

/-! ## Stateful Memory Grow Step -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_memory_grow_point_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [projection : Itasca.Runtime.Interp.Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (fetchBound : compiled.code.length≤U32.max)
    (shapes : ∀ object∈store.memories.val,MemoryShape view object)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (decodeStore view code store) raw {f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after}::rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      Machine.FramePoint (decodeStore view code store) {raw with pc:=target} {f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ pc : U32,∃ front : List val,∃ position : Nat,∃ result : U32,
        pc.val=raw.pc.val+1 ∧ raw.base.val≤position ∧ position<exec.slots.length ∧
        SlotsEffect {exec with frames:=exec.frames.set index {raw with pc:=pc}} out.2.1 (exec.slots.val.set position (UScalar.cast .U64 result)) ∧
        (∃ address delta,address.val<store.memories.length ∧ MemoryGrowth view code store address delta (result,out.2.2.1)) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} ∧
        Machine.FramePoint (decodeStore view code out.2.2.1) {raw with pc:=pc} {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} compiled C targets next output ∧
        SourceMachine.Cumulative.Step initial (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]}::rest,[]⟩) ⦄ := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (decodeStore view code store) {f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f .memoryGrow after frameTyped point.code with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,operands,input,result,first,second,a,b,entry,values,operandTypes,signature,heights,operandTyped,position,secondSlot,arguments,pair,fetch,tail⟩ := operation
    have pcBound : raw.pc.val<U32.max := by
      have inCode := (List.getElem?_eq_some_iff.mp fetch).1
      change compiled.code.val.length≤U32.max at fetchBound
      omega
    have actualPosition : first.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType) := by
      simpa only [point.locals] using position
    have bindings : SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C := by
      rw [←moduleEq]
      exact point.bindings
    apply Or.inr
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled _ last frameFound found codeFound fetch pcBound
    intro pc pcNext
    let advanced := {exec with frames:=exec.frames.set index {raw with pc:=pc}}
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after}::rest,[]⟩
    obtain ⟨out,run,success,samePlatform,resultType,metadata,resultValue,written,mutation,represented,transition⟩ := WP.spec_imp_exists
      (stateful_memory_grow_dispatch memory hooks floats allocator view laws code advanced store platform index raw inst C initial
        {f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after} rest after front operands input result first second a entry signature
        bindings found shapes rfl moduleEq slots values operandTypes operandTyped actualPosition)
    rw [run]
    apply WP.spec.ret
    have operandLength : operands.length≥1 := by
      have equal := congrArg List.length operandTypes
      rw [List.length_map,signature.input_length] at equal
      cases signature <;> simp_all [SourceMachine.Stateful.Instruction.arity]
    have capacity : raw.base.val+first.val<exec.slots.length := by
      have allScalar := signature.inputs_scalar
      have live := slots
      have enough : Compiler.encodeValues operands ≠ [] := by
        intro empty
        have lengthEq := congrArg List.length empty
        rw [Compiler.encode_values_length,operandTypes] at lengthEq
        cases signature <;> simp [Compiler.slots,Compiler.width] at lengthEq
      have words := frame_read_suffix slots values actualPosition rfl
      have firstWord := words 0 (List.length_pos_iff.mpr enough)
      simpa only [Nat.add_zero] using firstWord.1
    refine ⟨success,samePlatform,metadata,pc,front,raw.base.val+first.val,resultValue,pcNext,Nat.le_add_right _ _,capacity,written,mutation,represented,?_,?_⟩
    · have safe := SourceMachine.Stateful.transition_next .memoryGrow (decodeStore view code store) ambient f rest after
        ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front++[SourceMachine.integerVal .I32 resultValue.val]}::rest,[]⟩ typed transition
      exact point.continue safe.2.1 front operands [SourceMachine.integerVal .I32 resultValue.val] after values heights
        (by simpa only [resultType,Compiler.valueType,SourceMachine.integerVal,List.map_cons,List.map_nil,numtype_Inn,valtype_numtype] using tail) pc pcNext
    · exact .stateful transition (by intro impossible;cases impossible)
end Itasca.Runtime.Integration

end

end

/-! ## StatefulTableGrowExecution -/

section

/-!
Table growth dispatch and structured execution. Shared growth-slot adapters and handler effects remain below both memory and table growth constructions.
-/

/-! ## Stateful Table Grow Dispatch -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_table_grow_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (C : context)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (index : Nat) (first second a b entry : U32)
    (signature : SourceMachine.Stateful.Signature C (.tableGrow index) input output)
    (bindings : SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (sizes : ∀ object∈store.tables.val,object.elements.length≤U32.max)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Compiler.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Compiler.valueType value))
    (position : first.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (arguments : Compiler.StatefulArguments (.tableGrow index) a b) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Compiler.statefulInstruction (.tableGrow index) first second a entry) ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ output=[.I32] ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ result : U32,
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+first.val) (UScalar.cast .U64 result)) ∧
      (∃ address object delta reference,store.tables.val[address.val]?=some object ∧
        TableGrowth store address delta reference (result,out.2.2.1) ∧ val_ref (decodeRef object.ty reference)∈f.vals) ∧
      FrameSlots out.2.1 raw {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} ∧
      SourceMachine.Stateful.Transition state f rest after (.tableGrow index)
        (SourceMachine.advance {state with store:=decodeStore view code out.2.2.1}
          {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} rest) ⦄ := by
  cases signature with
  | tableGrow index type limits selected =>
    obtain ⟨x,y,rfl,xType,yType⟩ := two_operand_values operandTypes
    have xTyped := typed x (by simp)
    have yTyped := typed y (by simp)
    rw [xType] at xTyped
    rw [yType] at yTyped
    obtain ⟨reference,rfl,referenceTyped⟩ := SourceMachine.Stateful.reference_operand xTyped
    obtain ⟨bits,rfl,bitsBound⟩ := SourceMachine.integer_val_inv (ty:=.I32) yTyped
    let delta : U32 := UScalar.ofNatCore bits (by change bits<2^32;exact bitsBound)
    let amount := UScalar.cast .U64 delta
    have amountValue : amount.val=bits := by simp [amount,delta]
    have deltaValue : (UScalar.cast .U32 amount).val=bits := by simp [amount,delta];exact bitsBound
    obtain ⟨address,object,mapped,issued,objectType⟩ := table_binding_raw view code store inst C index _ bindings selected
    change decodeElemType object.ty=type at objectType
    have indexEq : a.val=index := arguments.1
    rw [←indexEq] at mapped
    obtain ⟨referenceBits,referenceEncoded⟩ := reference_encoding reference
    have encoded : Compiler.encodeValues [val_ref reference,SourceMachine.integerVal .I32 bits]=[referenceBits,bits] := by
      simp only [Compiler.encodeValues,List.flatMap_cons,List.flatMap_nil,List.append_nil,referenceEncoded]
      rfl
    let referenceWord := exec.slots.val[raw.base.val+first.val]!
    obtain ⟨referenceBound,referenceValue⟩ := frame_read_suffix_word slots values position encoded 0 (by simp)
    simp only [Nat.add_zero,List.getElem!_cons_zero] at referenceBound referenceValue
    have referenceSlot : exec.slots.val[raw.base.val+first.val]?=some referenceWord := by
      simp only [referenceWord,List.getElem?_eq_getElem referenceBound,_root_.getElem!_pos exec.slots.val (raw.base.val+first.val) referenceBound]
    have referenceEq : val_ref reference=val_ref (decodeRef object.ty referenceWord) :=
      reference_word_value _ _ _ (by simpa only [objectType] using xType) (by rw [referenceValue];exact referenceEncoded)
    have amountSlot := frame_read_scalar slots values position encoded 1 (by simp) amount (by simpa using amountValue)
    obtain ⟨out,run,success,metadata,result,written,growth,represented,transition⟩ := WP.spec_imp_exists
      (stateful_table_grow_slots memory allocator allocation view code exec store raw first a inst address object referenceWord amount
        state f rest after front found mapped issued referenceSlot amountSlot sizes sourceStore moduleEq
        (by rw [←referenceEq,deltaValue];exact values) slots position)
    simp only [Compiler.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨success,rfl,trivial,metadata,result,written,⟨address.index,object,_,_,issued,growth,by rw [←referenceEq,values];simp⟩,represented,by simpa only [indexEq] using transition⟩
end Itasca.Runtime.Integration

end

/-! ## Stateful Table Grow Step -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_table_grow_point_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [projection : Itasca.Runtime.Interp.Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (table : Nat)
    (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (fetchBound : compiled.code.length≤U32.max)
    (sizes : ∀ object∈store.tables.val,object.elements.length≤U32.max)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (decodeStore view code store) raw {f with code:=(SourceMachine.Stateful.Instruction.tableGrow table).source::after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableGrow table).source::after}::rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableGrow table).source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      Machine.FramePoint (decodeStore view code store) {raw with pc:=target} {f with code:=(SourceMachine.Stateful.Instruction.tableGrow table).source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ pc : U32,∃ front : List val,∃ position : Nat,∃ result : U32,
        pc.val=raw.pc.val+1 ∧ raw.base.val≤position ∧ position<exec.slots.length ∧
        SlotsEffect {exec with frames:=exec.frames.set index {raw with pc:=pc}} out.2.1 (exec.slots.val.set position (UScalar.cast .U64 result)) ∧
        (∃ address object delta reference,store.tables.val[address.val]?=some object ∧ TableGrowth store address delta reference (result,out.2.2.1) ∧ val_ref (decodeRef object.ty reference)∈f.vals) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} ∧
        Machine.FramePoint (decodeStore view code out.2.2.1) {raw with pc:=pc} {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} compiled C targets next output ∧
        SourceMachine.Cumulative.Step initial (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]}::rest,[]⟩) ⦄ := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (decodeStore view code store) {f with code:=(SourceMachine.Stateful.Instruction.tableGrow table).source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f (.tableGrow table) after frameTyped point.code with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,operands,input,result,first,second,a,b,entry,values,operandTypes,signature,heights,operandTyped,position,secondSlot,arguments,pair,fetch,tail⟩ := operation
    have pcBound : raw.pc.val<U32.max := by
      have inCode := (List.getElem?_eq_some_iff.mp fetch).1
      change compiled.code.val.length≤U32.max at fetchBound
      omega
    have actualPosition : first.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType) := by
      simpa only [point.locals] using position
    have bindings : SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C := by
      rw [←moduleEq]
      exact point.bindings
    apply Or.inr
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled _ last frameFound found codeFound fetch pcBound
    intro pc pcNext
    let advanced := {exec with frames:=exec.frames.set index {raw with pc:=pc}}
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableGrow table).source::after}::rest,[]⟩
    obtain ⟨out,run,success,samePlatform,resultType,metadata,resultValue,written,mutation,represented,transition⟩ := WP.spec_imp_exists
      (stateful_table_grow_dispatch memory hooks floats allocator allocation view code advanced store platform index raw inst C initial
        {f with code:=(SourceMachine.Stateful.Instruction.tableGrow table).source::after} rest after front operands input result table first second a b entry signature
        bindings found sizes rfl moduleEq slots values operandTypes operandTyped actualPosition arguments)
    rw [run]
    apply WP.spec.ret
    have operandLength : operands.length≥1 := by
      have equal := congrArg List.length operandTypes
      rw [List.length_map,signature.input_length] at equal
      cases signature <;> simp_all [SourceMachine.Stateful.Instruction.arity]
    have capacity : raw.base.val+first.val<exec.slots.length := by
      have allScalar := signature.inputs_scalar
      have live := slots
      have enough : Compiler.encodeValues operands ≠ [] := by
        intro empty
        have lengthEq := congrArg List.length empty
        rw [Compiler.encode_values_length,operandTypes] at lengthEq
        cases signature <;> simp [Compiler.slots,Compiler.width] at lengthEq
      have words := frame_read_suffix slots values actualPosition rfl
      have firstWord := words 0 (List.length_pos_iff.mpr enough)
      simpa only [Nat.add_zero] using firstWord.1
    refine ⟨success,samePlatform,metadata,pc,front,raw.base.val+first.val,resultValue,pcNext,Nat.le_add_right _ _,capacity,written,mutation,represented,?_,?_⟩
    · have safe := SourceMachine.Stateful.transition_next (.tableGrow table) (decodeStore view code store) ambient f rest after
        ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front++[SourceMachine.integerVal .I32 resultValue.val]}::rest,[]⟩ typed transition
      exact point.continue safe.2.1 front operands [SourceMachine.integerVal .I32 resultValue.val] after values heights
        (by simpa only [resultType,Compiler.valueType,SourceMachine.integerVal,List.map_cons,List.map_nil,numtype_Inn,valtype_numtype] using tail) pc pcNext
    · exact .stateful transition (by intro impossible;cases impossible)
end Itasca.Runtime.Integration

end

end

/-! ## InitialHostInvocationCauses -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- Exact initial-host invocation causes. Setup retains the initial store;
readback retains the completed source host event and its actual refused result
request; call failure retains the exact prepared base-zero helper execution. -/
def InitialHostInvocationCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (ambient : frame) (address : runtime.FuncAddr) (identity : U64)
    (signature : Itasca.wasm_types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  (after=store ∧ InvocationResourceCause allocator exec store signature results error) ∨
  (error=.Exhausted .Allocation ∧ ∃ values,
    ResultsTyped (Store.decodeStore view code after) (signature.results.val.map sourceType) values ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
      [.call address.index.val (args.val.map sourceValue) (some values)]
      ⟨⟨Store.decodeStore view code after,ambient⟩,vals values⟩ ∧
    ∃ n : Usize, n.val=signature.results.length-results.length ∧ allocator.reserve results n=.ok (false,results)) ∨
  ∃ (prepared : runtime.interp.Execution) (p : P)
    (called : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P),
    prepared.store=store.id ∧ prepared.frames.val=[] ∧ ValuesAt prepared.slots.val 0 (args.val.map sourceValue) ∧
    runtime.interp.call memory hooks floats allocator prepared store p address 0#usize=.ok called ∧
    called.1=.Err error ∧ called.2.2.1=after ∧
    HostCallCauses allocator hooks prepared store p signature 0#usize identity called

/-- Values refusal before or during initial host preparation uses only the
source signature buffers. There is no source Wasm frame requirement to invent. -/
theorem InitialHostInvocationCause.source_values {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {signature : Itasca.wasm_types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    (cause : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results after (.Exhausted .Values)) :
    store.limits.max_values.val<signatureWords (Store.decodeFuncType signature) := by
  rcases cause with ⟨same,cause⟩ | ⟨impossible,_⟩ | ⟨prepared,p,called,_,_,_,_,failed,_,cause⟩
  · exact cause
  · cases impossible
  · simpa only [HostCallCauses,failed,HostPreparationCause,hostSlotDemand,typeSlots,
      (show (0#usize).val = 0 from rfl),Nat.zero_add,Store.decodeFuncType,signatureWords,Nat.max_comm] using cause

/-- Every initial-host allocation refusal is an actual request bounded by
source parameter/result lengths or the source signature's slot width. -/
theorem InitialHostInvocationCause.source_allocation {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {signature : Itasca.wasm_types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    (cause : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results after (.Exhausted .Allocation)) :
    HostSignatureAllocation allocator (signature.params.val.map sourceType) (signature.results.val.map sourceType) 0 := by
  rcases cause with ⟨same,cause⟩ | ⟨_,values,typed,source,n,amount,refused⟩ | ⟨prepared,p,called,_,_,_,_,failed,_,cause⟩
  · rcases cause with ⟨n,bound,refused⟩ | ⟨n,amount,refused⟩
    · exact Or.inl ⟨exec.slots,n,by simpa only [Nat.zero_add,typeSlots] using bound,refused⟩
    · refine Or.inr (Or.inr ⟨results,n,?_,refused⟩)
      simp only [List.length_map]
      simp only [alloc.vec.Vec.length] at amount
      omega
  · refine Or.inr (Or.inr ⟨results,n,?_,refused⟩)
    simp only [List.length_map]
    simp only [alloc.vec.Vec.length] at amount
    omega
  · simp only [HostCallCauses,failed,HostPreparationCause] at cause
    rcases cause with ⟨n,bound,refused⟩ | ⟨n,bound,refused⟩ | ⟨n,bound,refused⟩
    · exact Or.inl ⟨prepared.slots,n,by simpa only [hostSlotDemand,typeSlots,(show (0#usize).val = 0 from rfl),Nat.zero_add,Nat.max_comm] using bound,refused⟩
    · exact Or.inr (Or.inl ⟨prepared.host_args,n,by simpa only [List.length_map] using bound,refused⟩)
    · exact Or.inr (Or.inr ⟨prepared.host_results,n,by simpa only [List.length_map] using bound,refused⟩)

theorem InitialHostInvocationCause.interrupted {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {signature : Itasca.wasm_types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    (cause : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results after .Terminated) :
    ∃ p next, hooks.interrupt p=.ok (.Terminate,next) := by
  rcases cause with ⟨same,impossible⟩ | ⟨impossible,_⟩ | ⟨prepared,p,called,_,_,_,_,failed,_,cause⟩
  · exact False.elim impossible
  · cases impossible
  · exact ⟨p,by simpa only [HostCallCauses,failed,HostPreparationCause] using cause⟩

theorem InitialHostInvocationCause.host_overflow {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {signature : Itasca.wasm_types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    (cause : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results after (.Exhausted .CallStack)) :
    ∃ p arguments defaults host returned,
      hooks.call_host p store identity arguments defaults=.ok (.Err .StackOverflow,host,after,returned) := by
  rcases cause with ⟨same,impossible⟩ | ⟨impossible,_⟩ | ⟨prepared,p,called,_,_,_,_,failed,same,cause⟩
  · exact False.elim impossible
  · cases impossible
  · simp only [HostCallCauses,failed] at cause
    obtain ⟨next,arguments,defaults,returned,actual⟩ := cause
    exact ⟨next,arguments,defaults,called.2.2.2,returned,by simpa only [same] using actual⟩
end Itasca.Runtime.Integration

end
