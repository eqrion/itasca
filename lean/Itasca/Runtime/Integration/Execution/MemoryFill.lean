import Itasca.Runtime.Integration.Execution.Mutation.BulkResult
import Itasca.Runtime.Store.Api.MemoryFill
import Itasca.Runtime.Interp.State.StatefulIntegerOperands
import Itasca.Runtime.Interp.State.StatefulLookup
import Itasca.Runtime.Store.Initialization.SegmentStep
import Itasca.Runtime.Interp.State.StatefulContinue
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission

/-!
Memory-fill correspondence from the handler to a machine step.

The store effect supplies the source transition and retained frame metadata.
Dispatch and structured-point lifting then establish the memory-fill case used
by supported bulk-memory execution, including the bounds trap.
-/

/-! ## Stateful Memory Fill -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem stateful_memory_fill_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand : U32) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (destination value count : U64)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (target : store.memories.val[address.index.val]? = some object)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (valueSlot : slots.val[base.val+operand.val+1]? = some value)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (memoryBound : (view object.buf).length ≤ 2^32)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[SourceMachine.integerVal .I32 (bulkWord destination).val,
      SourceMachine.integerVal .I32 (bulkWord value).val,SourceMachine.integerVal .I32 (bulkWord count).val]) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.MemoryFill operand) ⦃ out =>
      MemoryFillEffect view store address.index object (bulkWord destination) (bulkWord count)
        (UScalar.cast .U8 (UScalar.cast .U32 value)) out ∧
      FrameStoreMetadata store out.2 ∧
      SourceMachine.Stateful.Transition state f rest after .memoryFill
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
    simp only [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.memoryFill,values,SourceMachine.Stateful.pop_three_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,
      Option.map_some,bulk_integer_decoded,SourceMachine.Stateful.as_reference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at inside
    simp [
      decodeMemory,decodeBytes,bulk_integer_decoded,inside,U32.cast_U64_val_eq]
  · rename_i outside
    rw [effect]
    simp only [statefulBulkResult,SourceMachine.Stateful.evaluate,SourceMachine.Stateful.memoryFill,values,SourceMachine.Stateful.pop_three_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,
      Option.map_some,bulk_integer_decoded,SourceMachine.Stateful.as_reference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at outside
    simp [
      decodeMemory,decodeBytes,bulk_integer_decoded,outside]
end Itasca.Runtime.Integration

end

/-! ## Stateful Memory Fill Dispatch -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_memory_fill_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (C : context)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (first second a entry : U32)
    (signature : SourceMachine.Stateful.Signature C .memoryFill input output)
    (bindings : SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (shapes : ∀ object∈store.memories.val,MemoryShape view object)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Compiler.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Compiler.valueType value))
    (position : first.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType)) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Compiler.statefulInstruction .memoryFill first second a entry) ⦃ out =>
      out.2.1=exec ∧ out.2.2.2=platform ∧ output=[] ∧
      (∃ address : runtime.MemoryAddr,∃ object destination count value, store.memories.val[address.index.val]?=some object ∧
        MemoryFillEffect view store address.index object destination count value (out.1,out.2.2.1)) ∧
      FrameStoreMetadata store out.2.2.1 ∧ FrameSlots out.2.1 raw {f with code:=after,vals:=front} ∧
      SourceMachine.Stateful.Transition state f rest after .memoryFill
        (statefulBulkResult view code state f rest after front (out.1,out.2.2.1)) ⦄ := by
  cases signature with
  | memoryFill type selected =>
    obtain ⟨destination,source,count,rfl⟩ := three_i32_operands _ operands operandTypes typed
    obtain ⟨destinationSlot,sourceSlot,countSlot⟩ := frame_three_i32_slots destination source count slots values position
    obtain ⟨address,object,mapped,issued⟩ := memory_binding_raw view code store inst C type bindings selected
    have normalized : f.vals=front++[SourceMachine.integerVal .I32 (bulkWord (UScalar.cast .U64 destination)).val,
        SourceMachine.integerVal .I32 (bulkWord (UScalar.cast .U64 source)).val,SourceMachine.integerVal .I32 (bulkWord (UScalar.cast .U64 count)).val] := by
      simpa [bulkWord] using values
    obtain ⟨out,run,same,effect,metadata,transition⟩ := WP.spec_imp_exists
      (segment_execute_bulk memory exec store raw.instance raw.function raw.base (.MemoryFill first) _
        (stateful_memory_fill_effect memory view laws code store raw.instance raw.function raw.base (alloc.vec.Vec.deref exec.slots)
          first inst address object (UScalar.cast .U64 destination) (UScalar.cast .U64 source) (UScalar.cast .U64 count)
          state f rest after front found mapped issued (by simpa [alloc.vec.Vec.deref] using destinationSlot) (by simpa [alloc.vec.Vec.deref] using sourceSlot) (by simpa [alloc.vec.Vec.deref] using countSlot) (shapes object (List.mem_of_getElem? issued)).length_bound sourceStore moduleEq normalized))
    simp only [Compiler.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,trivial,⟨address,object,_,_,_,issued,effect⟩,metadata,
      by rw [same];exact frame_consume after slots values,transition⟩
end Itasca.Runtime.Integration

end

/-! ## Stateful Memory Fill Step -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_memory_fill_point_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    (point : Machine.FramePoint (decodeStore view code store) raw {f with code:=SourceMachine.Stateful.Instruction.memoryFill.source::after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=SourceMachine.Stateful.Instruction.memoryFill.source::after}::rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=SourceMachine.Stateful.Instruction.memoryFill.source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      Machine.FramePoint (decodeStore view code store) {raw with pc:=target} {f with code:=SourceMachine.Stateful.Instruction.memoryFill.source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2=platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ((∃ pc : U32,∃ front : List val,
        out.1=.Ok () ∧ pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
        (∃ address : runtime.MemoryAddr,∃ object destination source count,store.memories.val[address.index.val]?=some object ∧ MemoryFillEffect view store address.index object destination source count (out.1,out.2.2.1)) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=front} ∧
        Machine.FramePoint (decodeStore view code out.2.2.1) {raw with pc:=pc} {f with code:=after,vals:=front} compiled C targets next output ∧
        SourceMachine.Cumulative.Step initial (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .MemoryOutOfBounds) ∧ out.2.2.1=store ∧
        (∃ pc : U32,pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}}) ∧
        SourceMachine.Cumulative.Step initial .trap)) ⦄ := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (decodeStore view code store) {f with code:=SourceMachine.Stateful.Instruction.memoryFill.source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f .memoryFill after frameTyped point.code with jump | operation
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
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=SourceMachine.Stateful.Instruction.memoryFill.source::after}::rest,[]⟩
    obtain ⟨out,run,same,samePlatform,resultNil,rawEffect,metadata,represented,transition⟩ := WP.spec_imp_exists
      (stateful_memory_fill_dispatch memory hooks floats allocator view laws code advanced store platform index raw inst C initial
        {f with code:=SourceMachine.Stateful.Instruction.memoryFill.source::after} rest after front operands input result first second a entry signature
        bindings found shapes rfl moduleEq slots values operandTypes operandTyped actualPosition)
    rw [run]
    apply WP.spec.ret
    refine ⟨samePlatform,metadata,?_⟩
    obtain ⟨address,object,destination,source,count,issued,effect⟩ := rawEffect
    have classified := (effect.mutation view store address object destination source count _).2
    rcases classified with ⟨success,mutation⟩ | ⟨error,sameStore⟩
    · change out.1=.Ok () at success
      have sourceStep : SourceMachine.Stateful.Transition initial {f with code:=SourceMachine.Stateful.Instruction.memoryFill.source::after} rest after .memoryFill
          (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩) := by
        simpa [statefulBulkResult,success,initial,SourceMachine.advance] using transition
      refine Or.inl ⟨pc,front,success,pcNext,same,⟨address,object,destination,source,count,issued,effect⟩,represented,?_,?_⟩
      · have safe := SourceMachine.Stateful.transition_next .memoryFill (decodeStore view code store) ambient {f with code:=SourceMachine.Stateful.Instruction.memoryFill.source::after} rest after
          ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩ typed sourceStep
        have continued := point.continue safe.2.1 front operands [] after values heights (by simpa only [resultNil,List.map_nil] using tail) pc pcNext
        simpa only [List.append_nil] using continued
      · exact .stateful sourceStep (by intro impossible;cases impossible)
    · change out.1=.Err (.Trap .MemoryOutOfBounds) at error
      have sourceStep : SourceMachine.Stateful.Transition initial {f with code:=SourceMachine.Stateful.Instruction.memoryFill.source::after} rest after .memoryFill .trap := by
        simpa [statefulBulkResult,error] using transition
      exact Or.inr ⟨error,sameStore,⟨pc,pcNext,same⟩,.stateful sourceStep (by intro impossible;cases impossible)⟩
end Itasca.Runtime.Integration

end
