import Itasca.Runtime.Integration.Execution.Mutation.BulkResult
import Itasca.Runtime.Store.Api.MemoryInit
import Itasca.Runtime.Store.Initialization.BulkMemoryAt
import Itasca.Runtime.Interp.State.StatefulIntegerOperands
import Itasca.Runtime.Interp.State.StatefulLookup
import Itasca.Runtime.Store.Initialization.SegmentStep
import Itasca.Runtime.Interp.State.StatefulSegmentLookup
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Interp.State.StatefulContinue
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission

/-!
MemoryInit correspondence from store handler through dispatch to structured execution. Retains mutation, source-step and bounds-trap obligations for the bulk-operation execution theorem.
-/

/-! ## Stateful Memory Init -/

section

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

end

/-! ## Stateful Memory Init Dispatch -/

section

namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_memory_init_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (C : context)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (index : Nat) (first second a b entry : U32)
    (signature : Abs.Stateful.Signature C (.memoryInit index) input output)
    (bindings : Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (shapes : ∀ object∈store.memories.val,MemoryShape view object) (bounds : SegmentBounds store)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Code.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Code.valueType value))
    (position : first.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (arguments : Code.StatefulArguments (.memoryInit index) a b) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.statefulInstruction (.memoryInit index) first second a entry) ⦃ out =>
      out.2.1=exec ∧ out.2.2.2=platform ∧ output=[] ∧
      (∃ address : runtime.MemoryAddr,∃ object segment destination source count, store.memories.val[address.index.val]?=some object ∧
        MemoryInitializationEffect view store address.index object segment destination source count (out.1,out.2.2.1)) ∧
      FrameStoreMetadata store out.2.2.1 ∧ FrameSlots out.2.1 raw {f with code:=after,vals:=front} ∧
      Abs.Stateful.Transition state f rest after (.memoryInit index)
        (statefulBulkResult view code state f rest after front (out.1,out.2.2.1)) ⦄ := by
  cases signature with
  | memoryInit index type selected dataSelected =>
    obtain ⟨destination,source,count,rfl⟩ := three_i32_operands _ operands operandTypes typed
    obtain ⟨destinationSlot,sourceSlot,countSlot⟩ := frame_three_i32_slots destination source count slots values position
    obtain ⟨address,object,mapped,issued⟩ := memory_binding_raw view code store inst C type bindings selected
    have indexEq : a.val=index := arguments.1
    obtain ⟨dataAddress,dataMapped,dataIssued⟩ := data_binding_raw view code store inst C index _ bindings dataSelected
    rw [←indexEq] at dataMapped
    let segment := store.datas.val[dataAddress.val]
    have resolved : store.datas.val[dataAddress.val]?=some segment := List.getElem?_eq_getElem dataIssued
    have dataBound := bounds.data segment (List.mem_of_getElem? resolved)
    have normalized : f.vals=front++[Abs.integerVal .I32 (bulkWord (UScalar.cast .U64 destination)).val,
        Abs.integerVal .I32 (bulkWord (UScalar.cast .U64 source)).val,Abs.integerVal .I32 (bulkWord (UScalar.cast .U64 count)).val] := by
      simpa [bulkWord] using values
    obtain ⟨out,run,same,effect,metadata,transition⟩ := WP.spec_imp_exists
      (segment_execute_bulk memory exec store raw.instance raw.function raw.base (.MemoryInit first a) _
        (stateful_memory_init_effect memory view laws code store raw.instance raw.function raw.base (alloc.vec.Vec.deref exec.slots)
          first a inst address dataAddress object segment (UScalar.cast .U64 destination) (UScalar.cast .U64 source) (UScalar.cast .U64 count)
          state f rest after front found mapped issued (by simpa [alloc.vec.Vec.deref] using destinationSlot) (by simpa [alloc.vec.Vec.deref] using sourceSlot) (by simpa [alloc.vec.Vec.deref] using countSlot) dataMapped resolved (shapes object (List.mem_of_getElem? issued)).length_bound (Nat.le_of_lt dataBound) sourceStore moduleEq normalized))
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,trivial,⟨address,object,segment,_,_,_,issued,effect⟩,metadata,
      by rw [same];exact frame_consume after slots values,by simpa only [indexEq] using transition⟩
end Itasca.Runtime.Theorems

end

/-! ## Stateful Memory Init Step -/

section

namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_memory_init_point_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [projection : Itasca.Runtime.Interp.StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (dataIndex : Nat)
    (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (fetchBound : compiled.code.length≤U32.max)
    (shapes : ∀ object∈store.memories.val,MemoryShape view object) (bounds : SegmentBounds store)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint (decodeStore view code store) raw {f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after}::rest,[]⟩) :
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      StructuredMachine.FramePoint (decodeStore view code store) {raw with pc:=target} {f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2=platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ((∃ pc : U32,∃ front : List val,
        out.1=.Ok () ∧ pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
        (∃ address : runtime.MemoryAddr,∃ object segment destination source count,store.memories.val[address.index.val]?=some object ∧ MemoryInitializationEffect view store address.index object segment destination source count (out.1,out.2.2.1)) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=front} ∧
        StructuredMachine.FramePoint (decodeStore view code out.2.2.1) {raw with pc:=pc} {f with code:=after,vals:=front} compiled C targets next output ∧
        Abs.Cumulative.Step initial (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .MemoryOutOfBounds) ∧ out.2.2.1=store ∧
        (∃ pc : U32,pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}}) ∧
        Abs.Cumulative.Step initial .trap)) ⦄ := by
  dsimp only
  have frameTyped : Abs.FrameTyped (decodeStore view code store) {f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f (.memoryInit dataIndex) after frameTyped point.code with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,operands,input,result,first,second,a,b,entry,values,operandTypes,signature,heights,operandTyped,position,secondSlot,arguments,pair,fetch,tail⟩ := operation
    have pcBound : raw.pc.val<U32.max := by
      have inCode := (List.getElem?_eq_some_iff.mp fetch).1
      change compiled.code.val.length≤U32.max at fetchBound
      omega
    have actualPosition : first.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType) := by
      simpa only [point.locals] using position
    have bindings : Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C := by
      rw [←moduleEq]
      exact point.bindings
    apply Or.inr
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled _ last frameFound found codeFound fetch pcBound
    intro pc pcNext
    let advanced := {exec with frames:=exec.frames.set index {raw with pc:=pc}}
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after}::rest,[]⟩
    obtain ⟨out,run,same,samePlatform,resultNil,rawEffect,metadata,represented,transition⟩ := WP.spec_imp_exists
      (stateful_memory_init_dispatch memory hooks floats allocator view laws code advanced store platform index raw inst C initial
        {f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after} rest after front operands input result dataIndex first second a b entry signature
        bindings found shapes bounds rfl moduleEq slots values operandTypes operandTyped actualPosition arguments)
    rw [run]
    apply WP.spec.ret
    refine ⟨samePlatform,metadata,?_⟩
    obtain ⟨address,object,segment,destination,source,count,issued,effect⟩ := rawEffect
    have classified : out.1=.Ok () ∨ (out.1=.Err (.Trap .MemoryOutOfBounds) ∧ out.2.2.1=store) := by
      unfold MemoryInitializationEffect at effect
      split at effect
      · obtain ⟨buffer,equal,content⟩ := effect
        exact Or.inl (congrArg Prod.fst equal)
      · exact Or.inr ⟨congrArg Prod.fst effect,congrArg Prod.snd effect⟩
    rcases classified with success | ⟨error,sameStore⟩
    · change out.1=.Ok () at success
      have sourceStep : Abs.Stateful.Transition initial {f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after} rest after (.memoryInit dataIndex)
          (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩) := by
        simpa [statefulBulkResult,success,initial,Abs.advance] using transition
      refine Or.inl ⟨pc,front,success,pcNext,same,⟨address,object,segment,destination,source,count,issued,effect⟩,represented,?_,?_⟩
      · have safe := Abs.Stateful.transition_next (.memoryInit dataIndex) (decodeStore view code store) ambient {f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after} rest after
          ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩ typed sourceStep
        have continued := point.continue safe.2.1 front operands [] after values heights (by simpa only [resultNil,List.map_nil] using tail) pc pcNext
        simpa only [List.append_nil] using continued
      · exact .stateful sourceStep (by intro impossible;cases impossible)
    · change out.1=.Err (.Trap .MemoryOutOfBounds) at error
      have sourceStep : Abs.Stateful.Transition initial {f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after} rest after (.memoryInit dataIndex) .trap := by
        simpa [statefulBulkResult,error] using transition
      exact Or.inr ⟨error,sameStore,⟨pc,pcNext,same⟩,.stateful sourceStep (by intro impossible;cases impossible)⟩
end Itasca.Runtime.Theorems

end
