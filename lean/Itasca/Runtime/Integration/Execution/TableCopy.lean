import Itasca.Runtime.Integration.Execution.Mutation.BulkResult
import Itasca.Runtime.Store.Api.TableCopy
import Itasca.Runtime.Interp.State.StatefulIntegerOperands
import Itasca.Runtime.Interp.State.StatefulLookup
import Itasca.Runtime.Store.Initialization.SegmentStep
import Itasca.Runtime.Interp.State.StatefulSegmentLookup
import Itasca.Runtime.Interp.State.StatefulContinue
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission

/-!
TableCopy correspondence from store handler through dispatch to structured execution. Retains mutation, source-step and bounds-trap obligations for the bulk-operation execution theorem.
-/

/-! ## Stateful Table Copy -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem stateful_table_copy_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand entry tableId sourceId : U32) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) (address sourceAddress : runtime.TableAddr)
    (object sourceObject : runtime.store.TableInst) (destination source count : U64)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some compiled)
    (descriptor : compiled.indirect.val[entry.val]? = some (tableId,sourceId))
    (sourceMapped : inst.tables.val[sourceId.val]? = some sourceAddress)
    (sourceFound : store.tables.val[sourceAddress.index.val]? = some sourceObject)
    (sameType : sourceObject.ty=object.ty)
    (mapped : inst.tables.val[tableId.val]? = some address) (target : store.tables.val[address.index.val]? = some object)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (sources : f.vals = front++[SourceMachine.integerVal .I32 (bulkWord destination).val,
      SourceMachine.integerVal .I32 (bulkWord source).val,SourceMachine.integerVal .I32 (bulkWord count).val]) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.TableCopy operand entry) ⦃ out =>
      TableCopyEffect store address.index object sourceObject (bulkWord destination) (bulkWord source) (bulkWord count) out ∧
      FrameStoreMetadata store out.2 ∧
      SourceMachine.Stateful.Transition state f rest after (.tableCopy tableId.val sourceId.val)
        (statefulBulkResult view code state f rest after front out) ⦄ := by
  apply WP.spec_mono (bulk_table_copy memory store instIndex function base slots inst compiled operand entry tableId sourceId
    sourceAddress address object sourceObject destination source count found functionFound descriptor sourceMapped sourceFound
    mapped target destinationSlot sourceSlot countSlot)
  intro out effect
  refine ⟨effect,?_⟩
  unfold TableCopyEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨words,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult]
    rw [table_copy_decodes view code store inst f.toFrame tableId sourceId address sourceAddress object sourceObject _ _ _ words
      moduleEq mapped sourceMapped target sourceFound sameType ⟨inside.2,inside.1⟩ filled]
    simp only [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.tableCopy,sources,SourceMachine.Stateful.pop_three_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,sourceMapped,sourceFound,
      Option.map_some,bulk_integer_decoded,SourceMachine.Stateful.as_reference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at inside
    simp [
      decodeTable,bulk_integer_decoded,SourceMachine.Stateful.as_reference_value,inside,And.comm,alloc.vec.Vec.length]
  · rename_i outside
    rw [effect]
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult,SourceMachine.Stateful.evaluate,SourceMachine.Stateful.tableCopy,sources,SourceMachine.Stateful.pop_three_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,sourceMapped,sourceFound,
      Option.map_some,bulk_integer_decoded,SourceMachine.Stateful.as_reference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at outside
    simp [
      decodeTable,bulk_integer_decoded,SourceMachine.Stateful.as_reference_value,outside,And.comm,alloc.vec.Vec.length]
    intro destinationFits sourceFits
    have impossible := outside destinationFits
    omega
end Itasca.Runtime.Integration

end

/-! ## Stateful Table Copy Dispatch -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_table_copy_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (tableIndex sourceIndex : Nat) (first second a b entry : U32)
    (signature : SourceMachine.Stateful.Signature C (.tableCopy tableIndex sourceIndex) input output)
    (bindings : SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (functionFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Compiler.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Compiler.valueType value))
    (position : first.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (arguments : Compiler.StatefulArguments (.tableCopy tableIndex sourceIndex) a b)
    (pair : Compiler.StatefulPair compiled.indirect.val (.tableCopy tableIndex sourceIndex) a b entry) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Compiler.statefulInstruction (.tableCopy tableIndex sourceIndex) first second a entry) ⦃ out =>
      out.2.1=exec ∧ out.2.2.2=platform ∧ output=[] ∧
      (∃ address sourceAddress : runtime.TableAddr,∃ object sourceObject destination source count, store.tables.val[address.index.val]?=some object ∧
        store.tables.val[sourceAddress.index.val]?=some sourceObject ∧ sourceObject.ty=object.ty ∧
        TableCopyEffect store address.index object sourceObject destination source count (out.1,out.2.2.1)) ∧
      FrameStoreMetadata store out.2.2.1 ∧ FrameSlots out.2.1 raw {f with code:=after,vals:=front} ∧
      SourceMachine.Stateful.Transition state f rest after (.tableCopy tableIndex sourceIndex)
        (statefulBulkResult view code state f rest after front (out.1,out.2.2.1)) ⦄ := by
  cases signature with
  | tableCopy tableIndex sourceIndex type limits sourceLimits selected sourceSelected =>
    obtain ⟨destination,source,count,rfl⟩ := three_i32_operands _ operands operandTypes typed
    obtain ⟨destinationSlot,sourceSlot,countSlot⟩ := frame_three_i32_slots destination source count slots values position
    obtain ⟨address,object,mapped,issued,objectType⟩ := table_binding_raw view code store inst C tableIndex _ bindings selected
    obtain ⟨sourceAddress,sourceObject,sourceMapped,sourceFound,sourceType⟩ := table_binding_raw view code store inst C sourceIndex _ bindings sourceSelected
    have sameType : sourceObject.ty=object.ty := decode_elem_type_injective (sourceType.trans objectType.symm)
    have tableEq : a.val=tableIndex := arguments.1
    have sourceEq : b.val=sourceIndex := arguments.2
    rw [←tableEq] at mapped
    rw [←sourceEq] at sourceMapped
    have normalized : f.vals=front++[SourceMachine.integerVal .I32 (bulkWord (UScalar.cast .U64 destination)).val,
        SourceMachine.integerVal .I32 (bulkWord (UScalar.cast .U64 source)).val,SourceMachine.integerVal .I32 (bulkWord (UScalar.cast .U64 count)).val] := by
      simpa [bulkWord] using values
    obtain ⟨out,run,same,effect,metadata,transition⟩ := WP.spec_imp_exists
      (segment_execute_bulk memory exec store raw.instance raw.function raw.base (.TableCopy first entry) _
        (stateful_table_copy_effect memory view code store raw.instance raw.function raw.base (alloc.vec.Vec.deref exec.slots)
          first entry a b inst compiled address sourceAddress object sourceObject (UScalar.cast .U64 destination) (UScalar.cast .U64 source) (UScalar.cast .U64 count)
          state f rest after front found functionFound pair sourceMapped sourceFound sameType mapped issued (by simpa [alloc.vec.Vec.deref] using destinationSlot) (by simpa [alloc.vec.Vec.deref] using sourceSlot) (by simpa [alloc.vec.Vec.deref] using countSlot) sourceStore moduleEq normalized))
    simp only [Compiler.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,trivial,⟨address,sourceAddress,object,sourceObject,_,_,_,issued,sourceFound,sameType,effect⟩,metadata,
      by rw [same];exact frame_consume after slots values,by simpa only [tableEq,sourceEq] using transition⟩
end Itasca.Runtime.Integration

end

/-! ## Stateful Table Copy Step -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_table_copy_point_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [projection : Itasca.Runtime.Interp.Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (tableIndex sourceIndex : Nat)
    (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (fetchBound : compiled.code.length≤U32.max)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (decodeStore view code store) raw {f with code:=(SourceMachine.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after}::rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      Machine.FramePoint (decodeStore view code store) {raw with pc:=target} {f with code:=(SourceMachine.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2=platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ((∃ pc : U32,∃ front : List val,
        out.1=.Ok () ∧ pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
        (∃ address sourceAddress : runtime.TableAddr,∃ object segment destination source count,store.tables.val[address.index.val]?=some object ∧ store.tables.val[sourceAddress.index.val]?=some segment ∧ segment.ty=object.ty ∧ TableCopyEffect store address.index object segment destination source count (out.1,out.2.2.1)) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=front} ∧
        Machine.FramePoint (decodeStore view code out.2.2.1) {raw with pc:=pc} {f with code:=after,vals:=front} compiled C targets next output ∧
        SourceMachine.Cumulative.Step initial (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .TableOutOfBounds) ∧ out.2.2.1=store ∧
        (∃ pc : U32,pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}}) ∧
        SourceMachine.Cumulative.Step initial .trap)) ⦄ := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (decodeStore view code store) {f with code:=(SourceMachine.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f (.tableCopy tableIndex sourceIndex) after frameTyped point.code with jump | operation
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
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after}::rest,[]⟩
    obtain ⟨out,run,same,samePlatform,resultNil,rawEffect,metadata,represented,transition⟩ := WP.spec_imp_exists
      (stateful_table_copy_dispatch memory hooks floats allocator view code advanced store platform index raw inst compiled C initial
        {f with code:=(SourceMachine.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} rest after front operands input result tableIndex sourceIndex first second a b entry signature
        bindings found codeFound rfl moduleEq slots values operandTypes operandTyped actualPosition arguments pair)
    rw [run]
    apply WP.spec.ret
    refine ⟨samePlatform,metadata,?_⟩
    obtain ⟨address,sourceAddress,object,segment,destination,source,count,issued,sourceFound,sameType,effect⟩ := rawEffect
    have classified : out.1=.Ok () ∨ (out.1=.Err (.Trap .TableOutOfBounds) ∧ out.2.2.1=store) := by
      unfold TableCopyEffect at effect
      split at effect
      · obtain ⟨buffer,equal,content⟩ := effect
        exact Or.inl (congrArg Prod.fst equal)
      · exact Or.inr ⟨congrArg Prod.fst effect,congrArg Prod.snd effect⟩
    rcases classified with success | ⟨error,sameStore⟩
    · change out.1=.Ok () at success
      have sourceStep : SourceMachine.Stateful.Transition initial {f with code:=(SourceMachine.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} rest after (.tableCopy tableIndex sourceIndex)
          (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩) := by
        simpa [statefulBulkResult,success,initial,SourceMachine.advance] using transition
      refine Or.inl ⟨pc,front,success,pcNext,same,⟨address,sourceAddress,object,segment,destination,source,count,issued,sourceFound,sameType,effect⟩,represented,?_,?_⟩
      · have safe := SourceMachine.Stateful.transition_next (.tableCopy tableIndex sourceIndex) (decodeStore view code store) ambient {f with code:=(SourceMachine.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} rest after
          ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩ typed sourceStep
        have continued := point.continue safe.2.1 front operands [] after values heights (by simpa only [resultNil,List.map_nil] using tail) pc pcNext
        simpa only [List.append_nil] using continued
      · exact .stateful sourceStep (by intro impossible;cases impossible)
    · change out.1=.Err (.Trap .TableOutOfBounds) at error
      have sourceStep : SourceMachine.Stateful.Transition initial {f with code:=(SourceMachine.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} rest after (.tableCopy tableIndex sourceIndex) .trap := by
        simpa [statefulBulkResult,error] using transition
      exact Or.inr ⟨error,sameStore,⟨pc,pcNext,same⟩,.stateful sourceStep (by intro impossible;cases impossible)⟩
end Itasca.Runtime.Integration

end
