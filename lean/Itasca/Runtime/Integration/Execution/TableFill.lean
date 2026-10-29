import Itasca.Runtime.Integration.Execution.Mutation.BulkResult
import Itasca.Runtime.Store.Api.TableFill
import Itasca.Runtime.Interp.State.StatefulIntegerOperands
import Itasca.Runtime.Interp.State.StatefulLookup
import Itasca.Runtime.Store.Initialization.SegmentStep
import Itasca.Runtime.Interp.State.StatefulContinue
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission

/-!
TableFill correspondence from store handler through dispatch to structured execution. Retains mutation, source-step and bounds-trap obligations for the bulk-operation execution theorem.
-/

/-! ## Stateful Table Fill -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem stateful_table_fill_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand tableId : U32) (inst : runtime.store.ModuleInst) (address : runtime.TableAddr)
    (object : runtime.store.TableInst) (destination value count : U64)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.tables.val[tableId.val]? = some address) (target : store.tables.val[address.index.val]? = some object)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (valueSlot : slots.val[base.val+operand.val+1]? = some value)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[SourceMachine.integerVal .I32 (bulkWord destination).val,
      val_ref (decodeRef object.ty value),SourceMachine.integerVal .I32 (bulkWord count).val]) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.TableFill operand tableId) ⦃ out =>
      TableFillEffect store address.index object (bulkWord destination) value (bulkWord count) out ∧
      FrameStoreMetadata store out.2 ∧
      SourceMachine.Stateful.Transition state f rest after (.tableFill tableId.val)
        (statefulBulkResult view code state f rest after front out) ⦄ := by
  apply WP.spec_mono (bulk_table_fill memory store instIndex function base slots operand tableId inst address object
    destination value count found mapped target destinationSlot valueSlot countSlot)
  intro out effect
  refine ⟨effect,?_⟩
  unfold TableFillEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨words,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult]
    rw [table_fill_decodes view code store inst f.toFrame tableId address object _ _ value words
      moduleEq mapped target filled]
    simp only [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.tableFill,values,SourceMachine.Stateful.pop_three_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,
      Option.map_some,bulk_integer_decoded,SourceMachine.Stateful.as_reference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at inside
    simp [
      decodeTable,bulk_integer_decoded,SourceMachine.Stateful.as_reference_value,inside,alloc.vec.Vec.length]
  · rename_i outside
    rw [effect]
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,{},trivial,?_⟩
    simp only [statefulBulkResult,SourceMachine.Stateful.evaluate,SourceMachine.Stateful.tableFill,values,SourceMachine.Stateful.pop_three_append]
    simp only [moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,target,
      Option.map_some,bulk_integer_decoded,SourceMachine.Stateful.as_reference_value]
    simp [bulkWord,Slice.length,alloc.vec.Vec.length] at outside
    simp [
      decodeTable,bulk_integer_decoded,SourceMachine.Stateful.as_reference_value,outside,alloc.vec.Vec.length]
end Itasca.Runtime.Integration

end

/-! ## Stateful Table Fill Dispatch -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_table_fill_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (C : context)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (index : Nat) (first second a b entry : U32)
    (signature : SourceMachine.Stateful.Signature C (.tableFill index) input output)
    (bindings : SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Compiler.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Compiler.valueType value))
    (position : first.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (arguments : Compiler.StatefulArguments (.tableFill index) a b) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Compiler.statefulInstruction (.tableFill index) first second a entry) ⦃ out =>
      out.2.1=exec ∧ out.2.2.2=platform ∧ output=[] ∧
      (∃ address : runtime.TableAddr,∃ object destination value count, store.tables.val[address.index.val]?=some object ∧ val_ref (decodeRef object.ty value)∈f.vals ∧
        TableFillEffect store address.index object destination value count (out.1,out.2.2.1)) ∧
      FrameStoreMetadata store out.2.2.1 ∧ FrameSlots out.2.1 raw {f with code:=after,vals:=front} ∧
      SourceMachine.Stateful.Transition state f rest after (.tableFill index)
        (statefulBulkResult view code state f rest after front (out.1,out.2.2.1)) ⦄ := by
  cases signature with
  | tableFill index type limits selected =>
    obtain ⟨x,y,z,rfl,xType,yType,zType⟩ := three_operand_values operandTypes
    have xTyped := typed x (by simp)
    have yTyped := typed y (by simp)
    have zTyped := typed z (by simp)
    rw [xType] at xTyped
    rw [yType] at yTyped
    rw [zType] at zTyped
    obtain ⟨destinationBits,rfl,destinationBound⟩ := SourceMachine.integer_val_inv (ty:=.I32) xTyped
    obtain ⟨reference,rfl,referenceTyped⟩ := SourceMachine.Stateful.reference_operand yTyped
    obtain ⟨countBits,rfl,countBound⟩ := SourceMachine.integer_val_inv (ty:=.I32) zTyped
    let destination : U32 := UScalar.ofNatCore destinationBits destinationBound
    let count : U32 := UScalar.ofNatCore countBits countBound
    obtain ⟨referenceBits,referenceEncoded⟩ := reference_encoding reference
    have encoded : Compiler.encodeValues [SourceMachine.integerVal .I32 destinationBits,val_ref reference,SourceMachine.integerVal .I32 countBits]=
        [destinationBits,referenceBits,countBits] := by
      simp only [Compiler.encodeValues,List.flatMap_cons,List.flatMap_nil,List.append_nil,referenceEncoded]
      rfl
    have destinationSlot := frame_read_scalar slots values position encoded 0 (by simp) (UScalar.cast .U64 destination) (by simp [destination])
    simp only [Nat.add_zero] at destinationSlot
    have countSlot := frame_read_scalar slots values position encoded 2 (by simp) (UScalar.cast .U64 count) (by simp [count])
    obtain ⟨valueBound,valueEq⟩ := frame_read_suffix_word slots values position encoded 1 (by simp)
    simp only [List.getElem!_cons_succ,List.getElem!_cons_zero] at valueEq
    let value := exec.slots.val[raw.base.val+first.val+1]!
    have valueSlot : exec.slots.val[raw.base.val+first.val+1]?=some value := by
      simp only [value,List.getElem?_eq_getElem valueBound,_root_.getElem!_pos exec.slots.val (raw.base.val+first.val+1) valueBound]
    obtain ⟨address,object,mapped,issued,objectType⟩ := table_binding_raw view code store inst C index _ bindings selected
    change decodeElemType object.ty=type at objectType
    have indexEq : a.val=index := arguments.1
    rw [←indexEq] at mapped
    have referenceEq : val_ref reference=val_ref (decodeRef object.ty value) :=
      reference_word_value _ _ _ (by simpa only [objectType] using yType) (by rw [valueEq];exact referenceEncoded)
    have normalized : f.vals=front++[SourceMachine.integerVal .I32 (bulkWord (UScalar.cast .U64 destination)).val,
        val_ref (decodeRef object.ty value),SourceMachine.integerVal .I32 (bulkWord (UScalar.cast .U64 count)).val] := by
      rw [←referenceEq]
      simpa [bulkWord,destination,count,Nat.mod_eq_of_lt (show destinationBits<4294967296 from destinationBound),Nat.mod_eq_of_lt (show countBits<4294967296 from countBound)] using values
    obtain ⟨out,run,same,effect,metadata,transition⟩ := WP.spec_imp_exists
      (segment_execute_bulk memory exec store raw.instance raw.function raw.base (.TableFill first a) _
        (stateful_table_fill_effect memory view code store raw.instance raw.function raw.base (alloc.vec.Vec.deref exec.slots)
          first a inst address object (UScalar.cast .U64 destination) value (UScalar.cast .U64 count)
          state f rest after front found mapped issued (by simpa [alloc.vec.Vec.deref] using destinationSlot)
          (by simpa [alloc.vec.Vec.deref] using valueSlot) (by simpa [alloc.vec.Vec.deref] using countSlot) sourceStore moduleEq normalized))
    simp only [Compiler.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,trivial,⟨address,object,_,_,_,issued,by rw [←referenceEq,values];simp,effect⟩,metadata,
      by rw [same];exact frame_consume after slots values,by simpa only [indexEq] using transition⟩
end Itasca.Runtime.Integration

end

/-! ## Stateful Table Fill Step -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_table_fill_point_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [projection : Itasca.Runtime.Interp.Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (tableIndex : Nat)
    (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (fetchBound : compiled.code.length≤U32.max)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (decodeStore view code store) raw {f with code:=(SourceMachine.Stateful.Instruction.tableFill tableIndex).source::after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableFill tableIndex).source::after}::rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableFill tableIndex).source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      Machine.FramePoint (decodeStore view code store) {raw with pc:=target} {f with code:=(SourceMachine.Stateful.Instruction.tableFill tableIndex).source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2=platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ((∃ pc : U32,∃ front : List val,
        out.1=.Ok () ∧ pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
        (∃ address : runtime.TableAddr,∃ object destination source count,store.tables.val[address.index.val]?=some object ∧ val_ref (decodeRef object.ty source)∈f.vals ∧ TableFillEffect store address.index object destination source count (out.1,out.2.2.1)) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=front} ∧
        Machine.FramePoint (decodeStore view code out.2.2.1) {raw with pc:=pc} {f with code:=after,vals:=front} compiled C targets next output ∧
        SourceMachine.Cumulative.Step initial (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .TableOutOfBounds) ∧ out.2.2.1=store ∧
        (∃ pc : U32,pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}}) ∧
        SourceMachine.Cumulative.Step initial .trap)) ⦄ := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (decodeStore view code store) {f with code:=(SourceMachine.Stateful.Instruction.tableFill tableIndex).source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f (.tableFill tableIndex) after frameTyped point.code with jump | operation
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
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableFill tableIndex).source::after}::rest,[]⟩
    obtain ⟨out,run,same,samePlatform,resultNil,rawEffect,metadata,represented,transition⟩ := WP.spec_imp_exists
      (stateful_table_fill_dispatch memory hooks floats allocator view code advanced store platform index raw inst C initial
        {f with code:=(SourceMachine.Stateful.Instruction.tableFill tableIndex).source::after} rest after front operands input result tableIndex first second a b entry signature
        bindings found rfl moduleEq slots values operandTypes operandTyped actualPosition arguments)
    rw [run]
    apply WP.spec.ret
    refine ⟨samePlatform,metadata,?_⟩
    obtain ⟨address,object,destination,source,count,issued,member,effect⟩ := rawEffect
    have classified := (effect.mutation store address object destination source count _).2
    rcases classified with ⟨success,mutation⟩ | ⟨error,sameStore⟩
    · change out.1=.Ok () at success
      have sourceStep : SourceMachine.Stateful.Transition initial {f with code:=(SourceMachine.Stateful.Instruction.tableFill tableIndex).source::after} rest after (.tableFill tableIndex)
          (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩) := by
        simpa [statefulBulkResult,success,initial,SourceMachine.advance] using transition
      refine Or.inl ⟨pc,front,success,pcNext,same,⟨address,object,destination,source,count,issued,member,effect⟩,represented,?_,?_⟩
      · have safe := SourceMachine.Stateful.transition_next (.tableFill tableIndex) (decodeStore view code store) ambient {f with code:=(SourceMachine.Stateful.Instruction.tableFill tableIndex).source::after} rest after
          ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩ typed sourceStep
        have continued := point.continue safe.2.1 front operands [] after values heights (by simpa only [resultNil,List.map_nil] using tail) pc pcNext
        simpa only [List.append_nil] using continued
      · exact .stateful sourceStep (by intro impossible;cases impossible)
    · change out.1=.Err (.Trap .TableOutOfBounds) at error
      have sourceStep : SourceMachine.Stateful.Transition initial {f with code:=(SourceMachine.Stateful.Instruction.tableFill tableIndex).source::after} rest after (.tableFill tableIndex) .trap := by
        simpa [statefulBulkResult,error] using transition
      exact Or.inr ⟨error,sameStore,⟨pc,pcNext,same⟩,.stateful sourceStep (by intro impossible;cases impossible)⟩
end Itasca.Runtime.Integration

end
