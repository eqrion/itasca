import Itasca.Runtime.Integration.Api.StatefulGrowthSlots
import Itasca.Runtime.Interp.State.StatefulOperandValues
import Itasca.Runtime.Interp.State.StatefulLookup
import Itasca.Runtime.Interp.State.StatefulContinue
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission

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
