import Itasca.Runtime.Integration.Api.StatefulGrowthSlots
import Itasca.Runtime.Interp.State.StatefulOperandValues
import Itasca.Runtime.Interp.State.StatefulLookup
import Itasca.Runtime.Interp.State.StatefulContinue
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission

/-!
Table growth dispatch and structured execution. Shared growth-slot adapters and handler effects remain below both memory and table growth constructions.
-/

/-! ## Stateful Table Grow Dispatch -/

section

namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_table_grow_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (C : context)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (index : Nat) (first second a b entry : U32)
    (signature : Abs.Stateful.Signature C (.tableGrow index) input output)
    (bindings : Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (sizes : ∀ object∈store.tables.val,object.elements.length≤U32.max)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Code.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Code.valueType value))
    (position : first.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (arguments : Code.StatefulArguments (.tableGrow index) a b) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.statefulInstruction (.tableGrow index) first second a entry) ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ output=[.I32] ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ result : U32,
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+first.val) (UScalar.cast .U64 result)) ∧
      (∃ address object delta reference,store.tables.val[address.val]?=some object ∧
        TableGrowth store address delta reference (result,out.2.2.1) ∧ val_ref (decodeRef object.ty reference)∈f.vals) ∧
      FrameSlots out.2.1 raw {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} ∧
      Abs.Stateful.Transition state f rest after (.tableGrow index)
        (Abs.advance {state with store:=decodeStore view code out.2.2.1}
          {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} rest) ⦄ := by
  cases signature with
  | tableGrow index type limits selected =>
    obtain ⟨x,y,rfl,xType,yType⟩ := two_operand_values operandTypes
    have xTyped := typed x (by simp)
    have yTyped := typed y (by simp)
    rw [xType] at xTyped
    rw [yType] at yTyped
    obtain ⟨reference,rfl,referenceTyped⟩ := Abs.Stateful.reference_operand xTyped
    obtain ⟨bits,rfl,bitsBound⟩ := Abs.integer_val_inv (ty:=.I32) yTyped
    let delta : U32 := UScalar.ofNatCore bits (by change bits<2^32;exact bitsBound)
    let amount := UScalar.cast .U64 delta
    have amountValue : amount.val=bits := by simp [amount,delta]
    have deltaValue : (UScalar.cast .U32 amount).val=bits := by simp [amount,delta];exact bitsBound
    obtain ⟨address,object,mapped,issued,objectType⟩ := table_binding_raw view code store inst C index _ bindings selected
    change decodeElemType object.ty=type at objectType
    have indexEq : a.val=index := arguments.1
    rw [←indexEq] at mapped
    obtain ⟨referenceBits,referenceEncoded⟩ := reference_encoding reference
    have encoded : Code.encodeValues [val_ref reference,Abs.integerVal .I32 bits]=[referenceBits,bits] := by
      simp only [Code.encodeValues,List.flatMap_cons,List.flatMap_nil,List.append_nil,referenceEncoded]
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
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨success,rfl,trivial,metadata,result,written,⟨address.index,object,_,_,issued,growth,by rw [←referenceEq,values];simp⟩,represented,by simpa only [indexEq] using transition⟩
end Itasca.Runtime.Theorems

end

/-! ## Stateful Table Grow Step -/

section

namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_table_grow_point_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [projection : Itasca.Runtime.Interp.StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (table : Nat)
    (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (fetchBound : compiled.code.length≤U32.max)
    (sizes : ∀ object∈store.tables.val,object.elements.length≤U32.max)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint (decodeStore view code store) raw {f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after}::rest,[]⟩) :
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      StructuredMachine.FramePoint (decodeStore view code store) {raw with pc:=target} {f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ pc : U32,∃ front : List val,∃ position : Nat,∃ result : U32,
        pc.val=raw.pc.val+1 ∧ raw.base.val≤position ∧ position<exec.slots.length ∧
        SlotsEffect {exec with frames:=exec.frames.set index {raw with pc:=pc}} out.2.1 (exec.slots.val.set position (UScalar.cast .U64 result)) ∧
        (∃ address object delta reference,store.tables.val[address.val]?=some object ∧ TableGrowth store address delta reference (result,out.2.2.1) ∧ val_ref (decodeRef object.ty reference)∈f.vals) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} ∧
        StructuredMachine.FramePoint (decodeStore view code out.2.2.1) {raw with pc:=pc} {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} compiled C targets next output ∧
        Abs.Cumulative.Step initial (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]}::rest,[]⟩) ⦄ := by
  dsimp only
  have frameTyped : Abs.FrameTyped (decodeStore view code store) {f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f (.tableGrow table) after frameTyped point.code with jump | operation
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
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after}::rest,[]⟩
    obtain ⟨out,run,success,samePlatform,resultType,metadata,resultValue,written,mutation,represented,transition⟩ := WP.spec_imp_exists
      (stateful_table_grow_dispatch memory hooks floats allocator allocation view code advanced store platform index raw inst C initial
        {f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after} rest after front operands input result table first second a b entry signature
        bindings found sizes rfl moduleEq slots values operandTypes operandTyped actualPosition arguments)
    rw [run]
    apply WP.spec.ret
    have operandLength : operands.length≥1 := by
      have equal := congrArg List.length operandTypes
      rw [List.length_map,signature.input_length] at equal
      cases signature <;> simp_all [Abs.Stateful.Instruction.arity]
    have capacity : raw.base.val+first.val<exec.slots.length := by
      have allScalar := signature.inputs_scalar
      have live := slots
      have enough : Code.encodeValues operands ≠ [] := by
        intro empty
        have lengthEq := congrArg List.length empty
        rw [Code.encodeValues_length,operandTypes] at lengthEq
        cases signature <;> simp [Code.slots,Code.width] at lengthEq
      have words := frame_read_suffix slots values actualPosition rfl
      have firstWord := words 0 (List.length_pos_iff.mpr enough)
      simpa only [Nat.add_zero] using firstWord.1
    refine ⟨success,samePlatform,metadata,pc,front,raw.base.val+first.val,resultValue,pcNext,Nat.le_add_right _ _,capacity,written,mutation,represented,?_,?_⟩
    · have safe := Abs.Stateful.transition_next (.tableGrow table) (decodeStore view code store) ambient f rest after
        ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front++[Abs.integerVal .I32 resultValue.val]}::rest,[]⟩ typed transition
      exact point.continue safe.2.1 front operands [Abs.integerVal .I32 resultValue.val] after values heights
        (by simpa only [resultType,Code.valueType,Abs.integerVal,List.map_cons,List.map_nil,numtype_Inn,valtype_numtype] using tail) pc pcNext
    · exact .stateful transition (by intro impossible;cases impossible)
end Itasca.Runtime.Theorems

end
