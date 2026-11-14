import Itasca.Runtime.Interp.State.StatefulTableSetSlots
import Itasca.Runtime.Interp.State.StatefulIntegerOperands
import Itasca.Runtime.Interp.State.StatefulSegmentLookup
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered

/-!
Sections, each formerly its own module: TableSetDispatch, TableSetStep.
-/

/-! ## TableSetDispatch -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_table_set_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (C : context)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (index : Nat)
    (first second a b entry : U32)
    (signature : SourceMachine.Stateful.Signature C (.tableSet index) input output)
    (bindings : SourceMachine.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Compiler.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Compiler.valueType value))
    (position : first.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (secondSlot : second.val=first.val+1) (arguments : Compiler.StatefulArguments (.tableSet index) a b) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Compiler.statefulInstruction (.tableSet index) first second a entry) ⦃ out =>
      out.2.1=exec ∧ out.2.2.2=platform ∧ output=[] ∧ FrameStoreMetadata store out.2.2.1 ∧
      ((out.1=.Ok () ∧ (∃ address object value,store.tables.val[address.index.val]?=some object ∧ TableMutation store out.2.2.1 address object value ∧ val_ref (decodeRef object.ty value)∈f.vals) ∧
        FrameSlots out.2.1 raw {f with code:=after,vals:=front} ∧
        SourceMachine.Stateful.Transition state f rest after (.tableSet index)
          (SourceMachine.advance {state with store:=decodeStore view code out.2.2.1} {f with code:=after,vals:=front} rest)) ∨
      (out.1=.Err (.Trap .TableOutOfBounds) ∧ out.2.2.1=store ∧
        SourceMachine.Stateful.Transition state f rest after (.tableSet index) .trap)) ⦄ := by
  cases signature with
  | tableSet index type limits selected =>
    obtain ⟨x,y,rfl,xType,yType⟩ := two_operand_values operandTypes
    have xTyped := typed x (by simp)
    have yTyped := typed y (by simp)
    rw [xType] at xTyped
    rw [yType] at yTyped
    obtain ⟨bits,rfl,bitsBound⟩ := SourceMachine.integer_val_inv (ty:=.I32) xTyped
    obtain ⟨reference,rfl,referenceTyped⟩ := SourceMachine.Stateful.reference_operand yTyped
    let value : U32 := UScalar.ofNatCore bits (by change bits<2^32;exact bitsBound)
    have valueEq : value.val=bits := rfl
    obtain ⟨address,object,mapped,issued,objectType⟩ := table_binding_raw view code store inst C index _ bindings selected
    change decodeElemType object.ty=type at objectType
    have indexEq : a.val=index := arguments.1
    rw [←indexEq] at mapped
    have referenceEq := frame_reference_second (first:=first) (second:=second) (type:=object.ty) slots values (by rfl)
      (by simpa only [objectType] using yType) position secondSlot
    have actualValues : f.vals=front++[SourceMachine.integerVal .I32 value.val,val_ref (decodeRef object.ty exec.slots.val[raw.base.val+second.val]!)] := by
      rw [valueEq,←referenceEq]
      exact values
    obtain ⟨out,run,same,metadata,effect⟩ := WP.spec_imp_exists
      (table_set_slots memory view code exec store raw first second a inst address object value
        state f rest after front found mapped issued slots position secondSlot sourceStore moduleEq actualValues)
    simp only [Compiler.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    refine ⟨same,rfl,trivial,metadata,?_⟩
    split at effect
    · exact Or.inl ⟨effect.1,⟨address,object,_,issued,effect.2.1,by rw [actualValues];simp⟩,effect.2.2.1,by simpa only [indexEq] using effect.2.2.2⟩
    · obtain ⟨exactOut,transition⟩ := effect
      rw [exactOut]
      exact Or.inr ⟨rfl,rfl,by simpa only [indexEq] using transition⟩
end Itasca.Runtime.Integration

end

/-! ## TableSetStep -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_table_set_point_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
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
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (decodeStore view code store) raw {f with code:=(SourceMachine.Stateful.Instruction.tableSet table).source::after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableSet table).source::after}::rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableSet table).source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      Machine.FramePoint (decodeStore view code store) {raw with pc:=target} {f with code:=(SourceMachine.Stateful.Instruction.tableSet table).source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2=platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ((∃ pc : U32,∃ front : List val,
        out.1=.Ok () ∧ pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
        (∃ address object value,store.tables.val[address.index.val]?=some object ∧ TableMutation store out.2.2.1 address object value ∧ val_ref (decodeRef object.ty value)∈f.vals) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=front} ∧
        Machine.FramePoint (decodeStore view code out.2.2.1) {raw with pc:=pc} {f with code:=after,vals:=front} compiled C targets next output ∧
        SourceMachine.Cumulative.Step initial (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .TableOutOfBounds) ∧ out.2.2.1=store ∧
        (∃ pc : U32,pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}}) ∧
        SourceMachine.Cumulative.Step initial .trap)) ⦄ := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (decodeStore view code store) {f with code:=(SourceMachine.Stateful.Instruction.tableSet table).source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f (.tableSet table) after frameTyped point.code with jump | operation
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
    let initial : SourceMachine.AState := ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableSet table).source::after}::rest,[]⟩
    obtain ⟨out,run,same,samePlatform,resultNil,metadata,effect⟩ := WP.spec_imp_exists
      (stateful_table_set_dispatch memory hooks floats allocator view code advanced store platform index raw inst C initial
        {f with code:=(SourceMachine.Stateful.Instruction.tableSet table).source::after} rest after front operands input result table first second a b entry signature
        bindings found rfl moduleEq slots values operandTypes operandTyped actualPosition (secondSlot (by simp [SourceMachine.Stateful.Instruction.arity])) arguments)
    rw [run]
    apply WP.spec.ret
    refine ⟨samePlatform,metadata,?_⟩
    rcases effect with ⟨success,mutation,represented,transition⟩ | ⟨error,sameStore,transition⟩
    · refine Or.inl ⟨pc,front,success,pcNext,same,mutation,represented,?_,?_⟩
      · have safe := SourceMachine.Stateful.transition_next (.tableSet table) (decodeStore view code store) ambient f rest after
          ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩ typed transition
        have continued := point.continue safe.2.1 front operands [] after values heights (by simpa only [resultNil,List.map_nil] using tail) pc pcNext
        simpa only [List.append_nil] using continued
      · exact .stateful transition (by intro impossible;cases impossible)
    · exact Or.inr ⟨error,sameStore,⟨pc,pcNext,same⟩,.stateful transition (by intro impossible;cases impossible)⟩
end Itasca.Runtime.Integration

end
