import Itasca.Runtime.Interp.State.StatefulTableSetSlots
import Itasca.Runtime.Interp.State.StatefulOperandValues
import Itasca.Runtime.Interp.State.StatefulLookup
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
