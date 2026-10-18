import Exec.Theorems.Api.StatefulGrowthSlots
import Exec.Interp.State.StatefulOperandValues
import Exec.Interp.State.StatefulLookup
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp Exec.Interp.Stateful

theorem stateful_table_grow_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.Instance) (C : context)
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
      (stateful_table_grow_slots memory hooks floats allocator allocation view code exec store raw first a inst address object referenceWord amount
        state f rest after front found mapped issued referenceSlot amountSlot sizes sourceStore moduleEq
        (by rw [←referenceEq,deltaValue];exact values) slots position)
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨success,rfl,trivial,metadata,result,written,⟨address.index,object,_,_,issued,growth,by rw [←referenceEq,values];simp⟩,represented,by simpa only [indexEq] using transition⟩
end Exec.Theorems
