import Exec.Theorems.Api.StatefulGrowthSlots
import Exec.Interp.State.StatefulOperandValues
import Exec.Interp.State.StatefulLookup
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp Exec.Interp.Stateful

theorem stateful_memory_grow_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (C : context)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (first second a entry : U32)
    (signature : Abs.Stateful.Signature C .memoryGrow input output)
    (bindings : Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (shapes : ∀ object∈store.memories.val,MemoryShape view object)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Code.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Code.valueType value))
    (position : first.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType)) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.statefulInstruction .memoryGrow first second a entry) ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ output=[.I32] ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ result : U32,
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+first.val) (UScalar.cast .U64 result)) ∧
      (∃ address delta,address.val<store.memories.length ∧ MemoryGrowth view code store address delta (result,out.2.2.1)) ∧
      FrameSlots out.2.1 raw {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} ∧
      Abs.Stateful.Transition state f rest after .memoryGrow
        (Abs.advance {state with store:=decodeStore view code out.2.2.1}
          {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} rest) ⦄ := by
  cases signature with
  | memoryGrow type selected =>
    obtain ⟨value,rfl⟩ := List.length_eq_one_iff.mp (by simpa only [List.length_map,List.length_singleton] using congrArg List.length operandTypes)
    have valueType : Code.valueType value=.I32 := by simpa using operandTypes
    have valueTyped := typed value (by simp)
    rw [valueType] at valueTyped
    obtain ⟨bits,rfl,bitsBound⟩ := Abs.integer_val_inv (ty:=.I32) valueTyped
    let delta : U32 := UScalar.ofNatCore bits (by change bits<2^32;exact bitsBound)
    let amount := UScalar.cast .U64 delta
    have amountValue : amount.val=bits := by simp [amount,delta]
    have deltaValue : (UScalar.cast .U32 amount).val=bits := by simp [amount,delta];exact bitsBound
    have encoded : Code.encodeValues [Abs.integerVal .I32 bits]=[bits] := rfl
    have amountSlot := frame_read_scalar slots values position encoded 0 (by simp) amount (by simpa using amountValue)
    simp only [Nat.add_zero] at amountSlot
    obtain ⟨address,object,mapped,issued⟩ := memory_binding_raw view code store inst C type bindings selected
    obtain ⟨out,run,success,metadata,result,written,growth,represented,transition⟩ := WP.spec_imp_exists
      (stateful_memory_grow_slots memory view laws code exec store raw first inst address object amount
        state f rest after front found mapped issued amountSlot shapes sourceStore moduleEq
        (by simpa only [deltaValue] using values) slots position)
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨success,rfl,trivial,metadata,result,written,⟨address.index,_,(List.getElem?_eq_some_iff.mp issued).1,growth⟩,represented,transition⟩
end Exec.Theorems
