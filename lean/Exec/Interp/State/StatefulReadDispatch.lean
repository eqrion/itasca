import Exec.Interp.State.StatefulLookup
import Exec.Interp.State.StatefulReferenceValue
namespace Exec.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Exec.Store

def ReadResult (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (state : Abs.AState)
    (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (op : Abs.Stateful.Instruction) (output : List valtype) (first : U32)
    (status : core.result.Result Unit runtime.ExecError) (fresh : runtime.interp.Execution) : Prop :=
  (∃ produced word, status=.Ok () ∧ produced.map Code.valueType=output ∧
    SlotsEffect exec fresh (exec.slots.val.set (raw.base.val+first.val) word) ∧
    FrameSlots fresh raw {f with code:=after,vals:=front++produced} ∧
    Abs.Stateful.Transition state f rest after op (Abs.advance state {f with code:=after,vals:=front++produced} rest)) ∨
  (status=.Err (.Trap .TableOutOfBounds) ∧ fresh=exec ∧ Abs.Stateful.Transition state f rest after op .trap)

private theorem decode_reference_type (type : Itasca.types.ElemType) (word : U64) :
    Code.valueType (val_ref (decodeRef type word))=valtype_reftype (decodeElemType type) := by
  cases type <;> unfold decodeRef <;> split <;> rfl

private theorem empty_operands {operands : List val} (types : operands.map Code.valueType=[]) : operands=[] :=
  List.map_eq_nil_iff.mp types

private theorem one_operand {operands : List val} {type : valtype}
    (types : operands.map Code.valueType=[type]) : ∃ value,operands=[value] ∧ Code.valueType value=type := by
  obtain ⟨value,equal⟩ := List.length_eq_one_iff.mp (by simpa only [List.length_map,List.length_singleton] using congrArg List.length types)
  subst operands
  exact ⟨value,rfl,by simpa using types⟩

theorem read_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.Instance) (C : context)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (op : Abs.Stateful.Instruction)
    (first second a b entry : U32)
    (readOnly : op.readOnly=true) (signature : Abs.Stateful.Signature C op input output)
    (bindings : Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Code.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Code.valueType value))
    (position : first.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (capacity : raw.base.val+first.val<exec.slots.length) (arguments : Code.StatefulArguments op a b) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.statefulInstruction op first second a entry) ⦃ out =>
      out.2.2.1=store ∧ out.2.2.2=platform ∧ ReadResult exec raw state f rest after front op output first out.1 out.2.1 ⦄ := by
  cases signature <;> simp only [Abs.Stateful.Instruction.readOnly,Bool.false_eq_true] at readOnly
  case refNull type =>
    have operandsNil := empty_operands operandTypes
    subst operands
    simp only [List.append_nil] at values
    subst front
    let rawType := match type with | .FUNCREF => Itasca.types.ElemType.FuncRef | .EXTERNREF => .ExternRef
    have typeEq : decodeElemType rawType=type := by cases type <;> rfl
    obtain ⟨out,run,effect⟩ := WP.spec_imp_exists (ref_null_slots memory hooks floats allocator exec raw first rawType state f rest after slots position capacity)
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    refine ⟨rfl,rfl,Or.inl ⟨[.REF_NULL type],0#u64,effect.1,?_,effect.2.1,?_,?_⟩⟩
    · cases type <;> rfl
    · simpa only [typeEq] using effect.2.2.1
    · simpa only [typeEq] using effect.2.2.2
  case refFunc index type selected =>
    have operandsNil := empty_operands operandTypes
    subst operands
    simp only [List.append_nil] at values
    subst front
    have indexEq : a.val=index := arguments.1
    obtain ⟨address,mapped,issued⟩ := function_binding_raw view code store inst C index type bindings selected
    rw [←indexEq] at mapped
    obtain ⟨out,run,success,same,word,wordEq,written,represented,transition⟩ := WP.spec_imp_exists
      (ref_func_slots memory hooks floats allocator exec store raw first a inst address state f rest after found mapped issued slots position capacity moduleEq)
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,Or.inl ⟨[.REF_FUNC_ADDR address.index.val],word,success,rfl,written,represented,by simpa only [indexEq] using transition⟩⟩
  case refIsNull type =>
    obtain ⟨value,rfl,valueType⟩ := one_operand operandTypes
    have valueTyped := typed value (by simp)
    rw [valueType] at valueTyped
    obtain ⟨reference,rfl,referenceTyped⟩ := Abs.Stateful.reference_operand valueTyped
    let rawType := match type with | .FUNCREF => Itasca.types.ElemType.FuncRef | .EXTERNREF => .ExternRef
    have typeEq : decodeElemType rawType=type := by cases type <;> rfl
    obtain ⟨out,run,success,word,wordEq,written,represented,transition⟩ := WP.spec_imp_exists
      (ref_is_null_value_slots memory hooks floats allocator exec raw first rawType state f rest after front reference slots values (by simpa only [typeEq] using valueType) position)
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨rfl,rfl,Or.inl ⟨[Abs.integerVal .I32 word.val],word,success,rfl,written,represented,transition⟩⟩
  case tableGet index type limits selected =>
    obtain ⟨value,rfl,valueType⟩ := one_operand operandTypes
    have valueTyped := typed value (by simp)
    rw [valueType] at valueTyped
    obtain ⟨bits,rfl,bitsBound⟩ := Abs.integer_val_inv (ty := .I32) valueTyped
    let positionValue : U32 := UScalar.ofNatCore bits (by change bits<2^32; exact bitsBound)
    have bitsEq : positionValue.val=bits := rfl
    obtain ⟨address,object,mapped,issued,objectType⟩ := table_binding_raw view code store inst C index _ bindings selected
    have indexEq : a.val=index := arguments.1
    rw [←indexEq] at mapped
    obtain ⟨out,run,effect⟩ := WP.spec_imp_exists
      (table_get_slots memory hooks floats allocator view code exec store raw first a inst address object state f rest after front positionValue found mapped issued slots (by simpa only [bitsEq] using values) position sourceStore moduleEq)
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    split at effect
    · obtain ⟨success,same,written,represented,transition⟩ := effect
      refine ⟨same,rfl,Or.inl ⟨[val_ref (decodeRef object.ty object.elements.val[positionValue.val]!)],_,success,?_,written,represented,by simpa only [indexEq] using transition⟩⟩
      change [Code.valueType (val_ref (decodeRef object.ty object.elements.val[positionValue.val]!))]=[valtype_reftype type]
      change decodeElemType object.ty=type at objectType
      rw [←objectType]
      exact congrArg (fun type => [type]) (decode_reference_type object.ty _)
    · obtain ⟨same,transition⟩ := effect
      rw [same]
      exact ⟨rfl,rfl,Or.inr ⟨rfl,rfl,by simpa only [indexEq] using transition⟩⟩
  case tableSize index type selected =>
    have operandsNil := empty_operands operandTypes
    subst operands
    simp only [List.append_nil] at values
    subst front
    have indexEq : a.val=index := arguments.1
    obtain ⟨address,object,mapped,issued,objectType⟩ := table_binding_raw view code store inst C index type bindings selected
    rw [←indexEq] at mapped
    obtain ⟨out,run,success,same,written,represented,transition⟩ := WP.spec_imp_exists
      (table_size_slots memory hooks floats allocator view code exec store raw first a inst address object state f rest after found mapped issued slots position capacity sourceStore moduleEq)
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,Or.inl ⟨[Abs.integerVal .I32 object.elements.length],_,success,rfl,written,represented,by simpa only [indexEq] using transition⟩⟩
  case memorySize type selected =>
    have operandsNil := empty_operands operandTypes
    subst operands
    simp only [List.append_nil] at values
    subst front
    obtain ⟨address,object,mapped,issued⟩ := memory_binding_raw view code store inst C type bindings selected
    obtain ⟨out,run,success,same,pages,pagesEq,written,represented,transition⟩ := WP.spec_imp_exists
      (memory_size_slots memory hooks floats allocator view laws code exec store raw first inst address object state f rest after found mapped issued slots position capacity sourceStore moduleEq)
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,Or.inl ⟨[Abs.integerVal .I32 pages.val],_,success,rfl,written,represented,transition⟩⟩
end Exec.Interp.Stateful
