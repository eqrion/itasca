import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.SourceMachine.Stateful.Transition
import Itasca.Runtime.Compiler.Local.Capacity.OperandBounds
import Itasca.Runtime.Interp.State.StatefulLookup
import Itasca.Runtime.Interp.State.StatefulReferenceValue
import Itasca.Runtime.Interp.State.StatefulContinue
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission

/-!
Read-only store/reference instruction dispatch and structured step. Operand inversion, result slots and checked destination capacity establish the point-step correspondence.
-/

/-! ## Stateful Capacity -/

section

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std Itasca.ResultFacts

private theorem first_checked (first second : Result Bool)
    (checked : (do let b ← first; if b then second else .ok false) = .ok true) : first=.ok true := by
  obtain ⟨value,run,checked⟩ := bind_ok_inv _ _ _ checked
  cases value with
  | false => simp at checked
  | true => exact run

theorem read_valid_capacity (compiled : runtime.bytecode.CompiledFunction)
    (op : Abs.Stateful.Instruction) (first second a entry : U32)
    (readOnly : op.readOnly=true)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled (Code.statefulInstruction op first second a entry)=.ok true) :
    first.val<compiled.slot_count.val := by
  cases op <;> simp only [Abs.Stateful.Instruction.readOnly,Bool.false_eq_true] at readOnly
  all_goals
    simp only [Code.statefulInstruction,runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,
      runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,
      runtime.bytecode.Instr.simd,bind_ok] at checked
  all_goals first
    | (have bound := Code.slots_fit_true compiled first 1#u32 checked; scalar_tac)
    | (have bound := Code.slots_fit_true compiled first 1#u32 (first_checked _ _ checked); scalar_tac)
end Itasca.Runtime.Interp.Stateful

end

/-! ## Stateful Read Dispatch -/

section

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store

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
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (C : context)
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
    obtain ⟨out,run,effect⟩ := WP.spec_imp_exists (ref_null_slots exec raw first rawType state f rest after slots position capacity)
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
      (ref_func_slots memory exec store raw first a inst address state f rest after found mapped issued slots position capacity moduleEq)
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
      (ref_is_null_value_slots exec raw first rawType state f rest after front reference slots values (by simpa only [typeEq] using valueType) position)
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
      (table_get_slots memory view code exec store raw first a inst address object state f rest after front positionValue found mapped issued slots (by simpa only [bitsEq] using values) position sourceStore moduleEq)
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
      (table_size_slots memory view code exec store raw first a inst address object state f rest after found mapped issued slots position capacity sourceStore moduleEq)
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,Or.inl ⟨[Abs.integerVal .I32 object.elements.length],_,success,rfl,written,represented,by simpa only [indexEq] using transition⟩⟩
  case memorySize type selected =>
    have operandsNil := empty_operands operandTypes
    subst operands
    simp only [List.append_nil] at values
    subst front
    obtain ⟨address,object,mapped,issued⟩ := memory_binding_raw view code store inst C type bindings selected
    obtain ⟨out,run,success,same,pages,pagesEq,written,represented,transition⟩ := WP.spec_imp_exists
      (memory_size_slots memory view laws code exec store raw first inst address object state f rest after found mapped issued slots position capacity sourceStore moduleEq)
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,Or.inl ⟨[Abs.integerVal .I32 pages.val],_,success,rfl,written,represented,transition⟩⟩
end Itasca.Runtime.Interp.Stateful

end

/-! ## Stateful Read Step -/

section

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec

theorem read_point_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [projection : Itasca.Runtime.Interp.StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (op : Abs.Stateful.Instruction)
    (readOnly : op.readOnly=true) (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled=.ok true)
    (fetchBound : compiled.code.length≤U32.max)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint (decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩) :
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      StructuredMachine.FramePoint (decodeStore view code store) {raw with pc:=target} {f with code:=op.source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1=store ∧ out.2.2.2=platform ∧
      ((∃ pc : U32,∃ produced : List val,∃ position : Nat,∃ word : U64,
        out.1=.Ok () ∧ pc.val=raw.pc.val+1 ∧ raw.base.val≤position ∧ position<exec.slots.length ∧
        SlotsEffect {exec with frames:=exec.frames.set index {raw with pc:=pc}} out.2.1 (exec.slots.val.set position word) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=produced} ∧
        StructuredMachine.FramePoint (decodeStore view code store) {raw with pc:=pc} {f with code:=after,vals:=produced} compiled C targets next output ∧
        Abs.Cumulative.Step initial (.next ⟨decodeStore view code store,ambient,{f with code:=after,vals:=produced}::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .TableOutOfBounds) ∧
        (∃ pc : U32,pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}}) ∧
        Abs.Cumulative.Step initial .trap)) ⦄ := by
  dsimp only
  have frameTyped : Abs.FrameTyped (decodeStore view code store) {f with code:=op.source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f op after frameTyped point.code with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,operands,input,result,first,second,a,b,entry,values,operandTypes,signature,heights,operandTyped,position,secondSlot,arguments,pair,fetch,tail⟩ := operation
    have bounded := read_valid_capacity compiled op first second a entry readOnly (Code.well_formed_fetched compiled checked raw.pc.val _ fetch)
    have capacity : raw.base.val+first.val<exec.slots.length := by omega
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
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩
    obtain ⟨out,run,sameStore,samePlatform,effect⟩ := WP.spec_imp_exists
      (read_dispatch memory hooks floats allocator view laws code advanced store platform index raw inst C initial
        {f with code:=op.source::after} rest after front operands input result op first second a b entry readOnly signature
        bindings found rfl moduleEq slots values operandTypes operandTyped actualPosition capacity arguments)
    rw [run]
    apply WP.spec.ret
    refine ⟨sameStore,samePlatform,?_⟩
    rcases effect with ⟨produced,word,success,producedTypes,written,represented,transition⟩ | ⟨error,same,transition⟩
    · refine Or.inl ⟨pc,front++produced,raw.base.val+first.val,word,success,pcNext,Nat.le_add_right _ _,capacity,written,represented,?_,?_⟩
      · apply point.continue (extend_store_refl _ typed.typed.store) front operands produced after values heights _ pc pcNext
        simpa only [producedTypes] using tail
      · exact .stateful transition (by intro impossible; cases impossible)
    · exact Or.inr ⟨error,⟨pc,pcNext,same⟩,.stateful transition (by intro impossible; cases impossible)⟩
end Itasca.Runtime.Interp.Stateful

end
