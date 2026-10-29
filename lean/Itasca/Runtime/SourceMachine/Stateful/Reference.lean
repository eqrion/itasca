import Itasca.Runtime.SourceMachine.Stateful.Continuation
import Itasca.Runtime.SourceMachine.Core.Simulation
import Itasca.Runtime.Spec.ReferenceFunction
namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def asReference : val → Option ref
  | .REF_NULL ty => some (.REF_NULL ty)
  | .REF_FUNC_ADDR address => some (.REF_FUNC_ADDR address)
  | .REF_HOST_ADDR address => some (.REF_HOST_ADDR address)
  | _ => none

@[simp] theorem as_reference_value (value : ref) : asReference (val_ref value) = some value := by
  cases value <;> rfl

def refNull (s : AState) (f : AFrame) (rest : List AFrame) (type : reftype) (after : List instr) : AResult :=
  advance s {f with code := after,vals := f.vals ++ [.REF_NULL type]} rest

def refFunc (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match f.module.FUNCS[index]? with
  | none => .stuck
  | some address => advance s {f with code := after,vals := f.vals ++ [.REF_FUNC_ADDR address]} rest

def refIsNull (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) : AResult :=
  match pop f.vals with
  | none => .stuck
  | some (front,value) => match asReference value with
    | none => .stuck
    | some reference => advance s {f with code := after, vals := front ++ [integerVal .I32 (Spec.referenceIsNull reference)]} rest

theorem ref_null_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (type : reftype) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .REF_NULL type :: after} :: rest,[]⟩) :
    ∃ next, refNull ⟨s,ambient,{f with code := .REF_NULL type :: after} :: rest,[]⟩ f rest type after = .next next ∧
      CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := .REF_NULL type :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .REF_NULL type :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation
  cases operandTypes
  have valueTyped : Val_ok s (.REF_NULL type) (valtype_reftype type) :=
    .reftype s (.REF_NULL type) type (.null s type typed.typed.store) typed.typed.store
  have freshFrame := continuation [.REF_NULL type] (.cons valueTyped .nil)
  have actualFrame : FrameTyped s {f with code := after,vals := f.vals ++ [.REF_NULL type]} [] := by
    simpa only [split,List.append_nil] using freshFrame
  refine ⟨_,rfl,⟨active_frame_preservation typed.typed actualFrame rfl,typed.contents⟩,Or.inl ⟨?_,?_⟩⟩
  · have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,AFrame.toFrame,List.map_cons,admininstr_instr]
    rw [decode_labels_move_values _ _ _ _ height]
    rfl
  · simp [administrativeMeasure]

theorem ref_func_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .REF_FUNC (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, refFunc ⟨s,ambient,{f with code := .REF_FUNC (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := .REF_FUNC (.mk_uN index) :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .REF_FUNC (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | ref_func _ _ functionType bound sourceType contextWf instructionWf =>
    cases operandTypes
    simp only [labelContext,proj_uN_0] at bound sourceType
    have mappedBound : index < f.module.FUNCS.length := by rw [bindings.funcs.length_eq]; exact bound
    obtain ⟨fn,found,fnType⟩ := bindings.funcs.get mappedBound bound
    simp only [List.get_eq_getElem] at found fnType
    let address := f.module.FUNCS[index]
    have mapped : f.module.FUNCS[index]? = some address := List.getElem?_eq_getElem mappedBound
    have issued : address < s.FUNCS.length := (List.getElem?_eq_some_iff.mp found).1
    have reference : Ref_ok s (.REF_FUNC_ADDR address) .FUNCREF := by
      apply Ref_ok.func s address (s.FUNCS[address]!).TYPE
      · exact .func s address _ issued rfl typed.typed.store (.externtype_case_0 _)
      · exact typed.typed.store
      · exact .externtype_case_0 _
    have valueTyped : Val_ok s (.REF_FUNC_ADDR address) .FUNCREF := .reftype s _ _ reference typed.typed.store
    have freshFrame := continuation [.REF_FUNC_ADDR address] (.cons valueTyped .nil)
    have actualFrame : FrameTyped s {f with code := after,vals := f.vals ++ [.REF_FUNC_ADDR address]} [] := by
      simpa only [split,List.append_nil] using freshFrame
    refine ⟨_,by simp only [refFunc,mapped,advance],
      ⟨active_frame_preservation typed.typed actualFrame rfl,typed.contents⟩,NextSim.single ?_⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
    have indexBound : index < 2^32 := by cases instructionWf <;> rename_i valid; cases valid <;> norm_num at * <;> omega
    have source := Spec.ref_func_step s f.toFrame index address typed.typed.store frameWf indexBound mapped
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    simpa [vals,admininstr_instr] using mutable_stack_simulation s s ambient f rest
      (.REF_FUNC (.mk_uN index)) after f.vals [] [.REF_FUNC_ADDR address] typed.typed.ambient labelsWf valuesWf tailWf restWf height source

private theorem reference_value {s : store} {value : val} {type : reftype}
    (typed : Val_ok s value (valtype_reftype type)) : ∃ reference, value = val_ref reference := by
  generalize equation : valtype_reftype type = actual at typed
  cases typed with
  | numtype nt _ _ _ => cases type <;> cases nt <;> cases equation
  | vectype vt _ _ _ => cases type <;> cases vt <;> cases equation
  | reftype value type _ _ => exact ⟨value,rfl⟩

theorem ref_is_null_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .REF_IS_NULL :: after} :: rest,[]⟩) :
    ∃ next, refIsNull ⟨s,ambient,{f with code := .REF_IS_NULL :: after} :: rest,[]⟩ f rest after = .next next ∧
      CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := .REF_IS_NULL :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .REF_IS_NULL :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | ref_is_null _ type contextWf instructionWf =>
    cases operandTypes with
    | cons valueTyped tail =>
      cases tail
      obtain ⟨reference,rfl⟩ := reference_value valueTyped
      have bound : Spec.referenceIsNull reference < 2^32 := by cases reference <;> simp [Spec.referenceIsNull]
      have resultTyped := integer_val_typed typed.typed.store .I32 (Spec.referenceIsNull reference) bound
      have freshFrame := continuation [integerVal .I32 (Spec.referenceIsNull reference)] (.cons resultTyped .nil)
      refine ⟨_,by simp only [refIsNull,split,pop_append,as_reference_value,advance],
        ⟨active_frame_preservation typed.typed freshFrame rfl,typed.contents⟩,NextSim.single ?_⟩
      obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
      have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
      have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
      have source := Spec.ref_is_null_step s f.toFrame reference typed.typed.store frameWf
      have source' : StepH ⟨⟨s,f.toFrame⟩,vals [val_ref reference] ++ [admininstr_instr .REF_IS_NULL]⟩ []
          ⟨⟨s,f.toFrame⟩,vals [integerVal .I32 (Spec.referenceIsNull reference)]⟩ := by
        cases reference <;>
          simpa only [vals,List.map_cons,List.map_nil,List.singleton_append,val_ref,admininstr_ref,admininstr_instr,
            integerVal,numtype_Inn,admininstr_val,Segment.i32] using source
      simpa only [split] using mutable_stack_simulation s s ambient f rest .REF_IS_NULL after front
        [val_ref reference] [integerVal .I32 (Spec.referenceIsNull reference)]
        typed.typed.ambient labelsWf frontWf tailWf restWf heights source'

end Itasca.Runtime.SourceMachine.Stateful
