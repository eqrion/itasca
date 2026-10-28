import Itasca.Runtime.Abs.Core.MemoryStep
import Itasca.Runtime.Abs.Core.MemoryTyping
import Itasca.Runtime.Abs.Core.MemoryMutation
import Itasca.Runtime.Abs.Core.Trap

namespace Itasca.Runtime.Abs.Core
open SpecExt Itasca.Runtime.Spec

theorem numeric_value_inv {s : _root_.store} {value : val} {ty : numtype}
    (typed : Val_ok s value (valtype_numtype ty)) :
    ∃ number, value = .CONST ty number ∧ wf_num_ ty number := by
  have wf := val_ok_wf typed
  have ht := value_type_of_typed typed
  cases wf with
  | val_case_0 nt number valid =>
    have same : nt = ty := by cases nt <;> cases ty <;> simp_all [valueType,valtype_numtype]
    subst nt
    exact ⟨number,rfl,valid⟩
  | val_case_1 vt bits _ => cases ty <;> simp_all [valueType,valtype_numtype]
  | val_case_2 rt => cases ty <;> cases rt <;> simp_all [valueType,valtype_numtype,valtype_reftype]
  | val_case_3 address => cases ty <;> simp_all [valueType,valtype_numtype]
  | val_case_4 address => cases ty <;> simp_all [valueType,valtype_numtype]

/-- Scalar stores update only an in-bounds payload and retain full source
store/frame typing; an out-of-bounds write reaches the generated trap. -/
theorem store_progress (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Store) (argument : memarg)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    (∃ next, store ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
      f rest after op argument = .next next ∧ CoreTyped next ∧ Extend_store s next.store ∧
      StepH (decode ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) [] (decode next)) ∨
    (store ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
      f rest after op argument = .trap ∧ ∃ n, 0 < n ∧
      StepsHN n (decode ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have frameTyped : FrameTyped s {f with code := op.source argument :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,ins,outs,bindings,_,operation,split,operandTypes,frontWf,heights⟩ :=
    frame_typed_operands_bounds frameTyped
  obtain ⟨rfl,rfl,present⟩ := op.typing argument operation
  obtain ⟨memoryAddress,object,mapped,found⟩ := bindings.memory_lookup present
  cases operandTypes with
  | cons addressTyped tail =>
    cases tail with
    | cons valueTyped tail =>
      cases tail
      obtain ⟨bits,rfl,bitsBound⟩ := integer_val_inv (ty := .I32) addressTyped
      obtain ⟨number,rfl,numberWf⟩ := numeric_value_inv valueTyped
      have decoded : integer .I32 (integerVal .I32 bits) = some bits := by
        simpa only [numtype_Inn] using integer_accepts .I32 bits bitsBound
      obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf frameTyped
      have operationWf := wf_admininstr_instr (codeWf (op.source argument) (by simp))
      have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
      have restWf : Forall FrameWf rest := by
        cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
      have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
        simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
      have source := op.source_step s f.toFrame argument bits number typed.typed.store frameWf bitsBound operationWf numberWf
        (List.getElem?_eq_some_iff.mp mapped).1
      rw [memoryEq] at source
      have shape : f.vals = (front ++ [integerVal .I32 bits]) ++ [.CONST op.type number] := by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
      by_cases inside : bits + proj_uN_0 argument.OFFSET + op.bytes ≤ object.BYTES.length
      · obtain ⟨_,_,_,_,continuation⟩ := memory_store_frame_continuation op argument
          (by simpa only [split] using frameTyped)
        have extension := memoryPayloadWrite_extends s f.toFrame memoryAddress
          (bits+proj_uN_0 argument.OFFSET) object (op.payload number) typed.typed.store typed.contents mapped found (op.payload_wf number)
        have contents := typed.contents.memory_write typed.typed.store f.toFrame memoryAddress
          (bits+proj_uN_0 argument.OFFSET) object (op.payload number) mapped found (op.payload_wf number)
        have old := active_frame_preservation typed.typed continuation rfl
        have fresh := old.extend_same extension rfl
        let next : AState := ⟨memoryPayloadWrite s f.toFrame (bits+proj_uN_0 argument.OFFSET) (op.payload number),ambient,
          {f with code := after, vals := front} :: rest,[]⟩
        apply Or.inl
        refine ⟨next,?_,⟨fresh,contents⟩,extension,?_⟩
        · simp only [store,shape,pop_append,mapped,ite_true,decoded,found,inside,advance,next]
        · simp only [inside,ite_true] at source
          have full := mutable_stack_simulation s next.store ambient f rest (op.source argument) after front
            [integerVal .I32 bits,.CONST op.type number] [] typed.typed.ambient labelsWf frontWf tailWf restWf heights
            (by simpa [vals,admininstr_val,integerVal,Spec.Segment.i32,numtype_Inn,next] using source)
          simpa only [split,next,List.append_nil] using full
      · apply Or.inr
        refine ⟨?_,?_⟩
        · simp only [store,shape,pop_append,mapped,ite_true,decoded,found,inside,ite_false]
        · simp only [inside,ite_false] at source
          have full := operand_trap_simulation s ambient f rest (op.source argument) after front
            [integerVal .I32 bits,.CONST op.type number] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
            (by simpa [vals,admininstr_val,integerVal,Spec.Segment.i32,numtype_Inn] using source)
          simpa only [split] using full

end Itasca.Runtime.Abs.Core
