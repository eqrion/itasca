import Exec.Abs.Core.MemoryStep
import Exec.Abs.Core.MemoryTyping
import Exec.Abs.Core.MemoryMutation
import Exec.Abs.Core.Trap

namespace Exec.Abs.Core
open SpecExt Exec.Spec

/-- A typed scalar load either produces the value prescribed by the generated
memory rule, or takes a positive source reduction sequence to the bounds trap. -/
theorem load_progress (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Load) (argument : memarg)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    (∃ next, load ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
      f rest after op argument = .next next ∧ CoreTyped next ∧
      StepH (decode ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) [] (decode next)) ∨
    (load ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
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
    cases tail
    obtain ⟨bits,rfl,bitsBound⟩ := integer_val_inv (ty := .I32) addressTyped
    have decoded : integer .I32 (integerVal .I32 bits) = some bits := by
      simpa only [numtype_Inn] using integer_accepts .I32 bits bitsBound
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf frameTyped
    have operationWf := wf_admininstr_instr (codeWf (op.source argument) (by simp))
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by
      cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
    have objectTyped := typed.contents.memories object (List.mem_of_getElem? found)
    have bytesWf : Forall wf_byte object.BYTES := by
      cases objectTyped with
      | mk_Meminst_ok _ _ _ _ _ _ wf _ => cases wf; assumption
    have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
      simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
    have source := op.source_step s f.toFrame argument bits typed.typed.store frameWf bitsBound operationWf
      (by simpa only [memoryEq] using bytesWf)
    rw [memoryEq] at source
    by_cases inside : bits + proj_uN_0 argument.OFFSET + op.bytes ≤ object.BYTES.length
    · let payload := (object.BYTES.drop (bits + proj_uN_0 argument.OFFSET)).take op.bytes
      have payloadWf : Forall wf_byte payload := by
        intro byte member
        exact bytesWf byte (List.mem_of_mem_drop (List.mem_of_mem_take member))
      have payloadLength : payload.length = op.bytes := by
        simp only [payload,List.length_take,List.length_drop]
        omega
      have resultWf := op.value_wf payload payloadWf payloadLength
      have resultTyped : Val_ok s (op.value payload) (valtype_numtype op.type) := by
        cases op <;> exact .numtype _ _ _ typed.typed.store resultWf
      obtain ⟨_,_,_,_,continuation⟩ := memory_load_frame_continuation op argument
        (by simpa only [split] using frameTyped) resultTyped
      have fresh := active_frame_preservation typed.typed continuation rfl
      let next : AState := ⟨s,ambient,{f with code := after, vals := front ++ [op.value payload]} :: rest,[]⟩
      apply Or.inl
      refine ⟨next,?_,⟨fresh,typed.contents⟩,?_⟩
      · simp only [load,split,pop_append,mapped,decoded,found,inside,ite_true,advance,next,payload]
      · simp only [inside,ite_true] at source
        have full := mutable_stack_simulation s s ambient f rest (op.source argument) after front
          [integerVal .I32 bits] [op.value payload] typed.typed.ambient labelsWf frontWf tailWf restWf heights
          (by simpa [vals,admininstr_val,integerVal,Spec.Segment.i32,numtype_Inn,payload] using source)
        simpa only [split,next] using full
    · apply Or.inr
      refine ⟨?_,?_⟩
      · simp only [load,split,pop_append,mapped,decoded,found,inside,ite_false]
      · simp only [inside,ite_false] at source
        have full := operand_trap_simulation s ambient f rest (op.source argument) after front
          [integerVal .I32 bits] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
          (by simpa [vals,admininstr_val,integerVal,Spec.Segment.i32,numtype_Inn] using source)
        simpa only [split] using full

end Exec.Abs.Core
