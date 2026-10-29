import Itasca.Runtime.SourceMachine.Stateful.FillStore
import Itasca.Runtime.SourceMachine.Stateful.BulkSimulation
import Itasca.Runtime.SourceMachine.Stateful.MemorySize
import Itasca.Runtime.SourceMachine.Stateful.Operands
import Itasca.Runtime.SourceMachine.Core.Trap
namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def memoryFill (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) : AResult :=
  match popThree f.vals, f.module.MEMS[0]? with
  | some (front,offset,value,size), some address =>
    match integer .I32 offset, integer .I32 value, integer .I32 size, s.store.MEMS[address]? with
    | some destination, some valueNumber, some count, some object =>
      if destination+count ≤ object.BYTES.length then
        advance {s with store := Segment.memoryFill s.store f.toFrame destination valueNumber count}
          {f with code := after,vals := front} rest
      else .trap
    | _,_,_,_ => .stuck
  | _,_ => .stuck

theorem memory_fill_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .MEMORY_FILL::after}::rest,[]⟩) :
    (∃ next, memoryFill ⟨s,ambient,{f with code := .MEMORY_FILL::after}::rest,[]⟩ f rest after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .MEMORY_FILL::after}::rest,[]⟩ next) ∨
    (memoryFill ⟨s,ambient,{f with code := .MEMORY_FILL::after}::rest,[]⟩ f rest after = .trap ∧
      ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .MEMORY_FILL::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .MEMORY_FILL::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | memory_fill _ type present selected contextWf typeWf instructionWf =>
    obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
    cases operandTypes with
    | cons destinationTyped tail => cases tail with
      | cons valueTyped tail => cases tail with
        | cons countTyped tail =>
          cases tail
          obtain ⟨destination,rfl,destinationBound⟩ := integer_val_inv (ty:=.I32) destinationTyped
          obtain ⟨valueNumber,rfl,valueBound⟩ := integer_val_inv (ty:=.I32) valueTyped
          obtain ⟨count,rfl,countBound⟩ := integer_val_inv (ty:=.I32) countTyped
          have destinationDecoded := integer_accepts .I32 destination destinationBound
          have countDecoded := integer_accepts .I32 count countBound
          simp only [numtype_Inn] at destinationDecoded countDecoded
          have valueDecoded := integer_accepts .I32 valueNumber valueBound
          simp only [numtype_Inn] at valueDecoded
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
          have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
            simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          by_cases inside : destination+count ≤ object.BYTES.length
          · obtain ⟨extension,contents,functions⟩ := memory_fill_preserves s f.toFrame address destination valueNumber count object
              typed.typed.store typed.contents mapped found
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension functions
            apply Or.inl
            refine ⟨_,by simp only [memoryFill,split,pop_three_append,mapped,destinationDecoded,valueDecoded,countDecoded,found,inside,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.MEMS[0]! < s.MEMS.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have source := Segment.memory_fill_steps s f.toFrame destination valueNumber count typed.typed.store frameWf
              destinationBound valueBound countBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound
              (by simpa only [memoryEq] using inside)
            have full := bulk_empty_simulation s (Segment.memoryFill s f.toFrame destination valueNumber count) ambient f rest
              (.MEMORY_FILL) after front [integerVal .I32 destination,integerVal .I32 valueNumber,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [memoryFill,split,pop_three_append,mapped,destinationDecoded,valueDecoded,countDecoded,found,inside,ite_false],?_⟩
            have source := Segment.memory_fill_trap s f.toFrame destination valueNumber count typed.typed.store frameWf
              destinationBound valueBound countBound (by simpa only [memoryEq] using Nat.lt_of_not_ge inside)
            have full := operand_trap_simulation s ambient f rest (.MEMORY_FILL) after front
              [integerVal .I32 destination,integerVal .I32 valueNumber,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
end Itasca.Runtime.SourceMachine.Stateful
