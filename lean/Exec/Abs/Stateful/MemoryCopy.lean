import Exec.Abs.Stateful.CopyStore
import Exec.Abs.Stateful.InitStore
import Exec.Abs.Stateful.BulkSimulation
import Exec.Abs.Stateful.MemorySize
import Exec.Abs.Stateful.Operands
import Exec.Abs.Core.Trap
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

def memoryCopy (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) : AResult :=
  match popThree f.vals, f.module.MEMS[0]? with
  | some (front,offset,value,size), some address =>
    match integer .I32 offset, integer .I32 value, integer .I32 size, s.store.MEMS[address]? with
    | some destination, some sourceOffset, some count, some object =>
      if sourceOffset+count ≤ object.BYTES.length ∧ destination+count ≤ object.BYTES.length then
        advance {s with store := Segment.memoryCopy s.store f.toFrame destination sourceOffset count}
          {f with code := after,vals := front} rest
      else .trap
    | _,_,_,_ => .stuck
  | _,_ => .stuck

theorem memoryCopy_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .MEMORY_COPY::after}::rest,[]⟩) :
    (∃ next, memoryCopy ⟨s,ambient,{f with code := .MEMORY_COPY::after}::rest,[]⟩ f rest after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .MEMORY_COPY::after}::rest,[]⟩ next) ∨
    (memoryCopy ⟨s,ambient,{f with code := .MEMORY_COPY::after}::rest,[]⟩ f rest after = .trap ∧
      ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .MEMORY_COPY::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .MEMORY_COPY::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | memory_copy _ type present selected contextWf typeWf instructionWf =>
    obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
    cases operandTypes with
    | cons destinationTyped tail => cases tail with
      | cons valueTyped tail => cases tail with
        | cons countTyped tail =>
          cases tail
          obtain ⟨destination,rfl,destinationBound⟩ := integer_val_inv (ty:=.I32) destinationTyped
          obtain ⟨sourceOffset,rfl,valueBound⟩ := integer_val_inv (ty:=.I32) valueTyped
          obtain ⟨count,rfl,countBound⟩ := integer_val_inv (ty:=.I32) countTyped
          have destinationDecoded := integer_accepts .I32 destination destinationBound
          have countDecoded := integer_accepts .I32 count countBound
          simp only [numtype_Inn] at destinationDecoded countDecoded
          have valueDecoded := integer_accepts .I32 sourceOffset valueBound
          simp only [numtype_Inn] at valueDecoded
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
          have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
            simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          by_cases inside : sourceOffset+count ≤ object.BYTES.length ∧ destination+count ≤ object.BYTES.length
          · obtain ⟨extension,contents⟩ := memoryCopy_preserves s f.toFrame address destination sourceOffset count object
              typed.typed.store typed.contents mapped found inside
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension rfl
            apply Or.inl
            refine ⟨_,by simp only [memoryCopy,split,popThree_append,mapped,destinationDecoded,valueDecoded,countDecoded,found,inside,and_true,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.MEMS[0]! < s.MEMS.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have source := Segment.memory_copy_steps s f.toFrame destination sourceOffset count typed.typed.store frameWf
              destinationBound valueBound countBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound
              (by rw [memoryEq]; exact memory_byte_length_bound typed.contents (List.mem_of_getElem? found))
              (by simpa only [memoryEq] using inside)
            have full := bulk_empty_simulation s (Segment.memoryCopy s f.toFrame destination sourceOffset count) ambient f rest
              (.MEMORY_COPY) after front [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [memoryCopy,split,popThree_append,mapped,destinationDecoded,valueDecoded,countDecoded,found,inside,ite_false],?_⟩
            have source := Segment.memory_copy_trap s f.toFrame destination sourceOffset count typed.typed.store frameWf
              destinationBound valueBound countBound (by rw [memoryEq]; omega)
            have full := operand_trap_simulation s ambient f rest (.MEMORY_COPY) after front
              [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
end Exec.Abs.Stateful
