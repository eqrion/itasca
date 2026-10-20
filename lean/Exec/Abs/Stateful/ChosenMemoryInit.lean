import Exec.Abs.Stateful.MemoryInit
import Exec.Abs.Stateful.ChosenBulkSimulation
import Exec.Abs.Core.ChosenTrap
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

theorem memoryInit_chosen_progress {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (dataIndex : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .MEMORY_INIT (.mk_uN dataIndex)::after}::rest,[]⟩) :
    (∃ next, memoryInit ⟨s,ambient,{f with code := .MEMORY_INIT (.mk_uN dataIndex)::after}::rest,[]⟩ f rest dataIndex after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      ChosenNextSim choices occurrence ⟨s,ambient,{f with code := .MEMORY_INIT (.mk_uN dataIndex)::after}::rest,[]⟩ next) ∨
    (memoryInit ⟨s,ambient,{f with code := .MEMORY_INIT (.mk_uN dataIndex)::after}::rest,[]⟩ f rest dataIndex after = .trap ∧
      ∃ count,0<count ∧ ChosenStepsN choices occurrence count (decode ⟨s,ambient,{f with code := .MEMORY_INIT (.mk_uN dataIndex)::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .MEMORY_INIT (.mk_uN dataIndex)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | memory_init _ _ type present selected dataPresent dataSelected contextWf typeWf instructionWf =>
    obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
    have dataLeft : dataIndex < f.module.DATAS.length := by rw [bindings.datas.length_eq]; exact dataPresent
    obtain ⟨data,dataFound,dataTyped⟩ := bindings.datas.get dataLeft dataPresent
    simp only [List.get_eq_getElem] at dataFound dataTyped
    have dataMapped : f.module.DATAS[dataIndex]? = some f.module.DATAS[dataIndex] := List.getElem?_eq_getElem dataLeft
    obtain ⟨dataBound,dataBytes⟩ := data_bytes_typed (typed.contents.data data (List.mem_of_getElem? dataFound))
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
          have dataIndexBound : dataIndex<2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
          have dataEq : fun_data ⟨s,f.toFrame⟩ (.mk_uN dataIndex) = data := by
            simp [fun_data,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,dataMapped,dataFound]
          by_cases inside : sourceOffset+count ≤ data.BYTES.length ∧ destination+count ≤ object.BYTES.length
          · obtain ⟨extension,contents,functions⟩ := memoryInit_preserves s f.toFrame address dataIndex f.module.DATAS[dataIndex] destination sourceOffset count object data
              typed.typed.store typed.contents mapped found dataMapped dataFound inside
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension functions
            apply Or.inl
            refine ⟨_,by simp only [memoryInit,split,popThree_append,mapped,dataMapped,destinationDecoded,valueDecoded,countDecoded,found,dataFound,inside,and_true,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.MEMS[0]! < s.MEMS.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have source := Segment.memory_init_steps s f.toFrame destination sourceOffset count dataIndex typed.typed.store frameWf
              destinationBound valueBound countBound dataIndexBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound
              (by simpa only [dataEq] using dataBytes) (by simpa only [memoryEq,dataEq] using inside)
            have full := chosen_bulk_empty_simulation admissible occurrence s (Segment.memoryInit s f.toFrame dataIndex destination sourceOffset count) ambient f rest
              (.MEMORY_INIT (.mk_uN dataIndex)) after front [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
              (by exact (closedOrdinary_append _ _).mpr ⟨closedOrdinary_values _,
                by simp [closedOrdinary_cons,closedOrdinary_nil,admininstr_instr,closedOrdinaryInstruction]⟩)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [memoryInit,split,popThree_append,mapped,dataMapped,destinationDecoded,valueDecoded,countDecoded,found,dataFound,inside,ite_false],?_⟩
            have source := Segment.memory_init_trap s f.toFrame destination sourceOffset count dataIndex typed.typed.store frameWf
              destinationBound valueBound countBound dataIndexBound (by rw [memoryEq,dataEq]; omega)
            have full := chosen_operand_trap_simulation admissible vector occurrence s ambient f rest (.MEMORY_INIT (.mk_uN dataIndex)) after front
              [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
              (by simp only [neutralActive_vals,admininstr_instr,neutralActive])
            simpa only [split] using full
end Exec.Abs.Stateful
