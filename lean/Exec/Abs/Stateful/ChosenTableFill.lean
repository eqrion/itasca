import Exec.Abs.Stateful.TableFill
import Exec.Abs.Stateful.ChosenBulkSimulation
import Exec.Abs.Core.ChosenTrap
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

theorem tableFill_chosen_progress {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_FILL (.mk_uN index)::after}::rest,[]⟩) :
    (∃ next, tableFill ⟨s,ambient,{f with code := .TABLE_FILL (.mk_uN index)::after}::rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      ChosenNextSim choices occurrence ⟨s,ambient,{f with code := .TABLE_FILL (.mk_uN index)::after}::rest,[]⟩ next) ∨
    (tableFill ⟨s,ambient,{f with code := .TABLE_FILL (.mk_uN index)::after}::rest,[]⟩ f rest index after = .trap ∧
      ∃ count,0<count ∧ ChosenStepsN choices occurrence count (decode ⟨s,ambient,{f with code := .TABLE_FILL (.mk_uN index)::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .TABLE_FILL (.mk_uN index)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_fill _ _ type limits bound selected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    cases operandTypes with
    | cons destinationTyped tail => cases tail with
      | cons valueTyped tail => cases tail with
        | cons countTyped tail =>
          cases tail
          obtain ⟨destination,rfl,destinationBound⟩ := integer_val_inv (ty:=.I32) destinationTyped
          obtain ⟨reference,rfl,refTyped⟩ := reference_operand valueTyped
          obtain ⟨count,rfl,countBound⟩ := integer_val_inv (ty:=.I32) countTyped
          have destinationDecoded := integer_accepts .I32 destination destinationBound
          have countDecoded := integer_accepts .I32 count countBound
          simp only [numtype_Inn] at destinationDecoded countDecoded
          have rawTyped : Ref_ok s reference (tableElementType object.TYPE) := by rw [objectType]; exact refTyped
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
          have indexBound : index<2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
          have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          by_cases inside : destination+count ≤ object.REFS.length
          · obtain ⟨extension,contents,functions⟩ := tableFill_preserves s f.toFrame index address destination object reference count
              typed.typed.store typed.contents mapped found rawTyped
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension functions
            apply Or.inl
            refine ⟨_,by simp only [tableFill,split,popThree_append,mapped,destinationDecoded,asReference_value,countDecoded,found,inside,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.TABLES[index]! < s.TABLES.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have source := Segment.table_fill_steps s f.toFrame destination count index reference typed.typed.store frameWf
              destinationBound countBound indexBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound
              (by rw [tableEq]; exact table_size_bound typed.contents (List.mem_of_getElem? found)) (by simpa only [tableEq] using inside)
            have full := chosen_bulk_empty_simulation admissible occurrence s (Segment.tableFill s f.toFrame index destination reference count) ambient f rest
              (.TABLE_FILL (.mk_uN index)) after front [integerVal .I32 destination,val_ref reference,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.fillOperands,reference_admin_value,admininstr_instr,show admininstr_val (integerVal .I32 destination) = Segment.i32 destination from rfl,show admininstr_val (integerVal .I32 count) = Segment.i32 count from rfl] using source)
              (by exact (closedOrdinary_append _ _).mpr ⟨closedOrdinary_values _,
                by simp [closedOrdinary_cons,closedOrdinary_nil,admininstr_instr,closedOrdinaryInstruction]⟩)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [tableFill,split,popThree_append,mapped,destinationDecoded,asReference_value,countDecoded,found,inside,ite_false],?_⟩
            have source := Segment.table_fill_trap s f.toFrame destination count index reference typed.typed.store frameWf
              destinationBound countBound indexBound (by simpa only [tableEq] using Nat.lt_of_not_ge inside)
            have full := chosen_operand_trap_simulation admissible vector occurrence s ambient f rest (.TABLE_FILL (.mk_uN index)) after front
              [integerVal .I32 destination,val_ref reference,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.fillOperands,reference_admin_value,admininstr_instr,show admininstr_val (integerVal .I32 destination) = Segment.i32 destination from rfl,show admininstr_val (integerVal .I32 count) = Segment.i32 count from rfl] using source)
              (by simp only [neutralActive_vals,admininstr_instr,neutralActive])
            simpa only [split] using full
end Exec.Abs.Stateful
