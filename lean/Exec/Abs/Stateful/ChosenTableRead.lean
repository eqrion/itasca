import Exec.Abs.Stateful.TableRead
import Exec.Abs.Sim.ChosenBasic
import Exec.Abs.Core.ChosenTrap
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

theorem tableGet_chosen_progress {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_GET (.mk_uN index) :: after} :: rest,[]⟩) :
    (∃ next, tableGet ⟨s,ambient,{f with code := .TABLE_GET (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ ChosenNextSim choices occurrence ⟨s,ambient,{f with code := .TABLE_GET (.mk_uN index) :: after} :: rest,[]⟩ next) ∨
    (tableGet ⟨s,ambient,{f with code := .TABLE_GET (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .trap ∧
      ∃ count, 0 < count ∧ ChosenStepsN choices occurrence count (decode ⟨s,ambient,{f with code := .TABLE_GET (.mk_uN index) :: after} :: rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .TABLE_GET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_get _ _ type limits bound selected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    cases operandTypes with
    | cons valueTyped tail =>
      cases tail
      obtain ⟨position,rfl,positionBound⟩ := integer_val_inv (ty := .I32) valueTyped
      have decoded : integer .I32 (integerVal .I32 position) = some position := integer_accepts .I32 position positionBound
      obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
      have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
      have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
      have indexBound : index < 2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
      have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
        simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
      have source := Spec.table_get_step s f.toFrame index position typed.typed.store frameWf indexBound positionBound
      rw [tableEq] at source
      by_cases inside : position < object.REFS.length
      · have refTyped := table_references typed.contents (List.mem_of_getElem? found) object.REFS[position] (List.getElem_mem inside)
        rw [objectType] at refTyped
        have resultTyped : Val_ok s (val_ref object.REFS[position]) (valtype_reftype type) :=
          .reftype s _ type refTyped typed.typed.store
        have freshFrame := continuation [val_ref object.REFS[position]] (.cons resultTyped .nil)
        apply Or.inl
        refine ⟨_,by simp [tableGet,split,pop_append,mapped,decoded,found,inside,advance],
          ⟨active_frame_preservation typed.typed freshFrame rfl,typed.contents⟩,ChosenNextSim.neutral admissible vector occurrence ?_ (by simp only [List.map_cons,admininstr_instr,neutralActive])⟩
        simp only [inside,ite_true,getElem!_pos object.REFS position inside] at source
        have converted : admininstr_val (val_ref object.REFS[position]) = admininstr_ref object.REFS[position] := by
          generalize object.REFS[position] = value
          cases value <;> rfl
        have source' : StepH ⟨⟨s,f.toFrame⟩,vals [integerVal .I32 position] ++ [admininstr_instr (.TABLE_GET (.mk_uN index))]⟩ []
            ⟨⟨s,f.toFrame⟩,vals [val_ref object.REFS[position]]⟩ := by
          simpa only [vals,List.map_cons,List.map_nil,List.singleton_append,converted,admininstr_instr,
            show admininstr_val (integerVal .I32 position) = Segment.i32 position from rfl] using source
        simpa only [split] using mutable_stack_simulation s s ambient f rest (.TABLE_GET (.mk_uN index)) after front
          [integerVal .I32 position] [val_ref object.REFS[position]] typed.typed.ambient labelsWf frontWf tailWf restWf heights source'
      · apply Or.inr
        refine ⟨by simp [tableGet,split,pop_append,mapped,decoded,found,inside],?_⟩
        simp only [inside,ite_false] at source
        have full := chosen_operand_trap_simulation admissible vector occurrence s ambient f rest (.TABLE_GET (.mk_uN index)) after front
          [integerVal .I32 position] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
          (by simpa [vals,admininstr_val,integerVal,Segment.i32,numtype_Inn,admininstr_instr] using source)
          (by simp only [neutralActive_vals,admininstr_instr,neutralActive])
        simpa only [split] using full

theorem tableSize_chosen_progress {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_SIZE (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, tableSize ⟨s,ambient,{f with code := .TABLE_SIZE (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ ChosenNextSim choices occurrence ⟨s,ambient,{f with code := .TABLE_SIZE (.mk_uN index) :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .TABLE_SIZE (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_size _ _ limits type bound selected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    cases operandTypes
    have sizeBound := table_size_bound typed.contents (List.mem_of_getElem? found)
    have resultTyped := integer_val_typed typed.typed.store .I32 object.REFS.length sizeBound
    have freshFrame := continuation [integerVal .I32 object.REFS.length] (.cons resultTyped .nil)
    have actualFrame : FrameTyped s {f with code := after,vals := f.vals ++ [integerVal .I32 object.REFS.length]} [] := by
      simpa only [split,List.append_nil] using freshFrame
    refine ⟨_,by simp only [tableSize,mapped,found,advance],
      ⟨active_frame_preservation typed.typed actualFrame rfl,typed.contents⟩,ChosenNextSim.neutral admissible vector occurrence ?_ (by simp only [List.map_cons,admininstr_instr,neutralActive])⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
    have indexBound : index < 2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
    have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
      simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
    have source := Spec.table_size_step s f.toFrame index typed.typed.store frameWf indexBound (by simpa only [tableEq] using sizeBound)
    rw [tableEq] at source
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    have full := mutable_stack_simulation s s ambient f rest (.TABLE_SIZE (.mk_uN index)) after f.vals []
      [integerVal .I32 object.REFS.length] typed.typed.ambient labelsWf valuesWf tailWf restWf height
      (by simpa [vals,admininstr_val,integerVal,Segment.i32,numtype_Inn,admininstr_instr] using source)
    simpa only [List.append_nil] using full

end Exec.Abs.Stateful
