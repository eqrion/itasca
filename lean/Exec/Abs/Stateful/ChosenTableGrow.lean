import Exec.Abs.Stateful.TableGrow
import Exec.Abs.Sim.ChosenMutable
import Exec.Abs.Sim.ChosenTyped
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

theorem tableGrow_chosen_choices {choices : SourceChoices} (admissible : choices.Admissible)
    (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_GROW (.mk_uN index)::after}::rest,[]⟩) :
    ∃ front reference delta address object,
      f.vals = front++[val_ref reference,integerVal .I32 delta] ∧ f.module.TABLES[index]? = some address ∧ s.TABLES[address]? = some object ∧
      ∀ choice, TableGrowthChoice object delta reference choice →
      choices.table occurrence object delta reference = choice →
      ∃ next, tableGrow choice ⟨s,ambient,{f with code := .TABLE_GROW (.mk_uN index)::after}::rest,[]⟩ f rest index after = .next next ∧
        CoreTyped next ∧ Extend_store s next.store ∧
        ChosenNextSim choices occurrence ⟨s,ambient,{f with code := .TABLE_GROW (.mk_uN index)::after}::rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .TABLE_GROW (.mk_uN index)::after} [] := by cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_grow _ _ type limits bound selected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    cases operandTypes with
    | cons valueTyped tail => cases tail with
      | cons sizeTyped tail =>
        cases tail
        obtain ⟨reference,rfl,referenceTyped⟩ := reference_operand valueTyped
        obtain ⟨delta,rfl,deltaBound⟩ := integer_val_inv (ty:=.I32) sizeTyped
        have decoded : integer .I32 (integerVal .I32 delta) = some delta := integer_accepts .I32 delta deltaBound
        refine ⟨front,reference,delta,address,object,split,mapped,found,?_⟩
        have split' : f.vals = (front++[val_ref reference])++[integerVal .I32 delta] := by
          simpa [List.append_assoc] using split
        have rawTyped : Ref_ok s reference (tableElementType object.TYPE) := by rw [objectType]; exact referenceTyped
        have indexBound : index<2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
        have constant_admin : ∀ bits, admininstr_val (integerVal .I32 bits) = Segment.i32 bits := fun _ => rfl
        intro choice allowed matched
        obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
        have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
        have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
        have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
          simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
        cases allowed with
        | refused =>
          have resultTyped := integer_val_typed typed.typed.store .I32 (2^32-1) (by decide)
          have freshFrame := continuation [integerVal .I32 (2^32-1)] (.cons resultTyped .nil)
          refine ⟨_,by simp only [tableGrow,split',pop_append,mapped,decoded,found,asReference_value,advance],
            ⟨active_frame_preservation typed.typed freshFrame rfl,typed.contents⟩,extend_store_refl _ typed.typed.store,ChosenNextSim.single admissible ?_⟩
          have picked : choices.table occurrence (fun_table ⟨s,f.toFrame⟩ (.mk_uN index)) delta reference = none := by simpa only [tableEq] using matched
          have source := ChoiceStep.table (choices:=choices) (occurrence:=occurrence) s f.toFrame index delta reference
            typed.typed.store frameWf indexBound deltaBound
            (by intro success; simp only [picked,ne_eq,not_true_eq_false] at success)
            (by intro success; simp only [picked,ne_eq,not_true_eq_false] at success)
          rw [picked] at source
          simp only [tableGrowthOutput] at source
          have full := chosen_mutable_stack_simulation admissible s s ambient f rest (.TABLE_GROW (.mk_uN index)) after front [val_ref reference,integerVal .I32 delta]
            [integerVal .I32 (2^32-1)] typed.typed.ambient labelsWf frontWf tailWf restWf heights
            (by simpa [AFrame.toFrame,vals,reference_admin_value,admininstr_instr,constant_admin] using source)
          simpa only [split] using full
        | @grown grownObject grown =>
          have objectTyped := typed.contents.tables object (List.mem_of_getElem? found)
          obtain ⟨newTyped,objectExtension⟩ := growtable_typed objectTyped rawTyped grown
          obtain ⟨extension,contents⟩ := table_replacement_preserves s address object grownObject typed.typed.store typed.contents found objectExtension newTyped
          have bound : object.REFS.length < 2^32 := by
            exact table_size_bound typed.contents (List.mem_of_getElem? found)
          have resultTyped := integer_val_typed typed.typed.store .I32 (object.REFS.length) bound
          have frameNext := continuation [integerVal .I32 (object.REFS.length)] (.cons resultTyped .nil)
          have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension rfl
          refine ⟨_,by simp only [tableGrow,split',pop_append,mapped,decoded,found,asReference_value,advance],⟨fresh,contents⟩,extension,ChosenNextSim.single admissible ?_⟩
          have storeEq : {s with TABLES := s.TABLES.modify f.module.TABLES[index]! (fun _ => grownObject)} =
              {s with TABLES := s.TABLES.set address grownObject} := by
            simp [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some,List.modify_eq_set_getElem?,found]
          have source := ChoiceStep.table (choices:=choices) (occurrence:=occurrence) s f.toFrame index delta reference
            typed.typed.store frameWf indexBound deltaBound
            (fun _ => (List.getElem?_eq_some_iff.mp mapped).1)
            (fun _ => by simpa only [tableEq] using bound)
          rw [tableEq,matched] at source
          simp only [tableGrowthOutput] at source
          rw [tableEq] at source
          simp only [AFrame.toFrame,storeEq] at source
          have full := chosen_mutable_stack_simulation admissible s {s with TABLES:=s.TABLES.set address grownObject} ambient f rest (.TABLE_GROW (.mk_uN index)) after front
            [val_ref reference,integerVal .I32 delta] [integerVal .I32 (object.REFS.length)] typed.typed.ambient labelsWf frontWf tailWf restWf heights
            (by simpa [AFrame.toFrame,vals,reference_admin_value,admininstr_instr,constant_admin] using source)
          simpa only [split] using full
end Exec.Abs.Stateful
