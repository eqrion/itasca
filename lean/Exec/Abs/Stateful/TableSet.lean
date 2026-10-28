import Exec.Abs.Stateful.TableMutation
import Exec.Abs.Stateful.ReferenceOperands
import Exec.Abs.Core.Trap
import Exec.Spec.TableWriteBounds
namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

def tableSet (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match pop f.vals, f.module.TABLES[index]? with
  | some (prefixValues,value), some address => match pop prefixValues, asReference value, s.store.TABLES[address]? with
    | some (front,offset), some reference, some object => match integer .I32 offset with
      | some position =>
        if position < object.REFS.length then
          advance {s with store := Segment.tableWrite s.store f.toFrame index position reference}
            {f with code := after, vals := front} rest
        else .trap
      | none => .stuck
    | _,_,_ => .stuck
  | _,_ => .stuck

theorem tableSet_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    (∃ next, tableSet ⟨s,ambient,{f with code := .TABLE_SET (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .TABLE_SET (.mk_uN index) :: after} :: rest,[]⟩ next) ∨
    (tableSet ⟨s,ambient,{f with code := .TABLE_SET (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .trap ∧
      ∃ count, 0 < count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .TABLE_SET (.mk_uN index) :: after} :: rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .TABLE_SET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_set _ _ type limits bound selected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    cases operandTypes with
    | cons offsetTyped tail =>
      cases tail with
      | cons valueTyped tail =>
        cases tail
        obtain ⟨position,rfl,positionBound⟩ := integer_val_inv (ty := .I32) offsetTyped
        obtain ⟨reference,rfl,refTyped⟩ := reference_operand valueTyped
        have decoded : integer .I32 (integerVal .I32 position) = some position := integer_accepts .I32 position positionBound
        have rawTyped : Ref_ok s reference (tableElementType object.TYPE) := by rw [objectType]; exact refTyped
        have split' : f.vals = (front ++ [integerVal .I32 position]) ++ [val_ref reference] := by simpa only [List.append_assoc,List.singleton_append] using split
        obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
        have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
        have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
        have indexBound : index < 2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
        have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
          simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
        by_cases inside : position < object.REFS.length
        · have extension := tableWrite_extends s f.toFrame index address position object reference typed.typed.store typed.contents mapped found
          have contents := tableWrite_contents s f.toFrame index address position object reference typed.typed.store typed.contents mapped found rawTyped
          have freshFrame := continuation [] .nil
          have actualFrame : FrameTyped s {f with code := after,vals := front} [] := by simpa only [List.append_nil] using freshFrame
          have fresh := (active_frame_preservation typed.typed actualFrame rfl).extend_same extension rfl
          apply Or.inl
          refine ⟨_,by simp only [tableSet,split',pop_append,mapped,asReference_value,decoded,found,inside,ite_true,advance],
            ⟨fresh,contents⟩,extension,NextSim.single ?_⟩
          have source := Segment.table_write_step s f.toFrame index position reference typed.typed.store frameWf positionBound indexBound
            (List.getElem?_eq_some_iff.mp mapped).1 (by simpa only [tableEq] using inside)
          have full := mutable_stack_simulation s (Segment.tableWrite s f.toFrame index position reference) ambient f rest
            (.TABLE_SET (.mk_uN index)) after front [integerVal .I32 position,val_ref reference] []
            typed.typed.ambient labelsWf frontWf tailWf restWf heights
            (by simpa [vals,reference_admin_value,admininstr_instr,show admininstr_val (integerVal .I32 position) = Segment.i32 position from rfl] using source)
          simpa only [split,List.append_nil] using full
        · apply Or.inr
          refine ⟨by simp only [tableSet,split',pop_append,mapped,asReference_value,decoded,found,inside,ite_false],?_⟩
          have source := table_set_trap_step s f.toFrame index position reference typed.typed.store frameWf indexBound positionBound
            (by simpa only [tableEq] using Nat.le_of_not_gt inside)
          have full := operand_trap_simulation s ambient f rest (.TABLE_SET (.mk_uN index)) after front
            [integerVal .I32 position,val_ref reference] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
            (by simpa [vals,reference_admin_value,admininstr_instr,show admininstr_val (integerVal .I32 position) = Segment.i32 position from rfl] using source)
          simpa only [split] using full
end Itasca.Runtime.Abs.Stateful
