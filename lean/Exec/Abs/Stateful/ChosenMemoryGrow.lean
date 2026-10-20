import Exec.Abs.Stateful.MemoryGrow
import Exec.Abs.Sim.ChosenMutable
import Exec.Abs.Sim.ChosenTyped
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

theorem memoryGrow_chosen_choices {choices : SourceChoices} (admissible : choices.Admissible)
    (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .MEMORY_GROW::after}::rest,[]⟩) :
    ∃ front delta address object,
      f.vals = front++[integerVal .I32 delta] ∧ f.module.MEMS[0]? = some address ∧ s.MEMS[address]? = some object ∧
      ∀ choice, MemoryGrowthChoice object delta choice →
      choices.memory occurrence object delta = choice →
      ∃ next, memoryGrow choice ⟨s,ambient,{f with code := .MEMORY_GROW::after}::rest,[]⟩ f rest after = .next next ∧
        CoreTyped next ∧ Extend_store s next.store ∧
        ChosenNextSim choices occurrence ⟨s,ambient,{f with code := .MEMORY_GROW::after}::rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .MEMORY_GROW::after} [] := by cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | memory_grow _ type present selected contextWf typeWf instructionWf =>
    obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
    cases operandTypes with
    | cons valueTyped tail =>
      cases tail
      obtain ⟨delta,rfl,deltaBound⟩ := integer_val_inv (ty:=.I32) valueTyped
      have decoded : integer .I32 (integerVal .I32 delta) = some delta := integer_accepts .I32 delta deltaBound
      refine ⟨front,delta,address,object,split,mapped,found,?_⟩
      intro choice allowed matched
      obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
      have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
      have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
      have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
        simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
      cases allowed with
      | refused =>
        have resultTyped := integer_val_typed typed.typed.store .I32 (2^32-1) (by decide)
        have freshFrame := continuation [integerVal .I32 (2^32-1)] (.cons resultTyped .nil)
        refine ⟨_,by simp only [memoryGrow,split,pop_append,mapped,decoded,found,advance],
          ⟨active_frame_preservation typed.typed freshFrame rfl,typed.contents⟩,extend_store_refl _ typed.typed.store,ChosenNextSim.single admissible ?_⟩
        have picked : choices.memory occurrence (fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0)) delta = none := by simpa only [memoryEq] using matched
        have source := ChoiceStep.memory (choices:=choices) (occurrence:=occurrence) s f.toFrame delta
          typed.typed.store frameWf deltaBound
          (by intro success; simp only [picked,ne_eq,not_true_eq_false] at success)
          (by intro success; simp only [picked,ne_eq,not_true_eq_false] at success)
        rw [picked] at source
        simp only [memoryGrowthOutput] at source
        have full := chosen_mutable_stack_simulation admissible s s ambient f rest .MEMORY_GROW after front [integerVal .I32 delta]
          [integerVal .I32 (2^32-1)] typed.typed.ambient labelsWf frontWf tailWf restWf heights
          (by simpa [AFrame.toFrame,vals,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
        simpa only [split] using full
      | @grown grownObject grown =>
        have objectTyped := typed.contents.memories object (List.mem_of_getElem? found)
        obtain ⟨newTyped,objectExtension⟩ := growmemory_typed objectTyped grown
        obtain ⟨extension,contents⟩ := memory_replacement_preserves s address object grownObject typed.typed.store typed.contents found objectExtension newTyped
        have bound : object.BYTES.length/65536 < 2^32 := by
          have := memory_pages_bound typed.contents (List.mem_of_getElem? found); omega
        have resultTyped := integer_val_typed typed.typed.store .I32 (object.BYTES.length/65536) bound
        have frameNext := continuation [integerVal .I32 (object.BYTES.length/65536)] (.cons resultTyped .nil)
        have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension rfl
        refine ⟨_,by simp only [memoryGrow,split,pop_append,mapped,decoded,found,advance],⟨fresh,contents⟩,extension,ChosenNextSim.single admissible ?_⟩
        have storeEq : {s with MEMS := s.MEMS.modify f.module.MEMS[0]! (fun _ => grownObject)} =
            {s with MEMS := s.MEMS.set address grownObject} := by
          simp [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some,List.modify_eq_set_getElem?,found]
        have source := ChoiceStep.memory (choices:=choices) (occurrence:=occurrence) s f.toFrame delta
          typed.typed.store frameWf deltaBound
          (fun _ => (List.getElem?_eq_some_iff.mp mapped).1)
          (fun _ => by simpa only [memoryEq] using bound)
        rw [memoryEq,matched] at source
        simp only [memoryGrowthOutput] at source
        rw [memoryEq] at source
        simp only [AFrame.toFrame,storeEq] at source
        have full := chosen_mutable_stack_simulation admissible s {s with MEMS:=s.MEMS.set address grownObject} ambient f rest .MEMORY_GROW after front
          [integerVal .I32 delta] [integerVal .I32 (object.BYTES.length/65536)] typed.typed.ambient labelsWf frontWf tailWf restWf heights
          (by simpa [AFrame.toFrame,vals,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
        simpa only [split] using full
end Exec.Abs.Stateful
