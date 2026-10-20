import Exec.Abs.Stateful.Drops
import Exec.Abs.Sim.ChosenBasic
import Exec.Abs.Core.ChosenTrap
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

theorem elementDrop_chosen_progress {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .ELEM_DROP (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, elementDrop ⟨s,ambient,{f with code := .ELEM_DROP (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      ChosenNextSim choices occurrence ⟨s,ambient,{f with code := .ELEM_DROP (.mk_uN index) :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .ELEM_DROP (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | elem_drop _ _ type present selected contextWf instructionWf =>
    have right : index < C.ELEMS.length := present
    have left : index < f.module.ELEMS.length := by rw [bindings.elems.length_eq]; exact right
    obtain ⟨object,found,objectTyped⟩ := bindings.elems.get left right
    simp only [List.get_eq_getElem] at found objectTyped
    have mapped : f.module.ELEMS[index]? = some f.module.ELEMS[index] := List.getElem?_eq_getElem left
    cases operandTypes
    have extension := droppedElementStore_extends s f.toFrame index f.module.ELEMS[index] object typed.typed.store mapped found
    have contents := droppedElementStore_contents s f.toFrame index typed.contents extension
    have frameNext := continuation [] .nil
    have actualFrame : FrameTyped s {f with code := after} [] := by
      simpa only [List.append_nil,←split] using frameNext
    have fresh := (active_frame_preservation typed.typed actualFrame rfl).extend_same extension rfl
    refine ⟨_,by simp only [elementDrop,mapped,found,advance],⟨fresh,contents⟩,extension,ChosenNextSim.neutral admissible vector occurrence ?_ (by simp only [List.map_cons,admininstr_instr,neutralActive])⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
    have bound : index < 2^32 := by
      cases instructionWf with | instr_case_55 _ valid =>
      cases valid with | uN_case_0 _ valid => norm_num at valid ⊢; omega
    have source := element_drop_step s f.toFrame index typed.typed.store frameWf bound left (extend_store_wf extension).2
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    have full := mutable_stack_simulation s (droppedElementStore s f.toFrame index) ambient f rest (.ELEM_DROP (.mk_uN index)) after f.vals [] []
      typed.typed.ambient labelsWf valuesWf tailWf restWf height (by simpa [vals,admininstr_instr] using source)
    simpa only [List.append_nil] using full

theorem dataDrop_chosen_progress {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .DATA_DROP (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, dataDrop ⟨s,ambient,{f with code := .DATA_DROP (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      ChosenNextSim choices occurrence ⟨s,ambient,{f with code := .DATA_DROP (.mk_uN index) :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .DATA_DROP (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | data_drop _ _ present selected contextWf instructionWf =>
    have right : index < C.DATAS.length := present
    have left : index < f.module.DATAS.length := by rw [bindings.datas.length_eq]; exact right
    obtain ⟨object,found,objectTyped⟩ := bindings.datas.get left right
    simp only [List.get_eq_getElem] at found objectTyped
    have mapped : f.module.DATAS[index]? = some f.module.DATAS[index] := List.getElem?_eq_getElem left
    cases operandTypes
    have extension := droppedDataStore_extends s f.toFrame index f.module.DATAS[index] object typed.typed.store mapped found
    have contents := droppedDataStore_contents s f.toFrame index typed.contents extension
    have frameNext := continuation [] .nil
    have actualFrame : FrameTyped s {f with code := after} [] := by
      simpa only [List.append_nil,←split] using frameNext
    have fresh := (active_frame_preservation typed.typed actualFrame rfl).extend_same extension rfl
    refine ⟨_,by simp only [dataDrop,mapped,found,advance],⟨fresh,contents⟩,extension,ChosenNextSim.neutral admissible vector occurrence ?_ (by simp only [List.map_cons,admininstr_instr,neutralActive])⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
    have bound : index < 2^32 := by
      cases instructionWf with | instr_case_67 _ valid =>
      cases valid with | uN_case_0 _ valid => norm_num at valid ⊢; omega
    have source := data_drop_step s f.toFrame index typed.typed.store frameWf bound left (extend_store_wf extension).2
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    have full := mutable_stack_simulation s (droppedDataStore s f.toFrame index) ambient f rest (.DATA_DROP (.mk_uN index)) after f.vals [] []
      typed.typed.ambient labelsWf valuesWf tailWf restWf height (by simpa [vals,admininstr_instr] using source)
    simpa only [List.append_nil] using full

end Exec.Abs.Stateful
