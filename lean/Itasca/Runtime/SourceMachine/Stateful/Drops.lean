import Itasca.Runtime.SourceMachine.Core.ContentExtension
import Itasca.Runtime.Spec.SegmentDrops
import Itasca.Runtime.Spec.TableInit
import Itasca.Runtime.SourceMachine.Stateful.Continuation
import Itasca.Runtime.SourceMachine.Core.Simulation

/-!
Source data/element segment drops: store effects and typed continuation simulation.
-/

/-! ## Drop Store -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem dropped_element_store_wf (s : store) (f : frame) (index : Nat)
    (wf : wf_store s) : wf_store (droppedElementStore s f index) := by
  cases s
  cases wf
  constructor <;> assumption

theorem dropped_data_store_wf (s : store) (f : frame) (index : Nat)
    (wf : wf_store s) : wf_store (droppedDataStore s f index) := by
  cases s with | MKstore funcs globals tables memories elements data =>
  cases wf with | store_case_ _ _ _ _ _ _ hf hg ht hm hd =>
  exact .store_case_ _ _ _ _ _ _ hf hg ht hm
    (Segment.forall_modify _ _ _ _ hd (fun entry _ => .datainst_case_ _ (by simp [Forall])))

theorem dropped_element_store_as_set (s : store) (f : frame) (index address : Nat)
    (object : eleminst) (mapped : f.MODULE.ELEMS[index]? = some address)
    (found : s.ELEMS[address]? = some object) :
    droppedElementStore s f index = {s with ELEMS := s.ELEMS.set address {object with REFS := []}} := by
  simp only [droppedElementStore,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

theorem dropped_data_store_as_set (s : store) (f : frame) (index address : Nat)
    (object : datainst) (mapped : f.MODULE.DATAS[index]? = some address)
    (found : s.DATAS[address]? = some object) :
    droppedDataStore s f index = {s with DATAS := s.DATAS.set address {object with BYTES := []}} := by
  simp only [droppedDataStore,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

theorem dropped_element_store_extends (s : store) (f : frame) (index address : Nat)
    (object : eleminst) (wf : wf_store s)
    (mapped : f.MODULE.ELEMS[index]? = some address) (found : s.ELEMS[address]? = some object) :
    Extend_store s (droppedElementStore s f index) := by
  have fresh := dropped_element_store_wf s f index wf
  rw [dropped_element_store_as_set s f index address object mapped found] at fresh ⊢
  apply extend_store_set_elem s address _ wf fresh
  intro bound
  simp only [List.getElem!_eq_getElem?_getD,found,Option.getD_some]
  cases object
  exact .mk_Extend_eleminst _ _ _ (Or.inr rfl)

theorem dropped_data_store_extends (s : store) (f : frame) (index address : Nat)
    (object : datainst) (wf : wf_store s)
    (mapped : f.MODULE.DATAS[index]? = some address) (found : s.DATAS[address]? = some object) :
    Extend_store s (droppedDataStore s f index) := by
  have fresh := dropped_data_store_wf s f index wf
  rw [dropped_data_store_as_set s f index address object mapped found] at fresh ⊢
  apply extend_store_set_data s address _ wf fresh
  intro bound
  have old : wf_datainst object := by cases wf; apply_assumption; exact List.mem_of_getElem? found
  simp only [List.getElem!_eq_getElem?_getD,found,Option.getD_some]
  cases object
  exact .mk_Extend_datainst _ _ (Or.inr rfl) old (.datainst_case_ _ (by simp [Forall]))

theorem dropped_element_store_contents (s : store) (f : frame) (index : Nat)
    (contents : StoreContentsTyped s) (extension : Extend_store s (droppedElementStore s f index)) :
    StoreContentsTyped (droppedElementStore s f index) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact fun object member => globalinst_typed_extend extension (contents.globals object member)
  · exact fun object member => tableinst_typed_extend extension (contents.tables object member)
  · exact fun object member => meminst_typed_extend extension (contents.memories object member)
  · change Forall (fun object => Eleminst_ok _ object object.TYPE) (s.ELEMS.modify _ _)
    apply Segment.forall_modify
    · exact fun object member => eleminst_ok_extend extension (extend_elem_refl object) (contents.elements object member)
    · intro object typed
      cases typed with
      | mk_Eleminst_ok type refs refsOk length wf =>
        exact .mk_Eleminst_ok _ _ [] (by simp [Forall]) (by norm_num) wf
  · intro object member
    have typed := contents.data object member
    have wf : wf_datainst object := by cases typed; assumption
    exact datainst_ok_extend extension (extend_data_refl object wf) typed

theorem dropped_data_store_contents (s : store) (f : frame) (index : Nat)
    (contents : StoreContentsTyped s) (extension : Extend_store s (droppedDataStore s f index)) :
    StoreContentsTyped (droppedDataStore s f index) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact fun object member => globalinst_typed_extend extension (contents.globals object member)
  · exact fun object member => tableinst_typed_extend extension (contents.tables object member)
  · exact fun object member => meminst_typed_extend extension (contents.memories object member)
  · exact fun object member => eleminst_ok_extend extension (extend_elem_refl object) (contents.elements object member)
  · change Forall (fun object => Datainst_ok _ object .OK) (s.DATAS.modify _ _)
    apply Segment.forall_modify
    · intro object member
      have typed := contents.data object member
      have wf : wf_datainst object := by cases typed; assumption
      exact datainst_ok_extend extension (extend_data_refl object wf) typed
    · intro object typed
      exact .mk_Datainst_ok _ [] (by norm_num) (extend_store_wf extension).2 (.datainst_case_ _ (by simp [Forall]))
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## Drops -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def elementDrop (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match f.module.ELEMS[index]? with
  | none => .stuck
  | some address => match s.store.ELEMS[address]? with
    | none => .stuck
    | some _ => advance {s with store := droppedElementStore s.store f.toFrame index} {f with code := after} rest

theorem element_drop_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .ELEM_DROP (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, elementDrop ⟨s,ambient,{f with code := .ELEM_DROP (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .ELEM_DROP (.mk_uN index) :: after} :: rest,[]⟩ next := by
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
    have extension := dropped_element_store_extends s f.toFrame index f.module.ELEMS[index] object typed.typed.store mapped found
    have contents := dropped_element_store_contents s f.toFrame index typed.contents extension
    have frameNext := continuation [] .nil
    have actualFrame : FrameTyped s {f with code := after} [] := by
      simpa only [List.append_nil,←split] using frameNext
    have fresh := (active_frame_preservation typed.typed actualFrame rfl).extend_same extension rfl
    refine ⟨_,by simp only [elementDrop,mapped,found,advance],⟨fresh,contents⟩,extension,NextSim.single ?_⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
    have bound : index < 2^32 := by
      cases instructionWf with | instr_case_55 _ valid =>
      cases valid with | uN_case_0 _ valid => norm_num at valid ⊢; omega
    have source := element_drop_step s f.toFrame index typed.typed.store frameWf bound left (extend_store_wf extension).2
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    have full := mutable_stack_simulation s (droppedElementStore s f.toFrame index) ambient f rest (.ELEM_DROP (.mk_uN index)) after f.vals [] []
      typed.typed.ambient labelsWf valuesWf tailWf restWf height (by simpa [vals,admininstr_instr] using source)
    simpa only [List.append_nil] using full

def dataDrop (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match f.module.DATAS[index]? with
  | none => .stuck
  | some address => match s.store.DATAS[address]? with
    | none => .stuck
    | some _ => advance {s with store := droppedDataStore s.store f.toFrame index} {f with code := after} rest

theorem data_drop_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .DATA_DROP (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, dataDrop ⟨s,ambient,{f with code := .DATA_DROP (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .DATA_DROP (.mk_uN index) :: after} :: rest,[]⟩ next := by
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
    have extension := dropped_data_store_extends s f.toFrame index f.module.DATAS[index] object typed.typed.store mapped found
    have contents := dropped_data_store_contents s f.toFrame index typed.contents extension
    have frameNext := continuation [] .nil
    have actualFrame : FrameTyped s {f with code := after} [] := by
      simpa only [List.append_nil,←split] using frameNext
    have fresh := (active_frame_preservation typed.typed actualFrame rfl).extend_same extension rfl
    refine ⟨_,by simp only [dataDrop,mapped,found,advance],⟨fresh,contents⟩,extension,NextSim.single ?_⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
    have bound : index < 2^32 := by
      cases instructionWf with | instr_case_67 _ valid =>
      cases valid with | uN_case_0 _ valid => norm_num at valid ⊢; omega
    have source := data_drop_step s f.toFrame index typed.typed.store frameWf bound left (extend_store_wf extension).2
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    have full := mutable_stack_simulation s (droppedDataStore s f.toFrame index) ambient f rest (.DATA_DROP (.mk_uN index)) after f.vals [] []
      typed.typed.ambient labelsWf valuesWf tailWf restWf height (by simpa [vals,admininstr_instr] using source)
    simpa only [List.append_nil] using full

end Itasca.Runtime.SourceMachine.Stateful

end
