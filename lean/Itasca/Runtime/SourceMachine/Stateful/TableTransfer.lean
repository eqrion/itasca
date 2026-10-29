import Itasca.Runtime.SourceMachine.Stateful.CopyStore
import Itasca.Runtime.SourceMachine.Stateful.InitStore
import Itasca.Runtime.SourceMachine.Stateful.BulkSimulation
import Itasca.Runtime.SourceMachine.Stateful.ReferenceOperands
import Itasca.Runtime.SourceMachine.Stateful.Operands
import Itasca.Runtime.SourceMachine.Core.Trap

/-!
Source table copy and initialization, retaining reference and segment bounds in the common transfer argument.
-/

/-! ## Table Copy -/

section

namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

def tableCopy (s : AState) (f : AFrame) (rest : List AFrame) (index sourceIndex : Nat) (after : List instr) : AResult :=
  match popThree f.vals, f.module.TABLES[index]?, f.module.TABLES[sourceIndex]? with
  | some (front,offset,value,size), some address, some sourceAddress =>
    match integer .I32 offset, integer .I32 value, integer .I32 size, s.store.TABLES[address]?, s.store.TABLES[sourceAddress]? with
    | some destination, some sourceOffset, some count, some object, some sourceObject =>
      if sourceOffset+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length then
        advance {s with store := Segment.tableCopy s.store f.toFrame index sourceIndex destination sourceOffset count}
          {f with code := after,vals := front} rest
      else .trap
    | _,_,_,_,_ => .stuck
  | _,_,_ => .stuck

theorem tableCopy_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index sourceIndex : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩) :
    (∃ next, tableCopy ⟨s,ambient,{f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ f rest index sourceIndex after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ next) ∨
    (tableCopy ⟨s,ambient,{f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ f rest index sourceIndex after = .trap ∧
      ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_copy _ _ _ limits type sourceLimits bound selected sourceBound sourceSelected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    have sourceLookup : C.TABLES[sourceIndex]? = some (.mk_tabletype sourceLimits type) := by
      simp only [labelContext,proj_uN_0] at sourceBound sourceSelected
      simpa only [getElem!_pos C.TABLES sourceIndex sourceBound,List.getElem?_eq_getElem sourceBound] using congrArg some sourceSelected
    obtain ⟨sourceAddress,sourceObject,sourceMapped,sourceFound,sourceType⟩ := table_lookup bindings sourceLookup
    have sameType : tableElementType object.TYPE = tableElementType sourceObject.TYPE := objectType.trans sourceType.symm
    cases operandTypes with
    | cons destinationTyped tail => cases tail with
      | cons valueTyped tail => cases tail with
        | cons countTyped tail =>
          cases tail
          obtain ⟨destination,rfl,destinationBound⟩ := integer_val_inv (ty:=.I32) destinationTyped
          obtain ⟨sourceOffset,rfl,sourceOffsetBound⟩ := integer_val_inv (ty:=.I32) valueTyped
          obtain ⟨count,rfl,countBound⟩ := integer_val_inv (ty:=.I32) countTyped
          have destinationDecoded := integer_accepts .I32 destination destinationBound
          have countDecoded := integer_accepts .I32 count countBound
          simp only [numtype_Inn] at destinationDecoded countDecoded
          have sourceDecoded : integer .I32 (integerVal .I32 sourceOffset) = some sourceOffset := integer_accepts .I32 sourceOffset sourceOffsetBound
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
          have indexBound : index<2^32 := by cases instructionWf; rename_i valid _; cases valid; norm_num at *; omega
          have sourceIndexBound : sourceIndex<2^32 := by cases instructionWf; rename_i _ valid; cases valid; norm_num at *; omega
          have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          have sourceEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN sourceIndex) = sourceObject := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,sourceMapped,sourceFound]
          by_cases inside : sourceOffset+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length
          · obtain ⟨extension,contents⟩ := tableCopy_preserves s f.toFrame index sourceIndex address sourceAddress destination sourceOffset count object sourceObject
              typed.typed.store typed.contents mapped sourceMapped found sourceFound sameType inside
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension rfl
            apply Or.inl
            refine ⟨_,by simp only [tableCopy,split,popThree_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,and_true,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.TABLES[index]! < s.TABLES.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have sourceAddressBound : f.module.TABLES[sourceIndex]! < s.TABLES.length := by
              simpa only [List.getElem!_eq_getElem?_getD,sourceMapped,Option.getD_some] using (List.getElem?_eq_some_iff.mp sourceFound).1
            have source := Segment.table_copy_steps s f.toFrame destination sourceOffset count index sourceIndex typed.typed.store frameWf
              destinationBound sourceOffsetBound countBound indexBound sourceIndexBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound sourceAddressBound
              (by rw [tableEq,sourceEq]; exact ⟨table_size_bound typed.contents (List.mem_of_getElem? found),table_size_bound typed.contents (List.mem_of_getElem? sourceFound)⟩)
              (by simpa only [tableEq,sourceEq] using inside)
            have full := bulk_empty_simulation s (Segment.tableCopy s f.toFrame index sourceIndex destination sourceOffset count) ambient f rest
              (.TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)) after front [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [tableCopy,split,popThree_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,ite_false],?_⟩
            have source := Segment.table_copy_trap s f.toFrame destination sourceOffset count index sourceIndex typed.typed.store frameWf
              destinationBound sourceOffsetBound countBound indexBound sourceIndexBound (by rw [tableEq,sourceEq]; omega)
            have full := operand_trap_simulation s ambient f rest (.TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)) after front
              [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
end Itasca.Runtime.Abs.Stateful

end

/-! ## Table Init -/

section

namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

def tableInit (s : AState) (f : AFrame) (rest : List AFrame) (index sourceIndex : Nat) (after : List instr) : AResult :=
  match popThree f.vals, f.module.TABLES[index]?, f.module.ELEMS[sourceIndex]? with
  | some (front,offset,value,size), some address, some sourceAddress =>
    match integer .I32 offset, integer .I32 value, integer .I32 size, s.store.TABLES[address]?, s.store.ELEMS[sourceAddress]? with
    | some destination, some sourceOffset, some count, some object, some sourceObject =>
      if sourceOffset+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length then
        advance {s with store := Segment.tableInit s.store f.toFrame index sourceIndex destination sourceOffset count}
          {f with code := after,vals := front} rest
      else .trap
    | _,_,_,_,_ => .stuck
  | _,_,_ => .stuck

theorem tableInit_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index sourceIndex : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩) :
    (∃ next, tableInit ⟨s,ambient,{f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ f rest index sourceIndex after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ next) ∨
    (tableInit ⟨s,ambient,{f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ f rest index sourceIndex after = .trap ∧
      ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_init _ _ _ limits type bound selected sourceBound sourceSelected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    simp only [labelContext,proj_uN_0] at sourceBound sourceSelected
    have sourceLeft : sourceIndex < f.module.ELEMS.length := by rw [bindings.elems.length_eq]; exact sourceBound
    obtain ⟨sourceObject,sourceFound,sourceTyped⟩ := bindings.elems.get sourceLeft sourceBound
    simp only [List.get_eq_getElem] at sourceFound sourceTyped
    have sourceMapped : f.module.ELEMS[sourceIndex]? = some f.module.ELEMS[sourceIndex] := List.getElem?_eq_getElem sourceLeft
    obtain ⟨sourceType,elementBound,elementRefs⟩ := element_refs_typed sourceTyped
    have sourceType' : sourceObject.TYPE = type := by
      rw [sourceType]
      simpa only [labelContext,proj_uN_0,getElem!_pos C.ELEMS sourceIndex sourceBound] using sourceSelected
    have sameType : tableElementType object.TYPE = sourceObject.TYPE := objectType.trans sourceType'.symm
    cases operandTypes with
    | cons destinationTyped tail => cases tail with
      | cons valueTyped tail => cases tail with
        | cons countTyped tail =>
          cases tail
          obtain ⟨destination,rfl,destinationBound⟩ := integer_val_inv (ty:=.I32) destinationTyped
          obtain ⟨sourceOffset,rfl,sourceOffsetBound⟩ := integer_val_inv (ty:=.I32) valueTyped
          obtain ⟨count,rfl,countBound⟩ := integer_val_inv (ty:=.I32) countTyped
          have destinationDecoded := integer_accepts .I32 destination destinationBound
          have countDecoded := integer_accepts .I32 count countBound
          simp only [numtype_Inn] at destinationDecoded countDecoded
          have sourceDecoded : integer .I32 (integerVal .I32 sourceOffset) = some sourceOffset := integer_accepts .I32 sourceOffset sourceOffsetBound
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
          have indexBound : index<2^32 := by cases instructionWf; rename_i valid _; cases valid; norm_num at *; omega
          have sourceIndexBound : sourceIndex<2^32 := by cases instructionWf; rename_i _ valid; cases valid; norm_num at *; omega
          have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          have sourceEq : fun_elem ⟨s,f.toFrame⟩ (.mk_uN sourceIndex) = sourceObject := by
            simp [fun_elem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,sourceMapped,sourceFound]
          by_cases inside : sourceOffset+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length
          · obtain ⟨extension,contents,functions⟩ := tableInit_preserves s f.toFrame index sourceIndex address f.module.ELEMS[sourceIndex] destination sourceOffset count object sourceObject
              typed.typed.store typed.contents mapped found sourceMapped sourceFound sameType inside
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension functions
            apply Or.inl
            refine ⟨_,by simp only [tableInit,split,popThree_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,and_true,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.TABLES[index]! < s.TABLES.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have source := Segment.table_init_steps s f.toFrame destination sourceOffset count index sourceIndex typed.typed.store frameWf
              destinationBound sourceOffsetBound countBound indexBound sourceIndexBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound
              (by rw [tableEq]; exact table_size_bound typed.contents (List.mem_of_getElem? found))
              (by rw [sourceEq]; exact elementBound) (by simpa only [tableEq,sourceEq] using inside)
            have full := bulk_empty_simulation s (Segment.tableInit s f.toFrame index sourceIndex destination sourceOffset count) ambient f rest
              (.TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)) after front [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [tableInit,split,popThree_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,ite_false],?_⟩
            have source := Segment.table_init_trap s f.toFrame destination sourceOffset count index sourceIndex typed.typed.store frameWf
              destinationBound sourceOffsetBound countBound indexBound sourceIndexBound (by rw [tableEq,sourceEq]; omega)
            have full := operand_trap_simulation s ambient f rest (.TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)) after front
              [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
end Itasca.Runtime.Abs.Stateful

end
