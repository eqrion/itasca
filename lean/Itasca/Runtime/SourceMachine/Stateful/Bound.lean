import Itasca.Runtime.SourceMachine.Stateful.TableRead
import Itasca.Runtime.SourceMachine.Stateful.TableSet
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Runtime.SourceMachine.Bound

/-!
Sections, each formerly its own module: TableTransfer, Transition, Ownership, Bound.
-/

/-! ## TableTransfer -/

section

/-!
Source table copy and initialization, retaining reference and segment bounds in the common transfer argument.
-/

/-! ## Table Copy -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
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

theorem table_copy_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
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
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
          have indexBound : index<2^32 := by cases instructionWf; rename_i valid _; cases valid; norm_num at *; omega
          have sourceIndexBound : sourceIndex<2^32 := by cases instructionWf; rename_i _ valid; cases valid; norm_num at *; omega
          have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          have sourceEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN sourceIndex) = sourceObject := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,sourceMapped,sourceFound]
          by_cases inside : sourceOffset+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length
          · obtain ⟨extension,contents⟩ := table_copy_preserves s f.toFrame index sourceIndex address sourceAddress destination sourceOffset count object sourceObject
              typed.typed.store typed.contents mapped sourceMapped found sourceFound sameType inside
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension rfl
            apply Or.inl
            refine ⟨_,by simp only [tableCopy,split,pop_three_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,and_true,ite_true,advance],
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
            refine ⟨by simp only [tableCopy,split,pop_three_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,ite_false],?_⟩
            have source := Segment.table_copy_trap s f.toFrame destination sourceOffset count index sourceIndex typed.typed.store frameWf
              destinationBound sourceOffsetBound countBound indexBound sourceIndexBound (by rw [tableEq,sourceEq]; omega)
            have full := operand_trap_simulation s ambient f rest (.TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)) after front
              [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## Table Init -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
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

theorem table_init_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
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
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
          have indexBound : index<2^32 := by cases instructionWf; rename_i valid _; cases valid; norm_num at *; omega
          have sourceIndexBound : sourceIndex<2^32 := by cases instructionWf; rename_i _ valid; cases valid; norm_num at *; omega
          have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          have sourceEq : fun_elem ⟨s,f.toFrame⟩ (.mk_uN sourceIndex) = sourceObject := by
            simp [fun_elem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,sourceMapped,sourceFound]
          by_cases inside : sourceOffset+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length
          · obtain ⟨extension,contents,functions⟩ := table_init_preserves s f.toFrame index sourceIndex address f.module.ELEMS[sourceIndex] destination sourceOffset count object sourceObject
              typed.typed.store typed.contents mapped found sourceMapped sourceFound sameType inside
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension functions
            apply Or.inl
            refine ⟨_,by simp only [tableInit,split,pop_three_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,and_true,ite_true,advance],
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
            refine ⟨by simp only [tableInit,split,pop_three_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,ite_false],?_⟩
            have source := Segment.table_init_trap s f.toFrame destination sourceOffset count index sourceIndex typed.typed.store frameWf
              destinationBound sourceOffsetBound countBound indexBound sourceIndexBound (by rw [tableEq,sourceEq]; omega)
            have full := operand_trap_simulation s ambient f rest (.TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)) after front
              [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
end Itasca.Runtime.SourceMachine.Stateful

end

end

/-! ## Transition -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

/-- The only nondeterministic choices are successful growth or permitted refusal. -/
structure Selection where
  memory : Option meminst := none
  table : Option tableinst := none

/-- Growth choices refer to the actual operands and selected source object. -/
def Selection.Allowed (choice : Selection) (op : Instruction) (s : store) (f : AFrame) : Prop :=
  match op with
  | .memoryGrow => ∀ front delta address object,
      f.vals = front ++ [integerVal .I32 delta] → f.module.MEMS[0]? = some address →
      s.MEMS[address]? = some object → MemoryGrowthChoice object delta choice.memory
  | .tableGrow index => ∀ front reference delta address object,
      f.vals = front ++ [val_ref reference,integerVal .I32 delta] →
      f.module.TABLES[index]? = some address → s.TABLES[address]? = some object →
      TableGrowthChoice object delta reference choice.table
  | _ => True

theorem Selection.refusal_allowed (op : Instruction) (s : store) (f : AFrame) :
    Selection.Allowed {} op s f := by
  cases op <;> simp only [Selection.Allowed]
  all_goals first | trivial | intros; constructor

def evaluate (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) : AResult :=
  match op with
  | .refNull type => refNull s f rest type after
  | .refFunc index => refFunc s f rest index after
  | .refIsNull => refIsNull s f rest after
  | .tableGet index => tableGet s f rest index after
  | .tableSet index => tableSet s f rest index after
  | .tableSize index => tableSize s f rest index after
  | .tableGrow index => tableGrow choice.table s f rest index after
  | .tableFill index => tableFill s f rest index after
  | .tableCopy index source => tableCopy s f rest index source after
  | .tableInit index source => tableInit s f rest index source after
  | .elemDrop index => elementDrop s f rest index after
  | .memorySize => memorySize s f rest after
  | .memoryGrow => memoryGrow choice.memory s f rest after
  | .memoryFill => memoryFill s f rest after
  | .memoryCopy => memoryCopy s f rest after
  | .memoryInit index => memoryInit s f rest index after
  | .dataDrop index => dataDrop s f rest index after

/-- This relation selects a runtime result without choosing successful allocation in advance. -/
def Transition (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Instruction) (result : AResult) : Prop :=
  ∃ choice, choice.Allowed op s.store f ∧ evaluate choice op s f rest after = result

def ResultSafe (initial : AState) : AResult → Prop
  | .next next => CoreTyped next ∧ Extend_store initial.store next.store ∧ NextSim initial next
  | .trap => ∃ count, 0 < count ∧ StepsHN count (decode initial) [] ⟨⟨initial.store,initial.ambient⟩,[.TRAP]⟩
  | _ => False

def Instruction.readOnly : Instruction → Bool
  | .refNull _ | .refFunc _ | .refIsNull | .tableGet _ | .tableSize _ | .memorySize => true
  | _ => false

theorem evaluate_read_store (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState) (readOnly : op.readOnly = true)
    (result : evaluate choice op s f rest after = .next next) : next.store = s.store := by
  cases op <;> simp only [Instruction.readOnly, Bool.false_eq_true] at readOnly
  all_goals simp only [evaluate,refNull,refFunc,refIsNull,tableGet,tableSize,memorySize,advance] at result
  all_goals repeat first | split at result | (cases result; rfl) | contradiction

theorem evaluate_safe (choice : Selection) (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (allowed : choice.Allowed op s f) :
    ResultSafe ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩
      (evaluate choice op ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after) := by
  cases op with
  | refNull type =>
    obtain ⟨next,result,fresh,simulation⟩ := ref_null_progress s ambient f rest type after typed
    have same := evaluate_read_store choice (.refNull type) ⟨s,ambient,{f with code := (.refNull type : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (refNull _ f rest type after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | refFunc index =>
    obtain ⟨next,result,fresh,simulation⟩ := ref_func_progress s ambient f rest index after typed
    have same := evaluate_read_store choice (.refFunc index) ⟨s,ambient,{f with code := (.refFunc index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (refFunc _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | refIsNull =>
    obtain ⟨next,result,fresh,simulation⟩ := ref_is_null_progress s ambient f rest after typed
    have same := evaluate_read_store choice (.refIsNull) ⟨s,ambient,{f with code := (.refIsNull : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (refIsNull _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | tableSize index =>
    obtain ⟨next,result,fresh,simulation⟩ := table_size_progress s ambient f rest index after typed
    have same := evaluate_read_store choice (.tableSize index) ⟨s,ambient,{f with code := (.tableSize index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (tableSize _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | memorySize =>
    obtain ⟨next,result,fresh,simulation⟩ := memory_size_progress s ambient f rest after typed
    have same := evaluate_read_store choice (.memorySize) ⟨s,ambient,{f with code := (.memorySize : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (memorySize _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | tableGet index =>
    rcases table_get_progress s ambient f rest index after typed with ⟨next,result,fresh,simulation⟩ | ⟨result,trap⟩
    · have same := evaluate_read_store choice (.tableGet index) ⟨s,ambient,{f with code := (.tableGet index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
      change ResultSafe _ (tableGet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
    · change ResultSafe _ (tableGet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableSet index =>
    rcases table_set_progress s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableSet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableSet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableFill index =>
    rcases table_fill_progress s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableFill _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableFill _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableCopy index source =>
    rcases table_copy_progress s ambient f rest index source after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableCopy _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableCopy _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableInit index source =>
    rcases table_init_progress s ambient f rest index source after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableInit _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableInit _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryFill =>
    rcases memory_fill_progress s ambient f rest  after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (memoryFill _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (memoryFill _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryCopy =>
    rcases memory_copy_progress s ambient f rest  after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (memoryCopy _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (memoryCopy _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryInit index =>
    rcases memory_init_progress s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (memoryInit _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (memoryInit _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | elemDrop index =>
    obtain ⟨next,result,fresh,extended,simulation⟩ := element_drop_progress s ambient f rest index after typed
    change ResultSafe _ (elementDrop _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | dataDrop index =>
    obtain ⟨next,result,fresh,extended,simulation⟩ := data_drop_progress s ambient f rest index after typed
    change ResultSafe _ (dataDrop _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | memoryGrow =>
    obtain ⟨front,delta,address,object,values,mapped,found,choices⟩ := memory_grow_choices s ambient f rest after typed
    obtain ⟨next,result,fresh,extended,simulation⟩ := choices choice.memory (allowed front delta address object values mapped found)
    change ResultSafe _ (memoryGrow _ _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | tableGrow index =>
    obtain ⟨front,reference,delta,address,object,values,mapped,found,choices⟩ := table_grow_choices s ambient f rest index after typed
    obtain ⟨next,result,fresh,extended,simulation⟩ := choices choice.table (allowed front reference delta address object values mapped found)
    change ResultSafe _ (tableGrow _ _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩

theorem transition_safe (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr) (result : AResult)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op result) :
    ResultSafe ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ result := by
  obtain ⟨choice,allowed,rfl⟩ := step
  exact evaluate_safe choice op s ambient f rest after typed allowed

theorem transition_next (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op (.next next)) :
    CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ next :=
  transition_safe op s ambient f rest after (.next next) typed step

theorem transition_trap (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op .trap) :
    ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩) []
      ⟨⟨s,ambient⟩,[.TRAP]⟩ :=
  transition_safe op s ambient f rest after .trap typed step

end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## Ownership -/

section

/-!
Stateful ownership preservation, composing primitive updates, bulk operations and growth under retained heap ownership.
-/

/-! ## Ownership Primitives -/

section

namespace Itasca.Runtime.SourceMachine.Ownership
open SpecExt Itasca.Runtime.Spec Stateful

theorem stateful_owned_advance {bounds s f rest next}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : advance s f rest = .next next) : StatefulOwned bounds next :=
  ⟨ownership_advance results frame frames step,by cases step; exact heap⟩

theorem as_reference_owned {bounds value reference} (owned : ValueOwned bounds value)
    (decoded : asReference value = some reference) : ValueOwned bounds (val_ref reference) := by
  cases value <;> simp only [asReference] at decoded <;> cases decoded <;> exact owned

theorem stateful_ref_null_owned {bounds s f rest next type after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : refNull s f rest type after = .next next) : StatefulOwned bounds next := by
  apply stateful_owned_advance heap results _ frames step
  refine ⟨frame.1,values_owned_append.mpr ⟨frame.2,?_⟩⟩
  cases type <;> simp [ValuesOwned,ValueOwned]

theorem stateful_ref_func_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (issued : ∀ address,f.module.FUNCS[index]? = some address → address < bounds.functions)
    (step : refFunc s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold refFunc at step
  split at step
  · contradiction
  next address mapped =>
    apply stateful_owned_advance heap results _ frames step
    exact ⟨frame.1,values_owned_append.mpr ⟨frame.2,values_owned_cons.mpr ⟨issued address mapped,values_owned_nil _⟩⟩⟩

theorem stateful_ref_is_null_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : refIsNull s f rest after = .next next) : StatefulOwned bounds next := by
  unfold refIsNull at step
  split at step
  · contradiction
  next front value popped =>
    have prefixOwned := (frame.2.pop popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance heap results _ frames step
      exact ⟨frame.1,values_owned_append.mpr ⟨prefixOwned,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩

theorem stateful_table_get_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableGet s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableGet at step
  split at step
  next front value address popped mapped =>
    have prefixOwned := (frame.2.pop popped).1
    split at step
    next position object decoded found =>
      split at step
      next inside =>
        apply stateful_owned_advance heap results _ frames step
        refine ⟨frame.1,values_owned_append.mpr ⟨prefixOwned,values_owned_cons.mpr ⟨?_,values_owned_nil _⟩⟩⟩
        exact heap.tables object (List.mem_of_getElem? found) _ (List.getElem_mem inside)
      · contradiction
    · contradiction
  · contradiction

theorem stateful_table_set_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableSet s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableSet at step
  split at step
  next first value address popped mapped =>
    have firstOwned := frame.2.pop popped
    split at step
    next front offset reference object previous decoded found =>
      have prefixOwned := (firstOwned.1.pop previous).1
      have valueOwned := as_reference_owned firstOwned.2 decoded
      repeat' first | split at step | contradiction
      all_goals
        apply stateful_owned_advance (step := step)
        · exact heap.table_write _ _ _ _ valueOwned
        · exact results
        · exact ⟨frame.1,prefixOwned⟩
        · exact frames
    · contradiction
  · contradiction

theorem stateful_table_size_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableSize s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableSize at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance heap results _ frames step
    exact ⟨frame.1,values_owned_append.mpr ⟨frame.2,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩

theorem stateful_memory_size_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memorySize s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memorySize at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance heap results _ frames step
    exact ⟨frame.1,values_owned_append.mpr ⟨frame.2,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩

theorem stateful_element_drop_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : elementDrop s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold elementDrop at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance (step := step)
    · exact heap.elem_drop f.toFrame index
    · exact results
    · exact frame
    · exact frames

theorem stateful_data_drop_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : dataDrop s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold dataDrop at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance (step := step)
    · exact heap.data_drop f.toFrame index
    · exact results
    · exact frame
    · exact frames
end Itasca.Runtime.SourceMachine.Ownership

end

/-! ## Ownership Bulk -/

section

namespace Itasca.Runtime.SourceMachine.Ownership
open SpecExt Itasca.Runtime.Spec Stateful

theorem ValuesOwned.pop_three {bounds values front a b c} (owned : ValuesOwned bounds values)
    (popped : Stateful.popThree values = some (front,a,b,c)) :
    ValuesOwned bounds front ∧ ValueOwned bounds a ∧ ValueOwned bounds b ∧ ValueOwned bounds c := by
  unfold Stateful.popThree at popped
  split at popped
  · contradiction
  next first last one =>
    have h1 := owned.pop one
    split at popped
    · contradiction
    next second middle two =>
      have h2 := h1.1.pop two
      split at popped
      · contradiction
      next third start three =>
        have h3 := h2.1.pop three
        cases popped
        exact ⟨h3.1,h3.2,h2.2,h1.2⟩

theorem stateful_memory_fill_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryFill s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memoryFill at step
  split at step
  next front offset value size address popped mapped =>
    have prefixOwned := (frame.2.pop_three popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.memory_fill _ _ _ _
      · exact results
      · exact ⟨frame.1,prefixOwned⟩
      · exact frames
  · contradiction

theorem stateful_memory_copy_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryCopy s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memoryCopy at step
  split at step
  next front offset value size address popped mapped =>
    have prefixOwned := (frame.2.pop_three popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.memory_copy _ _ _ _
      · exact results
      · exact ⟨frame.1,prefixOwned⟩
      · exact frames
  · contradiction

theorem stateful_memory_init_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryInit s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold memoryInit at step
  split at step
  next front offset value size address dataAddress popped mapped dataMapped =>
    have prefixOwned := (frame.2.pop_three popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.memory_init _ _ _ _ _
      · exact results
      · exact ⟨frame.1,prefixOwned⟩
      · exact frames
  · contradiction

theorem stateful_table_fill_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableFill s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableFill at step
  split at step
  next front offset value size address popped mapped =>
    have input := frame.2.pop_three popped
    split at step
    next destination reference count object destinationEq referenceEq countEq found =>
      have valueOwned := as_reference_owned input.2.2.1 referenceEq
      split at step
      next inside =>
        apply stateful_owned_advance (step := step)
        · exact heap.table_fill _ _ _ _ _ valueOwned
        · exact results
        · exact ⟨frame.1,input.1⟩
        · exact frames
      · contradiction
    · contradiction
  · contradiction

theorem stateful_table_copy_owned {bounds s f rest next index sourceIndex after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableCopy s f rest index sourceIndex after = .next next) : StatefulOwned bounds next := by
  unfold tableCopy at step
  split at step
  next front offset value size address sourceAddress popped mapped sourceMapped =>
    have prefixOwned := (frame.2.pop_three popped).1
    split at step
    next destination source count object sourceObject destinationEq sourceEq countEq found sourceFound =>
      split at step
      next inside =>
        apply stateful_owned_advance (step := step)
        · exact heap.table_copy _ _ _ _ _ _ _ _ _ _ mapped sourceMapped found sourceFound inside
        · exact results
        · exact ⟨frame.1,prefixOwned⟩
        · exact frames
      · contradiction
    · contradiction
  · contradiction

theorem stateful_table_init_owned {bounds s f rest next index sourceIndex after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableInit s f rest index sourceIndex after = .next next) : StatefulOwned bounds next := by
  unfold tableInit at step
  split at step
  next front offset value size address sourceAddress popped mapped sourceMapped =>
    have prefixOwned := (frame.2.pop_three popped).1
    split at step
    next destination source count object sourceObject destinationEq sourceEq countEq found sourceFound =>
      split at step
      next inside =>
        apply stateful_owned_advance (step := step)
        · exact heap.table_init _ _ _ _ _ _ _ _ sourceMapped sourceFound inside.1
        · exact results
        · exact ⟨frame.1,prefixOwned⟩
        · exact frames
      · contradiction
    · contradiction
  · contradiction
end Itasca.Runtime.SourceMachine.Ownership

end

/-! ## Ownership Growth -/

section

namespace Itasca.Runtime.SourceMachine.Ownership
open SpecExt Itasca.Runtime.Spec Stateful

theorem stateful_memory_grow_owned {bounds choice s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryGrow choice s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memoryGrow at step
  split at step
  next front value address popped mapped =>
    have prefixOwned := (frame.2.pop popped).1
    repeat' first | split at step | contradiction
    all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq,as_reference_value]
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.metadata rfl rfl rfl rfl
      · exact results
      · exact ⟨frame.1,values_owned_append.mpr ⟨prefixOwned,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩
      · exact frames
  · contradiction

theorem stateful_table_grow_owned {bounds choice s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (front : List val) (reference : ref) (delta address : Nat) (object : tableinst)
    (values : f.vals = front ++ [val_ref reference,integerVal .I32 delta])
    (mapped : f.module.TABLES[index]? = some address) (found : s.store.TABLES[address]? = some object)
    (allowed : TableGrowthChoice object delta reference choice)
    (step : tableGrow choice s f rest index after = .next next) : StatefulOwned bounds next := by
  have input : ValuesOwned bounds front ∧ ValueOwned bounds (val_ref reference) := by
    have owned := frame.2
    rw [values] at owned
    exact ⟨(values_owned_append.mp owned).1,(values_owned_cons.mp (values_owned_append.mp owned).2).1⟩
  have split : f.vals = (front ++ [val_ref reference]) ++ [integerVal .I32 delta] := by
    simpa [List.append_assoc] using values
  cases allowed with
  | refused =>
    simp only [tableGrow,split,pop_append,mapped,found,as_reference_value] at step
    repeat' first | split at step | contradiction
    all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq,as_reference_value]
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap
      · exact results
      · exact ⟨frame.1,values_owned_append.mpr ⟨input.1,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩
      · exact frames
  | @grown fresh grown =>
    have newHeap := heap.table_grow address object fresh delta reference (List.mem_of_getElem? found) input.2 grown
    simp only [tableGrow,split,pop_append,mapped,found,as_reference_value] at step
    repeat' first | split at step | contradiction
    all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq,as_reference_value]
    all_goals
      apply stateful_owned_advance (step := step)
      · exact newHeap
      · exact results
      · exact ⟨frame.1,values_owned_append.mpr ⟨input.1,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩
      · exact frames
end Itasca.Runtime.SourceMachine.Ownership

end

/-! ## Ownership -/

section

namespace Itasca.Runtime.SourceMachine.Ownership
open SpecExt Itasca.Runtime.Spec Stateful

theorem StatefulHeapOwned.frame_function {bounds s} {f : AFrame} {instruction : instr} {after : List instr}
    (heap : StatefulHeapOwned bounds s) (typed : FrameTyped s {f with code := instruction::after} [])
    (index address : Nat) (mapped : f.module.FUNCS[index]? = some address) : address < bounds.functions := by
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands typed
  have mappedBound := (List.getElem?_eq_some_iff.mp mapped).1
  have bound : index < C.FUNCS.length := by rw [←bindings.funcs.length_eq]; exact mappedBound
  obtain ⟨fn,found,_⟩ := bindings.funcs.get mappedBound bound
  simp only [List.get_eq_getElem] at found
  have addressEq : f.module.FUNCS[index] = address := (List.getElem?_eq_some_iff.mp mapped).2
  rw [addressEq] at found
  exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp found).1 heap.functions

theorem evaluate_owned (bounds : Bounds) (choice : Selection) (op : Instruction)
    (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (allowed : choice.Allowed op s f)
    (step : evaluate choice op ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after = .next next) :
    StatefulOwned bounds next := by
  have frame : FrameOwned bounds f := owned.values.2 {f with code := op.source::after} (List.mem_cons_self ..)
  have frames : ∀ item ∈ rest,FrameOwned bounds item := fun item member => owned.values.2 item (by simp [member])
  cases op with
  | refNull type =>
    exact stateful_ref_null_owned owned.heap owned.values.1 frame frames step
  | refIsNull =>
    exact stateful_ref_is_null_owned owned.heap owned.values.1 frame frames step
  | tableGet index =>
    exact stateful_table_get_owned owned.heap owned.values.1 frame frames step
  | tableSet index =>
    exact stateful_table_set_owned owned.heap owned.values.1 frame frames step
  | tableSize index =>
    exact stateful_table_size_owned owned.heap owned.values.1 frame frames step
  | tableFill index =>
    exact stateful_table_fill_owned owned.heap owned.values.1 frame frames step
  | tableCopy index source =>
    exact stateful_table_copy_owned owned.heap owned.values.1 frame frames step
  | tableInit index source =>
    exact stateful_table_init_owned owned.heap owned.values.1 frame frames step
  | elemDrop index =>
    exact stateful_element_drop_owned owned.heap owned.values.1 frame frames step
  | memorySize =>
    exact stateful_memory_size_owned owned.heap owned.values.1 frame frames step
  | memoryGrow =>
    exact stateful_memory_grow_owned owned.heap owned.values.1 frame frames step
  | memoryFill =>
    exact stateful_memory_fill_owned owned.heap owned.values.1 frame frames step
  | memoryCopy =>
    exact stateful_memory_copy_owned owned.heap owned.values.1 frame frames step
  | memoryInit index =>
    exact stateful_memory_init_owned owned.heap owned.values.1 frame frames step
  | dataDrop index =>
    exact stateful_data_drop_owned owned.heap owned.values.1 frame frames step
  | refFunc index =>
    apply stateful_ref_func_owned owned.heap owned.values.1 frame frames _ step
    intro address mapped
    have active : FrameTyped s {f with code := (.refFunc index : Instruction).source::after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    exact owned.heap.frame_function active index address mapped
  | tableGrow index =>
    obtain ⟨front,reference,delta,address,object,values,mapped,found,_⟩ := table_grow_choices s ambient f rest index after typed
    exact stateful_table_grow_owned owned.heap owned.values.1 frame frames front reference delta address object
      values mapped found (allowed front reference delta address object values mapped found) step

theorem stateful_transition_owned (bounds : Bounds) (op : Instruction)
    (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op (.next next)) :
    StatefulOwned bounds next := by
  obtain ⟨choice,allowed,evaluated⟩ := step
  exact evaluate_owned bounds choice op s ambient f rest after next typed owned allowed evaluated
end Itasca.Runtime.SourceMachine.Ownership

end

end

/-! ## Bound -/

section

/-!
Stateful transition metadata and code-bound preservation, consumed by cumulative execution.
-/

/-! ## Metadata -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem evaluate_frame (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState)
    (result : evaluate choice op s f rest after = .next next) :
    ∃ values, next.frames = {f with code := after, vals := values}::rest ∧
      next.ambient = s.ambient ∧ next.results = s.results := by
  cases op <;> simp only [evaluate,refNull,refFunc,refIsNull,tableGet,tableSet,tableSize,tableGrow,
    tableFill,tableCopy,tableInit,elementDrop,memorySize,memoryGrow,memoryFill,memoryCopy,memoryInit,dataDrop] at result
  all_goals repeat first | split at result | contradiction
  all_goals cases result <;> exact ⟨_,rfl,rfl,rfl⟩

theorem transition_frame (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Instruction) (next : AState) (step : Transition s f rest after op (.next next)) :
    ∃ values, next.frames = {f with code := after,vals := values}::rest ∧
      next.ambient = s.ambient ∧ next.results = s.results := by
  obtain ⟨choice,_,result⟩ := step
  exact evaluate_frame choice op s f rest after next result
theorem table_fill_functions (s : store) (f : frame) (index destination : Nat) (value : ref) (count : Nat) :
    (Segment.tableFill s f index destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s destination with
  | zero => rfl
  | succ count ih => exact ih (Segment.tableWrite s f index destination value) (destination+1)

theorem memory_fill_functions (s : store) (f : frame) (destination value count : Nat) :
    (Segment.memoryFill s f destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s destination with
  | zero => rfl
  | succ count ih => exact ih (Segment.memoryWrite s f destination (Segment.fillByte value)) (Segment.next32 destination)

theorem memory_init_functions (s : store) (f : frame) (index destination source count : Nat) :
    (Segment.memoryInit s f index destination source count).FUNCS = s.FUNCS := by
  induction count generalizing s destination source with
  | zero => rfl
  | succ count ih => exact ih _ _ _

theorem table_init_functions (s : store) (f : frame) (index sourceIndex destination source count : Nat) :
    (Segment.tableInit s f index sourceIndex destination source count).FUNCS = s.FUNCS := by
  rw [Segment.table_init_eq]

theorem evaluate_functions (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState)
    (result : evaluate choice op s f rest after = .next next) : next.store.FUNCS = s.store.FUNCS := by
  cases op <;> simp only [evaluate,refNull,refFunc,refIsNull,tableGet,tableSet,tableSize,tableGrow,
    tableFill,tableCopy,tableInit,elementDrop,memorySize,memoryGrow,memoryFill,memoryCopy,memoryInit,dataDrop,advance] at result
  all_goals repeat' first | split at result | contradiction
  all_goals cases result
  all_goals first | rfl | apply table_fill_functions | apply memory_fill_functions | apply table_init_functions | apply memory_init_functions

theorem transition_functions (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Instruction) (next : AState) (step : Transition s f rest after op (.next next)) :
    next.store.FUNCS = s.store.FUNCS := by
  obtain ⟨choice,_,result⟩ := step
  exact evaluate_functions choice op s f rest after next result
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## Bound -/

section

namespace Itasca.Runtime.SourceMachine.Stateful

theorem transition_bound (bound : Nat) (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (bounded : CodeBound bound ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op (.next next)) :
    CodeBound bound next := by
  obtain ⟨values,frames,_,_⟩ := transition_frame _ _ _ _ _ _ step
  have functions := transition_functions _ _ _ _ _ _ step
  have active := bounded.frames {f with code := op.source::after} (List.mem_cons_self ..)
  refine ⟨bounded.positive,?_,?_⟩
  · rw [frames]
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · refine ⟨?_,active.2⟩
      have headBound : sizeOf (op.source::after) ≤ bound := active.1
      simp only [List.cons.sizeOf_spec] at headBound
      change sizeOf after ≤ bound
      omega
    · exact bounded.frames frame (List.mem_cons_of_mem _ member)
  · simpa only [functions] using bounded.functions
end Itasca.Runtime.SourceMachine.Stateful

end

end
