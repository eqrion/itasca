import Exec.Spec.Typing.MemorySetTyping
import Exec.Spec.Typing.TableSetTyping
import Exec.Spec.Typing.GrowthStoreTyping

/-! Successful and refused memory/table growth preserve source store, frame,
and stack typing under arbitrary surrounding stack types. -/
namespace Exec.Spec
open SpecExt

theorem growth_failure_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) {args : List val} {op : admininstr}
    (signature : writeInstructionSignature op=some (args.length,[.I32]))
    (result : num_) (resultWf : wf_admininstr (.CONST .I32 result)) {input output : List valtype}
    (typed : Instrs_ok2 s context (vals args++[op]) (.mk_functype (.mk_list input) (.mk_list output))) :
    WriteTypingResult s ⟨s,frame⟩ context [.CONST .I32 result] input output := by
  obtain ⟨base,params,primitive,arguments,inputSub,outputSub⟩ := write_operands_effect typed signature
  have wf := instrs_ok2_wf typed
  have valueTyped := Val_ok.numtype s .I32 result wf.1 (val_wf_of_admin resultWf)
  exact ⟨extend_store_refl _ wf.1,storeTyped,environment,
    realize_write_result inputSub outputSub (values_instrs_ok wf.1 wf.2.1 (.cons valueTyped .nil))⟩

theorem memory_grow_context_bound {s : store} {context : _root_.context} {instruction : admininstr}
    {input output : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (same : instruction=.MEMORY_GROW) : 0<context.MEMS.length := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases source <;> simp [admininstr_instr] at same
    cases primitive
    assumption
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem memory_growth_state_typed {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) (bound : 0<context.MEMS.length)
    (delta : Nat) (next : meminst) (grown : fun_growmemory (fun_mem ⟨s,frame⟩ (.mk_uN 0)) delta (some next))
    {after : state} (updated : fun_with_meminst ⟨s,frame⟩ (.mk_uN 0) next after) :
    match after with
    | ⟨store,nextFrame⟩ => nextFrame=frame ∧ Extend_store s store ∧ Store_ok store := by
  obtain ⟨address,object,addressFound,found⟩ := environment.memory_lookup (.mk_uN 0) bound
  simp only [proj_uN_0] at addressFound
  have actualAddress : frame.MODULE.MEMS[0]! = address := by
    simp only [List.getElem!_eq_getElem?_getD,addressFound,Option.getD_some]
  have actualGrowth : fun_growmemory s.MEMS[address]! delta (some next) := by
    simpa only [fun_mem,proj_uN_0,actualAddress] using grown
  cases updated
  have givenPost : wf_state ⟨{s with MEMS := s.MEMS.modify frame.MODULE.MEMS[0]! (fun _ => next)},frame⟩ := by assumption
  have normalizedPost : wf_state ⟨{s with MEMS := s.MEMS.set address next},frame⟩ := by
    simpa only [proj_uN_0,actualAddress,list_modify_as_set] using givenPost
  have effect := memory_growth_store_typed storeTyped address (List.getElem?_eq_some_iff.mp found).1 delta next actualGrowth
    (wf_state_parts normalizedPost).1
  simp only [proj_uN_0,actualAddress,list_modify_as_set]
  exact ⟨True.intro,effect⟩

theorem memory_grow_success_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) (delta : Nat) (next : meminst)
    (grown : fun_growmemory (fun_mem ⟨s,frame⟩ (.mk_uN 0)) delta (some next))
    {after : state} (updated : fun_with_meminst ⟨s,frame⟩ (.mk_uN 0) next after)
    (result : num_) (resultWf : wf_admininstr (.CONST .I32 result)) {input output : List valtype}
    (typed : Instrs_ok2 s context [.CONST .I32 (.mk_num__0 .I32 (.mk_uN delta)),.MEMORY_GROW]
      (.mk_functype (.mk_list input) (.mk_list output))) :
    WriteTypingResult s after context [.CONST .I32 result] input output := by
  change Instrs_ok2 s context (vals [.CONST .I32 (.mk_num__0 .I32 (.mk_uN delta))]++[.MEMORY_GROW]) _ at typed
  obtain ⟨base,params,primitive,arguments,inputSub,outputSub⟩ := write_operands_effect typed rfl
  have effect := memory_growth_state_typed storeTyped environment (memory_grow_context_bound primitive rfl) delta next grown updated
  have wf := instrs_ok2_wf typed
  cases after with
  | mk_state store nextFrame =>
    obtain ⟨same,extension,postTyped⟩ := effect
    cases same
    have valueTyped := Val_ok.numtype store .I32 result (extend_store_wf extension).2 (val_wf_of_admin resultWf)
    exact ⟨extension,postTyped,FrameEnvironment.extend extension environment,
      realize_write_result inputSub outputSub (values_instrs_ok (extend_store_wf extension).2 wf.2.1 (.cons valueTyped .nil))⟩

theorem table_grow_operand {s : store} {context : _root_.context} {instruction : admininstr} (index : idx)
    (delta : Nat) (reference : ref) {params results : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list params) (.mk_list results)))
    (same : instruction=.TABLE_GROW index)
    (arguments : ResultsTyped s params [val_ref reference,.CONST .I32 (.mk_num__0 .I32 (.mk_uN delta))]) :
    ∃ type limits, proj_uN_0 index<context.TABLES.length ∧
      context.TABLES[proj_uN_0 index]! = .mk_tabletype limits type ∧ Ref_ok s reference type := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases source <;> simp [admininstr_instr] at same
    cases same
    cases primitive
    rename_i type limits _ _ _ _ _
    cases arguments with
    | cons referenceTyped rest =>
      exact ⟨type,limits,by assumption,by assumption,reference_value_inversion reference referenceTyped⟩
  case ref =>
    rename_i actual type _ _ _
    cases actual <;> simp [admininstr_ref] at same
  all_goals cases same

theorem table_growth_state_typed {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) (index : idx)
    (bound : proj_uN_0 index<context.TABLES.length) (delta : Nat) (reference : ref) (next : tableinst)
    (referenceTyped : Ref_ok s reference (sourceTableElementType (fun_table ⟨s,frame⟩ index).TYPE))
    (grown : fun_growtable (fun_table ⟨s,frame⟩ index) delta reference (some next))
    {after : state} (updated : fun_with_tableinst ⟨s,frame⟩ index next after) :
    match after with
    | ⟨store,nextFrame⟩ => nextFrame=frame ∧ Extend_store s store ∧ Store_ok store := by
  obtain ⟨address,object,addressFound,found,objectType⟩ := environment.table_lookup index bound
  have actualAddress : frame.MODULE.TABLES[proj_uN_0 index]! = address := by
    simp only [List.getElem!_eq_getElem?_getD,addressFound,Option.getD_some]
  have actualGrowth : fun_growtable s.TABLES[address]! delta reference (some next) := by
    simpa only [fun_table,actualAddress] using grown
  have actualTyped : Ref_ok s reference (sourceTableElementType s.TABLES[address]!.TYPE) := by
    simpa only [fun_table,actualAddress] using referenceTyped
  cases updated
  have givenPost : wf_state ⟨{s with TABLES := s.TABLES.modify (frame.MODULE.TABLES[proj_uN_0 index]!) (fun _ => next)},frame⟩ := by assumption
  have normalizedPost : wf_state ⟨{s with TABLES := s.TABLES.set address next},frame⟩ := by
    simpa only [actualAddress,list_modify_as_set] using givenPost
  have effect := table_growth_store_typed storeTyped address (List.getElem?_eq_some_iff.mp found).1 delta reference actualTyped next actualGrowth
    (wf_state_parts normalizedPost).1
  simp only [actualAddress,list_modify_as_set]
  exact ⟨True.intro,effect⟩

theorem table_grow_success_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) (index : idx)
    (delta : Nat) (reference : ref) (next : tableinst)
    (grown : fun_growtable (fun_table ⟨s,frame⟩ index) delta reference (some next))
    {after : state} (updated : fun_with_tableinst ⟨s,frame⟩ index next after)
    (result : num_) (resultWf : wf_admininstr (.CONST .I32 result)) {input output : List valtype}
    (typed : Instrs_ok2 s context [admininstr_ref reference,.CONST .I32 (.mk_num__0 .I32 (.mk_uN delta)),.TABLE_GROW index]
      (.mk_functype (.mk_list input) (.mk_list output))) :
    WriteTypingResult s after context [.CONST .I32 result] input output := by
  have representation : admininstr_val (val_ref reference)=admininstr_ref reference := by cases reference <;> rfl
  rw [← representation] at typed
  change Instrs_ok2 s context (vals [val_ref reference,.CONST .I32 (.mk_num__0 .I32 (.mk_uN delta))]++[.TABLE_GROW index]) _ at typed
  obtain ⟨base,params,primitive,arguments,inputSub,outputSub⟩ := write_operands_effect typed rfl
  obtain ⟨type,limits,bound,typeEq,referenceTyped⟩ := table_grow_operand index delta reference primitive rfl arguments
  obtain ⟨address,object,addressFound,found,objectType⟩ := environment.table_lookup index bound
  have actualAddress : frame.MODULE.TABLES[proj_uN_0 index]! = address := by
    simp only [List.getElem!_eq_getElem?_getD,addressFound,Option.getD_some]
  have actualObject : s.TABLES[address]! = object := by
    simp only [List.getElem!_eq_getElem?_getD,found,Option.getD_some]
  have actualType : sourceTableElementType (fun_table ⟨s,frame⟩ index).TYPE=type := by
    change sourceTableElementType s.TABLES[frame.MODULE.TABLES[proj_uN_0 index]!]!.TYPE=type
    rw [actualAddress,actualObject,objectType,typeEq]
    rfl
  have actualTyped : Ref_ok s reference (sourceTableElementType (fun_table ⟨s,frame⟩ index).TYPE) := by
    rw [actualType]
    exact referenceTyped
  have effect := table_growth_state_typed storeTyped environment index bound delta reference next actualTyped grown updated
  have wf := instrs_ok2_wf typed
  cases after with
  | mk_state store nextFrame =>
    obtain ⟨same,extension,postTyped⟩ := effect
    cases same
    have valueTyped := Val_ok.numtype store .I32 result (extend_store_wf extension).2 (val_wf_of_admin resultWf)
    exact ⟨extension,postTyped,FrameEnvironment.extend extension environment,
      realize_write_result inputSub outputSub (values_instrs_ok (extend_store_wf extension).2 wf.2.1 (.cons valueTyped .nil))⟩

end Exec.Spec
