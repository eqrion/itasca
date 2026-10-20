import Exec.Spec.Typing.StoreComponentTyping
import Exec.Spec.Typing.FrameReadTyping

/-! Typed global/table payloads and function references follow actual module
address maps; read replacements retain arbitrary operand prefixes. -/

namespace Exec.Spec
open SpecExt

theorem FrameEnvironment.global_lookup {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (index : idx) (bound : proj_uN_0 index<context.GLOBALS.length) :
    ∃ address object, frame.MODULE.GLOBALS[proj_uN_0 index]?=some address ∧
      s.GLOBALS[address]?=some object ∧ object.TYPE=context.GLOBALS[proj_uN_0 index]! := by
  have paired := environment.global_addresses
  have addressBound : proj_uN_0 index<frame.MODULE.GLOBALS.length := by rw [paired.length_eq]; exact bound
  have relation := paired.get addressBound bound
  simp only [List.get_eq_getElem] at relation
  obtain ⟨object,found,same⟩ := external_global_lookup relation
  refine ⟨frame.MODULE.GLOBALS[proj_uN_0 index],object,List.getElem?_eq_getElem addressBound,found,?_⟩
  simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using same

theorem SourceStoreComponents.global_value {s : store} (components : SourceStoreComponents s)
    {address : Nat} {object : globalinst} {mutable : «mut»} {type : valtype}
    (found : s.GLOBALS[address]?=some object) (same : object.TYPE=.mk_globaltype mutable type) :
    Val_ok s object.VALUE type := by
  have typed := components.globals object (List.mem_of_getElem? found)
  cases typed with
  | mk_Globalinst_ok actual valueType value globalType valueTyped _ _ =>
    cases same
    exact valueTyped

theorem FrameEnvironment.global_value {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (components : SourceStoreComponents s) (index : idx)
    {mutable : «mut»} {type : valtype} (bound : proj_uN_0 index<context.GLOBALS.length)
    (same : context.GLOBALS[proj_uN_0 index]! = .mk_globaltype mutable type) :
    Val_ok s (fun_global ⟨s,frame⟩ index).VALUE type := by
  obtain ⟨address,object,addressFound,found,typeEq⟩ := environment.global_lookup index bound
  have actual := components.global_value found (typeEq.trans same)
  simpa only [fun_global,List.getElem!_eq_getElem?_getD,addressFound,Option.getD_some,found] using actual

theorem FrameEnvironment.table_lookup {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (index : idx) (bound : proj_uN_0 index<context.TABLES.length) :
    ∃ address object, frame.MODULE.TABLES[proj_uN_0 index]?=some address ∧
      s.TABLES[address]?=some object ∧ sourceTableElementType object.TYPE=sourceTableElementType context.TABLES[proj_uN_0 index]! := by
  have paired := environment.table_addresses
  have addressBound : proj_uN_0 index<frame.MODULE.TABLES.length := by rw [paired.length_eq]; exact bound
  have relation := paired.get addressBound bound
  simp only [List.get_eq_getElem] at relation
  obtain ⟨object,found,same⟩ := external_table_lookup relation
  refine ⟨frame.MODULE.TABLES[proj_uN_0 index],object,List.getElem?_eq_getElem addressBound,found,?_⟩
  simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using same

theorem SourceStoreComponents.table_references {s : store} (components : SourceStoreComponents s)
    {object : tableinst} (member : object ∈ s.TABLES) :
    Forall (fun value => Ref_ok s value (sourceTableElementType object.TYPE)) object.REFS := by
  have typed := components.tables object member
  cases typed with
  | mk_Tableinst_ok count maximum type refs _ refsOk _ _ _ _ => exact refsOk

theorem FrameEnvironment.table_references {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (components : SourceStoreComponents s) (index : idx)
    {limits : _root_.limits} {type : reftype} (bound : proj_uN_0 index<context.TABLES.length)
    (same : context.TABLES[proj_uN_0 index]! = .mk_tabletype limits type) :
    Forall (fun value => Ref_ok s value type) (fun_table ⟨s,frame⟩ index).REFS := by
  obtain ⟨address,object,addressFound,found,typeEq⟩ := environment.table_lookup index bound
  have refs := components.table_references (List.mem_of_getElem? found)
  rw [typeEq,same] at refs
  simpa only [sourceTableElementType,fun_table,List.getElem!_eq_getElem?_getD,addressFound,Option.getD_some,found] using refs

theorem FrameEnvironment.function_reference {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (storeWf : wf_store s) (index : idx)
    (bound : proj_uN_0 index<context.FUNCS.length) :
    Val_ok s (.REF_FUNC_ADDR frame.MODULE.FUNCS[proj_uN_0 index]!) .FUNCREF := by
  have paired := environment.function_addresses
  have addressBound : proj_uN_0 index<frame.MODULE.FUNCS.length := by rw [paired.length_eq]; exact bound
  have relation := paired.get addressBound bound
  have selected : Externaddr_ok s (.FUNC frame.MODULE.FUNCS[proj_uN_0 index]!) (.FUNC context.FUNCS[proj_uN_0 index]!) := by
    simpa only [List.get_eq_getElem,List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,
      List.getElem?_eq_getElem addressBound,Option.getD_some] using relation
  exact .reftype _ (.REF_FUNC_ADDR _) _ (.func _ _ _ selected storeWf (.externtype_case_0 _)) storeWf

theorem global_get_primitive_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (components : SourceStoreComponents s)
    {instruction : admininstr} (index : idx) {input output : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (same : instruction=.GLOBAL_GET index) :
    Instrs_ok2 s context [admininstr_val (fun_global ⟨s,frame⟩ index).VALUE]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    have storeWf : wf_store s := by assumption
    have contextWf : wf_context context := by assumption
    cases source <;> simp [admininstr_instr] at same
    cases same
    cases primitive
    rename_i type mutable _ _ _ _
    have bound : proj_uN_0 index<context.GLOBALS.length := by assumption
    have typeEq : context.GLOBALS[proj_uN_0 index]! = .mk_globaltype mutable type := by assumption
    exact values_instrs_ok storeWf contextWf (.cons (environment.global_value components index bound typeEq) .nil)
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem ref_func_primitive_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) {instruction : admininstr} (index : idx)
    {input output : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (same : instruction=.REF_FUNC index) :
    Instrs_ok2 s context [.REF_FUNC_ADDR frame.MODULE.FUNCS[proj_uN_0 index]!]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    have storeWf : wf_store s := by assumption
    have contextWf : wf_context context := by assumption
    cases source <;> simp [admininstr_instr] at same
    cases same
    cases primitive
    have bound : proj_uN_0 index<context.FUNCS.length := by assumption
    exact values_instrs_ok storeWf contextWf (.cons (environment.function_reference storeWf index bound) .nil)
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem value_operation_at_context {s : store} {context : _root_.context}
    {args : List val} {op : admininstr} {after : List admininstr} {input output : List valtype}
    (typed : Instrs_ok2 s context (vals args++[op]) (.mk_functype (.mk_list input) (.mk_list output)))
    (operation : ∀ params results, Instr_ok2 s context op (.mk_functype (.mk_list params) (.mk_list results)) →
      params.length=args.length ∧ (ResultsTyped s params args →
        Instrs_ok2 s context after (.mk_functype (.mk_list []) (.mk_list results)))) :
    Instrs_ok2 s context after (.mk_functype (.mk_list input) (.mk_list output)) := by
  obtain ⟨base,types,inputBase,argsTyped,called⟩ := value_prefix_typing typed
  obtain ⟨callBase,params,results,primitive,callSub,outputSub⟩ := instruction_typing_effect called op rfl
  obtain ⟨arity,effect⟩ := operation params results primitive
  have count : types.length=params.length := by have same := argsTyped.length_eq; omega
  have baseSub := resulttype_sub_prefix callSub count
  have baseCount := (resulttype_sub_iff.mp baseSub).length_eq
  have argsSub := resulttype_sub_suffix callSub baseCount
  have framed := instrs_frame (effect (resultsTyped_subtype argsTyped argsSub)) callBase
  simp only [List.append_nil] at framed
  exact instrs_subtype framed (resulttype_sub_trans inputBase baseSub) outputSub

theorem table_get_primitive_result {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (components : SourceStoreComponents s)
    {instruction : admininstr} (index : idx) (position : Nat) {input output : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (same : instruction=.TABLE_GET index)
    (elementBound : position<(fun_table ⟨s,frame⟩ index).REFS.length) :
    input=[.I32] ∧ ∃ type, output=[valtype_reftype type] ∧
      Ref_ok s (fun_table ⟨s,frame⟩ index).REFS[position]! type := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases source <;> simp [admininstr_instr] at same
    cases same
    cases primitive
    rename_i type limits _ _ _ _ _
    have bound : proj_uN_0 index<context.TABLES.length := by assumption
    have typeEq : context.TABLES[proj_uN_0 index]! = .mk_tabletype limits type := by assumption
    have refs := environment.table_references components index bound typeEq
    have member : (fun_table ⟨s,frame⟩ index).REFS[position]! ∈ (fun_table ⟨s,frame⟩ index).REFS := by
      simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem elementBound,Option.getD_some] using List.getElem_mem elementBound
    exact ⟨rfl,type,rfl,refs _ member⟩
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem table_get_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (components : SourceStoreComponents s)
    (index : idx) (condition : num_) (position : Nat) {input output : List valtype}
    (typed : Instrs_ok2 s context [.CONST .I32 condition,.TABLE_GET index]
      (.mk_functype (.mk_list input) (.mk_list output)))
    (elementBound : position<(fun_table ⟨s,frame⟩ index).REFS.length) :
    Instrs_ok2 s context [admininstr_ref (fun_table ⟨s,frame⟩ index).REFS[position]!]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  change Instrs_ok2 s context (vals [.CONST .I32 condition]++[.TABLE_GET index]) _ at typed
  apply value_operation_at_context typed
  intro params results primitive
  have storeWf : wf_store s := by
    generalize same : admininstr.TABLE_GET index=instruction at primitive
    cases primitive <;> assumption
  have contextWf := (instrs_ok2_wf typed).2.1
  obtain ⟨rfl,type,rfl,referenceTyped⟩ := table_get_primitive_result environment components index position primitive rfl elementBound
  refine ⟨rfl,fun _ => ?_⟩
  have valueTyped := Val_ok.reftype _ _ _ referenceTyped storeWf
  have representation : admininstr_val (val_ref (fun_table ⟨s,frame⟩ index).REFS[position]!) =
      admininstr_ref (fun_table ⟨s,frame⟩ index).REFS[position]! := by
    cases (fun_table ⟨s,frame⟩ index).REFS[position]! <;> rfl
  simpa only [vals,List.map_cons,List.map_nil,representation] using
    values_instrs_ok storeWf contextWf (.cons valueTyped .nil)

end Exec.Spec
