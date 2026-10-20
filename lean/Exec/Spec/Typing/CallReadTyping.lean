import Exec.Spec.Typing.BlockReadTyping

/-! Direct and indirect dispatch preserve semantic operand and result types
using actual module bindings and the selected function signature. -/

namespace Exec.Spec
open SpecExt

theorem call_primitive_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) {instruction : admininstr} (index : idx)
    {input output : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (same : instruction=.CALL index) :
    Instrs_ok2 s context [.CALL_ADDR frame.MODULE.FUNCS[proj_uN_0 index]!]
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
    have selectedType : context.FUNCS[proj_uN_0 index]! = .mk_functype (.mk_list input) (.mk_list output) := by assumption
    have paired := environment.function_addresses
    have addressBound : proj_uN_0 index<frame.MODULE.FUNCS.length := by rw [paired.length_eq]; exact bound
    have relation := paired.get addressBound bound
    have selected : Externaddr_ok s (.FUNC frame.MODULE.FUNCS[proj_uN_0 index]!)
        (.FUNC (.mk_functype (.mk_list input) (.mk_list output))) := by
      have actual : Externaddr_ok s (.FUNC frame.MODULE.FUNCS[proj_uN_0 index]!)
          (.FUNC context.FUNCS[proj_uN_0 index]!) := by
        simpa only [List.get_eq_getElem,List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,
          List.getElem?_eq_getElem addressBound,Option.getD_some] using relation
      rw [selectedType] at actual
      exact actual
    exact .instr _ _ _ _ _ (.call_addr _ _ _ _ _ selected storeWf contextWf (.admininstr_case_70 _) (.externtype_case_0 _))
      storeWf contextWf (.admininstr_case_70 _)
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem call_read_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (index : idx) {input output : List valtype}
    (typed : Instrs_ok2 s context [.CALL index] (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [.CALL_ADDR frame.MODULE.FUNCS[proj_uN_0 index]!]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  apply singleton_typing_at_context typed
  intro params results primitive
  exact call_primitive_preserved environment index primitive rfl

theorem consume_value_at_context {s : store} {context : _root_.context} (argument : val)
    (op : admininstr) (after : List admininstr) {input output : List valtype}
    (typed : Instrs_ok2 s context [admininstr_val argument,op] (.mk_functype (.mk_list input) (.mk_list output)))
    (operation : ∀ params results, Instr_ok2 s context op (.mk_functype (.mk_list params) (.mk_list results)) →
      ∃ operands type, params=operands++[type] ∧
        Instrs_ok2 s context after (.mk_functype (.mk_list operands) (.mk_list results))) :
    Instrs_ok2 s context after (.mk_functype (.mk_list input) (.mk_list output)) := by
  change Instrs_ok2 s context (vals [argument]++[op]) _ at typed
  obtain ⟨base,types,inputBase,argsTyped,called⟩ := value_prefix_typing typed
  cases argsTyped with
  | cons argumentTyped rest =>
    cases rest
    rename_i argumentType
    obtain ⟨callBase,params,results,primitive,callSub,outputSub⟩ := instruction_typing_effect called op rfl
    obtain ⟨operands,type,rfl,afterTyped⟩ := operation params results primitive
    have sub : Resulttype_sub (.mk_list (base++[argumentType])) (.mk_list ((callBase++operands)++[type])) := by
      simpa only [List.append_assoc] using callSub
    have bases := resulttype_sub_prefix sub rfl
    exact instrs_subtype (instrs_frame afterTyped callBase) (resulttype_sub_trans inputBase bases) outputSub

theorem indirect_call_primitive_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) {instruction : admininstr} (table typeIndex : idx)
    (address : Nat) {input output : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (same : instruction=.CALL_INDIRECT table typeIndex)
    (addressBound : address<s.FUNCS.length) (signature : fun_type ⟨s,frame⟩ typeIndex=s.FUNCS[address]!.TYPE) :
    ∃ operands, input=operands++[.I32] ∧ Instrs_ok2 s context [.CALL_ADDR address]
      (.mk_functype (.mk_list operands) (.mk_list output)) := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    have storeWf : wf_store s := by assumption
    have contextWf : wf_context context := by assumption
    cases source <;> simp [admininstr_instr] at same
    rcases same with ⟨sameTable,sameType⟩
    cases sameTable
    cases sameType
    cases primitive
    rename_i params limits _ _ _ _ _ _ _
    have selectedType : context.TYPES[proj_uN_0 typeIndex]! = .mk_functype (.mk_list params) (.mk_list output) := by assumption
    have moduleTypes := moduleinst_types_agree environment.moduleTyped
    change frame.MODULE.TYPES=context.TYPES at moduleTypes
    have actualSignature : s.FUNCS[address]!.TYPE=.mk_functype (.mk_list params) (.mk_list output) := by
      rw [← signature]
      simpa only [fun_type,moduleTypes] using selectedType
    have external := Externaddr_ok.func s address s.FUNCS[address]! addressBound rfl storeWf (.externtype_case_0 _)
    rw [actualSignature] at external
    refine ⟨params,rfl,?_⟩
    exact .instr _ _ _ _ _ (.call_addr _ _ _ _ _ external storeWf contextWf (.admininstr_case_70 _) (.externtype_case_0 _))
      storeWf contextWf (.admininstr_case_70 _)
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem indirect_call_read_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (condition : num_) (table typeIndex : idx) (address : Nat)
    {input output : List valtype}
    (typed : Instrs_ok2 s context [.CONST .I32 condition,.CALL_INDIRECT table typeIndex]
      (.mk_functype (.mk_list input) (.mk_list output)))
    (addressBound : address<s.FUNCS.length) (signature : fun_type ⟨s,frame⟩ typeIndex=s.FUNCS[address]!.TYPE) :
    Instrs_ok2 s context [.CALL_ADDR address] (.mk_functype (.mk_list input) (.mk_list output)) := by
  apply consume_value_at_context (.CONST .I32 condition) (.CALL_INDIRECT table typeIndex) [.CALL_ADDR address] typed
  intro params results primitive
  obtain ⟨operands,same,called⟩ := indirect_call_primitive_preserved environment table typeIndex address primitive rfl addressBound signature
  exact ⟨operands,.I32,same,called⟩

end Exec.Spec
