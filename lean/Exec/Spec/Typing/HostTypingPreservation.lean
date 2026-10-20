import Exec.Spec.Typing.StackTypingInversion
import Exec.Spec.Typing.AdminExtension

/-! Direct host calls preserve semantic instruction and configuration typing.
Result types are recovered from the original call derivation and signature. -/

namespace Exec.Spec
open SpecExt

theorem external_function_signature {s : store} {address : externaddr} {type : externtype}
    (typed : Externaddr_ok s address type) (fa : funcaddr) (ft : functype)
    (sameAddress : address=.FUNC fa) (sameType : type=.FUNC ft) :
    s.FUNCS[fa]?.map funcinst.TYPE = some ft := by
  induction typed with
  | func address fn bound found _ _ =>
    cases sameAddress
    cases sameType
    rw [List.getElem?_eq_getElem bound]
    simp only [Option.map_some]
    congr 1
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using congrArg funcinst.TYPE found
  | sub address type actual prior sub _ _ _ ih =>
    cases sameType
    cases sub
    casesm* Functype_sub _ _
    exact ih sameAddress rfl
  | global => cases sameAddress
  | mem => cases sameAddress
  | table => cases sameAddress

def instructionCallAddress : admininstr → Option funcaddr
  | .CALL_ADDR address => some address
  | _ => none

theorem call_instruction_type {s : store} {context : _root_.context} {instruction : admininstr} {address : funcaddr}
    {input output params results : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (call : instructionCallAddress instruction = some address)
    (signature : s.FUNCS[address]?.map funcinst.TYPE = some (.mk_functype (.mk_list params) (.mk_list results))) :
    input=params ∧ output=results := by
  cases typed
  case plain =>
    rename_i instruction _ _ _ _
    cases instruction <;> simp [admininstr_instr,instructionCallAddress] at call
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref,instructionCallAddress] at call
  case call_addr =>
    rename_i called _ _ _ _ _
    have external : Externaddr_ok s (.FUNC called) (.FUNC (.mk_functype (.mk_list input) (.mk_list output))) := by assumption
    simp only [instructionCallAddress,Option.some.injEq] at call
    subst called
    have actual := external_function_signature external address _ rfl rfl
    rw [signature] at actual
    simpa only [Option.some.injEq,functype.mk_functype.injEq,list.mk_list.injEq] using actual.symm
  all_goals simp [instructionCallAddress] at call

theorem call_expression_results {s : store} {context : _root_.context} {address : funcaddr}
    {args : List val} {params results output : List valtype}
    (typed : Expr_ok2 s context (vals args++[.CALL_ADDR address]) (.mk_list output))
    (arguments : ResultsTyped s params args)
    (signature : s.FUNCS[address]?.map funcinst.TYPE = some (.mk_functype (.mk_list params) (.mk_list results))) :
    Resulttype_sub (.mk_list results) (.mk_list output) := by
  cases typed
  have instructions : Instrs_ok2 s context (vals args++[.CALL_ADDR address])
      (.mk_functype (.mk_list []) (.mk_list output)) := by assumption
  obtain ⟨types,values,called⟩ := closed_value_prefix_typing instructions
  have same := resultsTyped_types_unique values arguments
  subst types
  obtain ⟨base,input,produced,primitive,inputSub,outputSub⟩ := instruction_typing_effect called (.CALL_ADDR address) rfl
  obtain ⟨rfl,rfl⟩ := call_instruction_type primitive rfl signature
  have count := (resulttype_sub_iff.mp inputSub).length_eq
  have empty : base=[] := by
    have zero : base.length=0 := by simp only [List.length_append] at count; omega
    simpa using zero
  subst base
  exact outputSub

theorem direct_host_return_config_preserved {s t : store} {frame : _root_.frame} {address : funcaddr}
    {identity : Nat} {args returned : List val} {params results output : List valtype}
    (typed : Config_ok ⟨⟨s,frame⟩,vals args++[.CALL_ADDR address]⟩ (.mk_list output))
    (host : HostFunction s address identity params results)
    (arguments : ResultsTyped s params args) (extension : Extend_store s t)
    (storeTyped : Store_ok t) (values : ResultsTyped t results returned) :
    Config_ok ⟨⟨t,frame⟩,vals returned⟩ (.mk_list output) := by
  obtain ⟨module,found⟩ := host
  have signature : s.FUNCS[address]?.map funcinst.TYPE = some (.mk_functype (.mk_list params) (.mk_list results)) := by
    simp only [found,Option.map_some]
  cases typed with
  | mk_Config_ok _ _ _ _ context state expression _ _ _ =>
    exact host_return_config_ok state extension storeTyped
      (resultsTyped_subtype values (call_expression_results expression arguments signature))

theorem direct_host_trap_config_preserved {s t : store} {frame : _root_.frame}
    {body : List admininstr} {output : List valtype}
    (typed : Config_ok ⟨⟨s,frame⟩,body⟩ (.mk_list output))
    (extension : Extend_store s t) (storeTyped : Store_ok t) :
    Config_ok ⟨⟨t,frame⟩,[.TRAP]⟩ (.mk_list output) := by
  cases typed with
  | mk_Config_ok _ _ _ _ context state _ _ _ _ =>
    exact host_trap_config_ok state extension storeTyped output

theorem resulttype_sub_cancel_suffix {left right tail : List valtype}
    (sub : Resulttype_sub (.mk_list (left++tail)) (.mk_list (right++tail))) :
    Resulttype_sub (.mk_list left) (.mk_list right) := by
  have relation := resulttype_sub_iff.mp sub
  have count : left.length=right.length := by
    have same := relation.length_eq
    simp only [List.length_append] at same
    omega
  have selected := List.forall₂_take left.length relation
  apply resulttype_sub_iff.mpr
  simp only [List.take_append,List.take_length,Nat.sub_self,List.take_zero,List.append_nil] at selected
  simpa only [count,List.take_length,Nat.sub_self,List.take_zero,List.append_nil] using selected

theorem direct_host_return_instructions_preserved {s t : store} {context : _root_.context} {address : funcaddr}
    {args returned : List val} {params results input output : List valtype}
    (typed : Instrs_ok2 s context (vals args++[.CALL_ADDR address]) (.mk_functype (.mk_list input) (.mk_list output)))
    (signature : s.FUNCS[address]?.map funcinst.TYPE = some (.mk_functype (.mk_list params) (.mk_list results)))
    (arguments : ResultsTyped s params args) (extension : Extend_store s t)
    (values : ResultsTyped t results returned) :
    Instrs_ok2 t context (vals returned) (.mk_functype (.mk_list input) (.mk_list output)) := by
  obtain ⟨base,types,inputBase,argsTyped,called⟩ := value_prefix_typing typed
  have same := resultsTyped_types_unique argsTyped arguments
  subst types
  obtain ⟨callBase,callInput,callOutput,primitive,callSub,outputSub⟩ := instruction_typing_effect called (.CALL_ADDR address) rfl
  obtain ⟨rfl,rfl⟩ := call_instruction_type primitive rfl signature
  have bases := resulttype_sub_cancel_suffix callSub
  have inputSub := resulttype_sub_trans inputBase bases
  have contextWf := (instrs_ok2_wf typed).2.1
  have returnedTyped := instrs_frame (values_instrs_ok (extend_store_wf extension).2 contextWf values) callBase
  simp only [List.append_nil] at returnedTyped
  exact instrs_subtype returnedTyped inputSub outputSub

end Exec.Spec
