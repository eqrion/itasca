import Exec.Spec.Typing.FramePayloadTyping

/-! Recover typed operands, exact primitive effects, and the retained stack
prefix for state-changing source instructions. -/

namespace Exec.Spec
open SpecExt

def writeInstructionSignature : admininstr → Option (Nat × List valtype)
  | .LOCAL_SET _ | .GLOBAL_SET _ => some (1,[])
  | .TABLE_SET _ | .STORE _ _ _ | .VSTORE _ _ | .VSTORE_LANE _ _ _ _ => some (2,[])
  | .ELEM_DROP _ | .DATA_DROP _ => some (0,[])
  | .MEMORY_GROW => some (1,[.I32])
  | .TABLE_GROW _ => some (2,[.I32])
  | _ => none

set_option maxHeartbeats 1600000 in
theorem write_instruction_effect {s : store} {context : _root_.context} {instruction : admininstr}
    {input output results : List valtype} {count : Nat}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (signature : writeInstructionSignature instruction=some (count,results)) : input.length=count ∧ output=results := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases primitive <;> simp_all [writeInstructionSignature,admininstr_instr]
    all_goals (rcases signature with ⟨rfl,rfl⟩; rfl)
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref,writeInstructionSignature] at signature
  all_goals simp [writeInstructionSignature] at signature

theorem write_operands {s : store} {context : _root_.context} {args : List val} {op : admininstr}
    {input output : List valtype}
    (typed : Instrs_ok2 s context (vals args++[op]) (.mk_functype (.mk_list input) (.mk_list output)))
    (arity : ∀ params results, Instr_ok2 s context op (.mk_functype (.mk_list params) (.mk_list results)) →
      params.length=args.length) :
    ∃ base params results, Instr_ok2 s context op (.mk_functype (.mk_list params) (.mk_list results)) ∧
      ResultsTyped s params args ∧ Resulttype_sub (.mk_list input) (.mk_list base) ∧
      Resulttype_sub (.mk_list (base++results)) (.mk_list output) := by
  obtain ⟨base,types,inputBase,argsTyped,called⟩ := value_prefix_typing typed
  obtain ⟨callBase,params,results,primitive,callSub,outputSub⟩ := instruction_typing_effect called op rfl
  have count : types.length=params.length := by
    have before := argsTyped.length_eq
    have after := arity params results primitive
    omega
  have baseSub := resulttype_sub_prefix callSub count
  have baseCount := (resulttype_sub_iff.mp baseSub).length_eq
  have argsSub := resulttype_sub_suffix callSub baseCount
  exact ⟨callBase,params,results,primitive,resultsTyped_subtype argsTyped argsSub,
    resulttype_sub_trans inputBase baseSub,outputSub⟩

theorem realize_write_result {t : store} {context : _root_.context}
    {after : List admininstr} {base results input output : List valtype}
    (inputSub : Resulttype_sub (.mk_list input) (.mk_list base))
    (outputSub : Resulttype_sub (.mk_list (base++results)) (.mk_list output))
    (result : Instrs_ok2 t context after (.mk_functype (.mk_list []) (.mk_list results))) :
    Instrs_ok2 t context after (.mk_functype (.mk_list input) (.mk_list output)) := by
  have framed := instrs_frame result base
  simp only [List.append_nil] at framed
  exact instrs_subtype framed inputSub outputSub

theorem write_operands_effect {s : store} {context : _root_.context} {args : List val} {op : admininstr}
    {input output results : List valtype}
    (typed : Instrs_ok2 s context (vals args++[op]) (.mk_functype (.mk_list input) (.mk_list output)))
    (signature : writeInstructionSignature op=some (args.length,results)) :
    ∃ base params, Instr_ok2 s context op (.mk_functype (.mk_list params) (.mk_list results)) ∧
      ResultsTyped s params args ∧ Resulttype_sub (.mk_list input) (.mk_list base) ∧
      Resulttype_sub (.mk_list (base++results)) (.mk_list output) := by
  obtain ⟨base,params,actual,primitive,arguments,inputSub,outputSub⟩ := write_operands typed
    (fun _ _ primitive => (write_instruction_effect primitive signature).1)
  have same := (write_instruction_effect primitive signature).2
  subst actual
  exact ⟨base,params,primitive,arguments,inputSub,outputSub⟩

end Exec.Spec
