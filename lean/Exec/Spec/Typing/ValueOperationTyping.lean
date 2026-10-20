import Exec.Spec.Typing.FixedInstructionTyping

/-! Typed effects of value-consuming operations, including drop/select, null
tests, local tee, and a stack-polymorphic consumed-value adapter. -/

namespace Exec.Spec
open SpecExt

theorem resulttype_sub_suffix {left right xs ys : List valtype}
    (sub : Resulttype_sub (.mk_list (left++xs)) (.mk_list (right++ys)))
    (prefixCount : left.length=right.length) : Resulttype_sub (.mk_list xs) (.mk_list ys) := by
  have selected := List.forall₂_drop left.length (resulttype_sub_iff.mp sub)
  apply resulttype_sub_iff.mpr
  simp only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at selected
  simpa only [prefixCount,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] using selected

theorem value_operation_preserved {s : store} {args : List val} {op : admininstr} {after : List admininstr}
    (operation : ∀ (context : _root_.context) (params results : List valtype),
      Instr_ok2 s context op (.mk_functype (.mk_list params) (.mk_list results)) →
      params.length=args.length ∧ (ResultsTyped s params args →
        Instrs_ok2 s context after (.mk_functype (.mk_list []) (.mk_list results)))) :
    TypedReplacement s s (vals args++[op]) after := by
  intro context input output typed
  obtain ⟨base,types,inputBase,argsTyped,called⟩ := value_prefix_typing typed
  obtain ⟨callBase,params,results,primitive,callSub,outputSub⟩ := instruction_typing_effect called op rfl
  obtain ⟨arity,effect⟩ := operation context params results primitive
  have count : types.length=params.length := by have same := argsTyped.length_eq; omega
  have baseSub := resulttype_sub_prefix callSub count
  have baseCount := (resulttype_sub_iff.mp baseSub).length_eq
  have argsSub := resulttype_sub_suffix callSub baseCount
  have afterTyped := effect (resultsTyped_subtype argsTyped argsSub)
  have framed := instrs_frame afterTyped callBase
  simp only [List.append_nil] at framed
  exact instrs_subtype framed (resulttype_sub_trans inputBase baseSub) outputSub

theorem drop_typing_preserved (s : store) (value : val) :
    TypedReplacement s s [admininstr_val value,.DROP] [] := by
  change TypedReplacement s s (vals [value]++[.DROP]) []
  apply value_operation_preserved
  intro context params results typed
  generalize same : admininstr.DROP = instruction at typed
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases source <;> simp [admininstr_instr] at same
    cases primitive
    refine ⟨rfl,?_⟩
    intro _
    apply instrs_identity
    · assumption
    · assumption
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem select_typing_preserved (s : store) (first second : val) (condition : num_)
    (annotation : Option (List valtype)) (chooseFirst : Bool) :
    TypedReplacement s s [admininstr_val first,admininstr_val second,.CONST .I32 condition,.SELECT annotation]
      [admininstr_val (if chooseFirst then first else second)] := by
  change TypedReplacement s s
    (vals [first,second,.CONST .I32 condition]++[.SELECT annotation])
    (vals [if chooseFirst then first else second])
  apply value_operation_preserved
  intro context params results typed
  generalize same : admininstr.SELECT annotation = instruction at typed
  have storeWf : wf_store s := by cases typed <;> assumption
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases source <;> simp [admininstr_instr] at same
    cases same
    cases primitive
    all_goals refine ⟨rfl,?_⟩
    all_goals intro arguments
    all_goals cases arguments with
    | cons firstTyped rest =>
      cases rest with
      | cons secondTyped rest =>
        apply values_instrs_ok storeWf contextWf
        apply List.Forall₂.cons
        · cases chooseFirst <;> simp only [Bool.false_eq_true,if_false,if_true] <;> assumption
        · exact .nil
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem null_test_typing_preserved (s : store) (reference : ref) (result : num_)
    (resultWf : wf_admininstr (.CONST .I32 result)) :
    TypedReplacement s s [admininstr_ref reference,.REF_IS_NULL] [.CONST .I32 result] := by
  have representation : admininstr_val (val_ref reference)=admininstr_ref reference := by cases reference <;> rfl
  rw [← representation]
  change TypedReplacement s s (vals [val_ref reference]++[.REF_IS_NULL]) (vals [.CONST .I32 result])
  apply value_operation_preserved
  intro context params results typed
  generalize same : admininstr.REF_IS_NULL = instruction at typed
  have storeWf : wf_store s := by cases typed <;> assumption
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases source <;> simp [admininstr_instr] at same
    cases primitive
    refine ⟨rfl,?_⟩
    intro _
    exact values_instrs_ok storeWf contextWf (.cons (.numtype _ _ _ storeWf (val_wf_of_admin resultWf)) .nil)
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem local_tee_typing_preserved (s : store) (value : val) (index : idx) :
    TypedReplacement s s [admininstr_val value,.LOCAL_TEE index]
      [admininstr_val value,admininstr_val value,.LOCAL_SET index] := by
  change TypedReplacement s s (vals [value]++[.LOCAL_TEE index])
    (vals [value,value]++[.LOCAL_SET index])
  apply value_operation_preserved
  intro context params results typed
  generalize same : admininstr.LOCAL_TEE index = instruction at typed
  have storeWf : wf_store s := by cases typed <;> assumption
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    have sourceWf : wf_instr source := by assumption
    cases source <;> simp [admininstr_instr] at same
    cases same
    have setWf : wf_instr (.LOCAL_SET index) := by
      cases sourceWf
      constructor
      assumption
    cases primitive
    rename_i type _ _ _ _
    refine ⟨rfl,?_⟩
    intro arguments
    cases arguments with
    | cons valueTyped rest =>
      have copied := values_instrs_ok storeWf contextWf (.cons valueTyped (.cons valueTyped .nil))
      have setting : Instr_ok context (.LOCAL_SET index) (.mk_functype (.mk_list [type]) (.mk_list [])) := by
        apply Instr_ok.local_set <;> assumption
      have setAdmin := Instr_ok2.plain s context (.LOCAL_SET index) [type] [] setting storeWf contextWf setWf
      have setTyped := Instrs_ok2.instr _ _ _ _ _ setAdmin storeWf contextWf (wf_admininstr_instr setWf)
      exact instrs_sequence copied (instrs_frame setTyped [type])
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

def BasicPureInstruction (instruction : admininstr) : Prop :=
  fixedInstructionSignature instruction ≠ none ∨
    match instruction with
    | .DROP | .SELECT _ | .REF_IS_NULL | .LOCAL_TEE _ => True
    | _ => False

def BasicPureRedex (code : List admininstr) : Prop :=
  ∃ instruction, code.getLast?=some instruction ∧ BasicPureInstruction instruction

set_option maxHeartbeats 2400000 in
theorem basic_pure_step_preserves {s : store} {before after : List admininstr}
    (storeWf : wf_store s) (source : Step_pure before after) (scope : BasicPureRedex before) :
    TypedReplacement s s before after := by
  have original := source
  cases source
  all_goals try exact trap_typing_replacement _ _
  all_goals try {
    apply fixed_pure_step_preserves storeWf original
    simp [fixedInstructionSignature] }
  all_goals try { simp [BasicPureRedex,BasicPureInstruction,fixedInstructionSignature] at scope }
  case drop => exact drop_typing_preserved _ _
  case select_true => simpa using select_typing_preserved s _ _ _ _ true
  case select_false => simpa using select_typing_preserved s _ _ _ _ false
  case ref_is_null_true => (apply null_test_typing_preserved; assumption)
  case ref_is_null_false => (apply null_test_typing_preserved; assumption)
  case local_tee => exact local_tee_typing_preserved _ _ _

theorem consume_value_typing_preserved {s : store} (argument : val) (op : admininstr) (after : List admininstr)
    (operation : ∀ (context : _root_.context) (params results : List valtype),
      Instr_ok2 s context op (.mk_functype (.mk_list params) (.mk_list results)) →
      ∃ operands type, params=operands++[type] ∧
        Instrs_ok2 s context after (.mk_functype (.mk_list operands) (.mk_list results))) :
    TypedReplacement s s [admininstr_val argument,op] after := by
  intro context input output typed
  change Instrs_ok2 s context (vals [argument]++[op]) _ at typed
  obtain ⟨base,types,inputBase,argsTyped,called⟩ := value_prefix_typing typed
  cases argsTyped with
  | cons argumentTyped rest =>
    cases rest
    rename_i argumentType
    obtain ⟨callBase,params,results,primitive,callSub,outputSub⟩ := instruction_typing_effect called op rfl
    obtain ⟨operands,type,rfl,afterTyped⟩ := operation context params results primitive
    have sub : Resulttype_sub (.mk_list (base++[argumentType])) (.mk_list ((callBase++operands)++[type])) := by
      simpa only [List.append_assoc] using callSub
    have bases := resulttype_sub_prefix sub rfl
    exact instrs_subtype (instrs_frame afterTyped callBase) (resulttype_sub_trans inputBase bases) outputSub

end Exec.Spec
