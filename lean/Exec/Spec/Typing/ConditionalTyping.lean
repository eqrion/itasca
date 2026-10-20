import Exec.Spec.Typing.ValueOperationTyping

/-! Both conditional outcomes and every listed/default branch-table target
preserve semantic stack typing. -/

namespace Exec.Spec
open SpecExt

theorem if_typing_preserved (s : store) (condition : num_) (bt : blocktype)
    (first second : List instr) (chooseFirst : Bool) :
    TypedReplacement s s [.CONST .I32 condition,.IFELSE bt first second]
      [.BLOCK bt (if chooseFirst then first else second)] := by
  change TypedReplacement s s [admininstr_val (.CONST .I32 condition),.IFELSE bt first second]
    [.BLOCK bt (if chooseFirst then first else second)]
  apply consume_value_typing_preserved
  intro context params results typed
  generalize same : admininstr.IFELSE bt first second = instruction at typed
  have storeWf : wf_store s := by cases typed <;> assumption
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    have sourceWf : wf_instr source := by assumption
    cases source <;> simp [admininstr_instr] at same
    rcases same with ⟨sameBt,sameFirst,sameSecond⟩
    cases sameBt
    cases sameFirst
    cases sameSecond
    have firstWf : wf_instr (.BLOCK bt first) := by
      cases sourceWf
      constructor <;> assumption
    have secondWf : wf_instr (.BLOCK bt second) := by
      cases sourceWf
      constructor <;> assumption
    cases primitive
    refine ⟨_,.I32,rfl,?_⟩
    apply Instrs_ok2.instr
    · apply Instr_ok2.plain s context (.BLOCK bt (if chooseFirst then first else second))
      · cases chooseFirst <;> simp only [Bool.false_eq_true,if_false,if_true]
        all_goals apply Instr_ok.block <;> assumption
      · exact storeWf
      · exact contextWf
      · cases chooseFirst <;> simp only [Bool.false_eq_true,if_false,if_true] <;> assumption
    · exact storeWf
    · exact contextWf
    · apply wf_admininstr_instr (i := .BLOCK bt (if chooseFirst then first else second))
      cases chooseFirst <;> simp only [Bool.false_eq_true,if_false,if_true] <;> assumption
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem br_if_typing_preserved (s : store) (condition : num_) (index : labelidx) (taken : Bool) :
    TypedReplacement s s [.CONST .I32 condition,.BR_IF index] (if taken then [.BR index] else []) := by
  change TypedReplacement s s [admininstr_val (.CONST .I32 condition),.BR_IF index] _
  apply consume_value_typing_preserved
  intro context params results typed
  generalize same : admininstr.BR_IF index = instruction at typed
  have storeWf : wf_store s := by cases typed <;> assumption
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    have sourceWf : wf_instr source := by assumption
    cases source <;> simp [admininstr_instr] at same
    cases same
    have branchWf : wf_instr (.BR index) := by
      cases sourceWf
      constructor
      assumption
    cases primitive
    refine ⟨_,.I32,rfl,?_⟩
    cases taken with
    | false => exact instrs_identity storeWf contextWf _
    | true =>
      simp only [if_true]
      apply Instrs_ok2.instr
      · apply Instr_ok2.plain s context (.BR index)
        · apply Instr_ok.br (t_1_lst := []) <;> assumption
        · exact storeWf
        · exact contextWf
        · exact branchWf
      · exact storeWf
      · exact contextWf
      · exact wf_admininstr_instr branchWf
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem br_table_typing_preserved (s : store) (condition : num_) (labels : List labelidx)
    (fallback target : labelidx) (selected : target ∈ labels ∨ target=fallback) :
    TypedReplacement s s [.CONST .I32 condition,.BR_TABLE labels fallback] [.BR target] := by
  change TypedReplacement s s [admininstr_val (.CONST .I32 condition),.BR_TABLE labels fallback] [.BR target]
  apply consume_value_typing_preserved
  intro context params results typed
  generalize same : admininstr.BR_TABLE labels fallback = instruction at typed
  have storeWf : wf_store s := by cases typed <;> assumption
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    have sourceWf : wf_instr source := by assumption
    cases source <;> simp [admininstr_instr] at same
    rcases same with ⟨sameLabels,sameFallback⟩
    cases sameLabels
    cases sameFallback
    have branchWf : wf_instr (.BR target) := by
      apply wf_instr.instr_case_7
      cases sourceWf
      rcases selected with member | rfl
      · have all : Forall (wf_uN 32) labels := by assumption
        exact all target member
      · assumption
    cases primitive
    rename_i discarded operands _ _ _ _ _ _
    have bounds : Forall (fun l => proj_uN_0 l < context.LABELS.length) labels := by assumption
    have subtypes : Forall (fun l => Resulttype_sub (.mk_list operands) context.LABELS[proj_uN_0 l]!) labels := by assumption
    have fallbackBound : proj_uN_0 fallback < context.LABELS.length := by assumption
    have fallbackSub : Resulttype_sub (.mk_list operands) context.LABELS[proj_uN_0 fallback]! := by assumption
    have targetBound : proj_uN_0 target < context.LABELS.length := by
      rcases selected with member | rfl
      · exact bounds target member
      · exact fallbackBound
    have targetSub : Resulttype_sub (.mk_list operands) context.LABELS[proj_uN_0 target]! := by
      rcases selected with member | rfl
      · exact subtypes target member
      · exact fallbackSub
    refine ⟨discarded++operands,.I32,(List.append_assoc _ _ _).symm,?_⟩
    cases found : context.LABELS[proj_uN_0 target]! with
    | mk_list branchTypes =>
      rw [found] at targetSub
      have branch : Instr_ok context (.BR target)
          (.mk_functype (.mk_list (discarded++branchTypes)) (.mk_list results)) :=
        .br _ _ _ _ _ targetBound (by simp only [found,proj_list_0]) contextWf branchWf
      have branchTyped := Instrs_ok2.instr _ _ _ _ _
        (.plain _ _ _ _ _ branch storeWf contextWf branchWf) storeWf contextWf (wf_admininstr_instr branchWf)
      exact instrs_subtype branchTyped (resulttype_sub_append (resulttype_sub_refl discarded) targetSub)
        (resulttype_sub_refl results)
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

end Exec.Spec
