import Exec.Spec.Typing.FramePayloadTyping
import Exec.Spec.Typing.SourceAdministrativeTyping

/-! Actual module type lookup agrees with block typing. Block and loop entry
preserve semantic stack typing, including multi-value parameters and results. -/

namespace Exec.Spec
open SpecExt

theorem moduleinst_types_agree {s : store} {module : moduleinst} {context : _root_.context}
    (typed : Moduleinst_ok s module context) : module.TYPES=context.TYPES := by
  cases typed
  rfl

theorem FrameEnvironment.blocktype {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) {block : blocktype} {type : functype}
    (typed : Blocktype_ok context block type) : fun_blocktype ⟨s,frame⟩ block=type := by
  have types := moduleinst_types_agree environment.moduleTyped
  change frame.MODULE.TYPES=context.TYPES at types
  cases typed with
  | valtype type _ _ => cases type <;> rfl
  | typeidx index input output _ found _ _ =>
    simpa only [fun_blocktype,fun_type,types] using found

theorem block_read_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (values : List val) (block : blocktype) (body : List instr)
    (arity : Nat) (params results : List valtype)
    (expanded : fun_blocktype ⟨s,frame⟩ block=.mk_functype (.mk_list params) (.mk_list results))
    (count : values.length=params.length) (resultCount : arity=results.length)
    {input output : List valtype}
    (typed : Instrs_ok2 s context (vals values++[.BLOCK block body]) (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [.LABEL_ arity [] (vals values++body.map admininstr_instr)]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  apply value_operation_at_context typed
  intro primitiveInput primitiveOutput primitive
  generalize same : admininstr.BLOCK block body=instruction at primitive
  have storeWf : wf_store s := by cases primitive <;> assumption
  have contextWf : wf_context context := by cases primitive <;> assumption
  cases primitive
  case plain =>
    rename_i source _ _ _ sourceTyped
    cases source <;> simp [admininstr_instr] at same
    rcases same with ⟨sameBlock,sameBody⟩
    cases sameBlock
    cases sameBody
    cases sourceTyped
    have blockTyped : Blocktype_ok context block (.mk_functype (.mk_list primitiveInput) (.mk_list primitiveOutput)) := by assumption
    have typeEq := (environment.blocktype blockTyped).symm.trans expanded
    have equalities : primitiveInput=params ∧ primitiveOutput=results := by
      simpa only [functype.mk_functype.injEq,list.mk_list.injEq] using typeEq
    rcases equalities with ⟨rfl,rfl⟩
    refine ⟨count.symm,?_⟩
    intro arguments
    let labelContext : _root_.context := {(default : _root_.context) with LABELS := [.mk_list primitiveOutput]} ++ context
    have bodyTyped : Instrs_ok labelContext body (.mk_functype (.mk_list primitiveInput) (.mk_list primitiveOutput)) := by assumption
    have bodyAdmin := source_instrs_administrative storeWf bodyTyped
    have innerContextWf := (instrs_ok2_wf bodyAdmin).2.1
    have inner := instrs_sequence (values_instrs_ok storeWf innerContextWf arguments) bodyAdmin
    have innerWf := (instrs_ok2_wf inner).2.2
    have labelWf : wf_admininstr (.LABEL_ arity [] (vals values++body.map admininstr_instr)) :=
      .admininstr_case_71 _ _ _ (by simp [Forall]) innerWf
    apply Instrs_ok2.instr
    · apply Instr_ok2.label
      · exact instrs_identity storeWf contextWf primitiveOutput
      · exact inner
      · exact storeWf
      · exact contextWf
      · exact labelWf
      · assumption
      · exact resultCount
    · exact storeWf
    · exact contextWf
    · exact labelWf
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem loop_read_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (values : List val) (block : blocktype) (body : List instr)
    (arity : Nat) (params results : List valtype)
    (expanded : fun_blocktype ⟨s,frame⟩ block=.mk_functype (.mk_list params) (.mk_list results))
    (count : values.length=params.length) (branchCount : arity=params.length)
    {input output : List valtype}
    (typed : Instrs_ok2 s context (vals values++[.LOOP block body]) (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [.LABEL_ arity [.LOOP block body] (vals values++body.map admininstr_instr)]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  apply value_operation_at_context typed
  intro primitiveInput primitiveOutput primitive
  generalize same : admininstr.LOOP block body=instruction at primitive
  have storeWf : wf_store s := by cases primitive <;> assumption
  have contextWf : wf_context context := by cases primitive <;> assumption
  cases primitive
  case plain =>
    rename_i source _ _ _ sourceTyped
    cases source <;> simp [admininstr_instr] at same
    rcases same with ⟨sameBlock,sameBody⟩
    cases sameBlock
    cases sameBody
    have originalLoop := sourceTyped
    cases sourceTyped
    have blockTyped : Blocktype_ok context block (.mk_functype (.mk_list primitiveInput) (.mk_list primitiveOutput)) := by assumption
    have typeEq := (environment.blocktype blockTyped).symm.trans expanded
    have equalities : primitiveInput=params ∧ primitiveOutput=results := by
      simpa only [functype.mk_functype.injEq,list.mk_list.injEq] using typeEq
    rcases equalities with ⟨rfl,rfl⟩
    refine ⟨count.symm,?_⟩
    intro arguments
    let labelContext : _root_.context := {(default : _root_.context) with LABELS := [.mk_list primitiveInput]} ++ context
    have bodyTyped : Instrs_ok labelContext body (.mk_functype (.mk_list primitiveInput) (.mk_list primitiveOutput)) := by assumption
    have bodyAdmin := source_instrs_administrative storeWf bodyTyped
    have innerContextWf := (instrs_ok2_wf bodyAdmin).2.1
    have inner := instrs_sequence (values_instrs_ok storeWf innerContextWf arguments) bodyAdmin
    have innerWf := (instrs_ok2_wf inner).2.2
    have loopWf : wf_instr (.LOOP block body) := by assumption
    have continuation := Instrs_ok2.instr s context (admininstr_instr (.LOOP block body)) primitiveInput primitiveOutput
      (.plain _ _ _ _ _ originalLoop storeWf contextWf loopWf) storeWf contextWf (wf_admininstr_instr loopWf)
    have labelWf : wf_admininstr (.LABEL_ arity [.LOOP block body] (vals values++body.map admininstr_instr)) :=
      .admininstr_case_71 _ _ _ (by simpa [Forall] using loopWf) innerWf
    apply Instrs_ok2.instr
    · apply Instr_ok2.label
      · exact continuation
      · exact inner
      · exact storeWf
      · exact contextWf
      · exact labelWf
      · assumption
      · exact branchCount
    · exact storeWf
    · exact contextWf
    · exact labelWf
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

end Exec.Spec
