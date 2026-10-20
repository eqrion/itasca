import Exec.Spec.Choices.Control
import Exec.Spec.PureWf
import Exec.Spec.Typing.ValueConfigTyping
import Exec.Spec.Typing.EmptyFrameTyping

/-! Administrative trap cleanup permits different one-step successors under
fixed policies, even from a semantically typed configuration. Residual proper
trap contexts clean up in one further step. -/

namespace Exec.Spec
open SpecExt

/-- The administrative overlap occurs in a semantically typed configuration,
not only among malformed or merely well-formed instruction lists. -/
theorem trap_cleanup_input_typed (s : store) (typed : Store_ok s) :
    Config_ok ⟨⟨s,default⟩,[Segment.i32 0,.TRAP,.NOP]⟩ (.mk_list []) := by
  have storeWf : wf_store s := by cases typed; assumption
  let zero : val := .CONST .I32 (.mk_num__0 .I32 (.mk_uN 0))
  have i32Wf := Segment.i32_wf 0 (by decide)
  have zeroWf : wf_val zero := val_wf_of_admin i32Wf
  have valueTyped : Val_ok s zero .I32 := .numtype s .I32 _ storeWf zeroWf
  have valuesWf : Forall wf_admininstr (vals [zero]) := by
    simpa [Forall,vals,zero,Segment.i32,admininstr_val] using i32Wf
  have trapWf : wf_admininstr .TRAP := .admininstr_case_73
  have trapsWf : Forall wf_admininstr [.TRAP] := by simpa [Forall] using trapWf
  have nopWf : wf_admininstr .NOP := .admininstr_case_0
  have nopsWf : Forall wf_admininstr [.NOP] := by simpa [Forall] using nopWf
  have valuesTyped := values_instrs_ok storeWf empty_context_wf (List.Forall₂.cons valueTyped .nil)
  have trapTyped := Instrs_ok2.instr s default .TRAP [.I32] []
    (.trap s default [.I32] [] storeWf empty_context_wf trapWf) storeWf empty_context_wf trapWf
  have twoTyped := Instrs_ok2.seq s default (vals [zero]) [.TRAP] [] [] [.I32] valuesTyped trapTyped
    storeWf empty_context_wf valuesWf trapsWf
  have nopTyped := Instrs_ok2.instr s default .NOP [] []
    (.plain s default .NOP [] [] (.nop default empty_context_wf .instr_case_0)
      storeWf empty_context_wf .instr_case_0) storeWf empty_context_wf nopWf
  have twoWf := forall_append valuesWf trapsWf
  have allTyped := Instrs_ok2.seq s default ((vals [zero])++[.TRAP]) [.NOP] [] [] []
    twoTyped nopTyped storeWf empty_context_wf twoWf nopsWf
  have allWf := forall_append twoWf nopsWf
  exact .mk_Config_ok s default _ [] default (empty_state_ok s typed)
    (.mk_Expr_ok2 s default _ [] allTyped storeWf empty_context_wf allWf)
    empty_context_wf (wf_config_make storeWf empty_frame_wf allWf) (.state_case_0 _ _ storeWf empty_frame_wf)

/-- Fixed numeric/growth/host policies do not make administrative trap cleanup
one-step deterministic: a context may discard a smaller fragment first. -/
theorem trap_cleanup_alternatives (choices : SourceChoices) (occurrence : Nat)
    (s : store) (f : frame) (storeWf : wf_store s) (frameWf : wf_frame f) :
    ChoiceStep choices occurrence ⟨⟨s,f⟩,[Segment.i32 0,.TRAP,.NOP]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ ∧
    ChoiceStep choices occurrence ⟨⟨s,f⟩,[Segment.i32 0,.TRAP,.NOP]⟩ [] ⟨⟨s,f⟩,[Segment.i32 0,.TRAP]⟩ ∧
    (config.mk_config ⟨s,f⟩ [.TRAP]) ≠ ⟨⟨s,f⟩,[Segment.i32 0,.TRAP]⟩ := by
  let zero : val := .CONST .I32 (.mk_num__0 .I32 (.mk_uN 0))
  have i32Wf := Segment.i32_wf 0 (by decide)
  have zeroWf : wf_val zero := val_wf_of_admin i32Wf
  have trapWf : wf_admininstr .TRAP := .admininstr_case_73
  have nopWf : wf_admininstr .NOP := .admininstr_case_0
  have beforeWf : wf_config ⟨⟨s,f⟩,[Segment.i32 0,.TRAP,.NOP]⟩ :=
    wf_config_make storeWf frameWf (by simp [Forall,i32Wf,trapWf,nopWf])
  have innerWf : wf_config ⟨⟨s,f⟩,[.TRAP,.NOP]⟩ :=
    wf_config_make storeWf frameWf (by simp [Forall,trapWf,nopWf])
  have middleWf : wf_config ⟨⟨s,f⟩,[Segment.i32 0,.TRAP]⟩ :=
    wf_config_make storeWf frameWf (by simp [Forall,i32Wf,trapWf])
  have finalWf := wf_config_trap storeWf frameWf
  have direct := ChoiceStep.propagate_trap (choices := choices) (occurrence := occurrence)
    (z := .mk_state s f) (front := [zero]) (tail := [.NOP]) (Or.inl (by simp))
    (by simpa [Forall] using zeroWf) (by simpa [Forall] using nopWf) beforeWf finalWf
  have inner := ChoiceStep.propagate_trap (choices := choices) (occurrence := occurrence)
    (z := .mk_state s f) (front := []) (tail := [.NOP]) (Or.inr (by simp))
    (by simp) (by simpa [Forall] using nopWf) innerWf finalWf
  have contextual := ChoiceStep.instrs (front := [zero]) (after := []) inner (Or.inl (by simp)) beforeWf middleWf
  exact ⟨direct,contextual,by intro same; cases same⟩

/-- Every proper residual trap context reaches the same terminal trap in one
additional step, regardless of the selected source policies. -/
theorem residual_trap_cleanup (choices : SourceChoices) (occurrence : Nat)
    (s : store) (f : frame) (front : List val) (tail : List admininstr)
    (nonempty : front ≠ [] ∨ tail ≠ []) (storeWf : wf_store s) (frameWf : wf_frame f)
    (frontWf : Forall wf_val front) (tailWf : Forall wf_admininstr tail) :
    ChoiceSteps choices occurrence ⟨⟨s,f⟩,vals front++[.TRAP]++tail⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have final := wf_config_trap storeWf frameWf
  have input : wf_config ⟨⟨s,f⟩,vals front++[.TRAP]++tail⟩ :=
    wf_config_make storeWf frameWf (forall_append (forall_append (wf_vals frontWf)
      (by simpa [Forall] using wf_admininstr.admininstr_case_73)) tailWf)
  exact .cons (ChoiceStep.propagate_trap nonempty frontWf tailWf input final) (.refl _ final)

end Exec.Spec

