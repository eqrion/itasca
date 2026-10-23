import Exec.Spec.Wf

namespace Exec.Spec
open SpecExt

/-- A label evaluation context, preserving the inner state. -/
def labelContext (arity : Nat) (cont : List instr) : config → config
  | .mk_config z body => .mk_config z [.LABEL_ arity cont body]

/-- A frame evaluation context; the enclosing frame is not changed. -/
def frameContext (arity : Nat) (outer : frame) : config → config
  | .mk_config (.mk_state s inner) body =>
      .mk_config (.mk_state s outer) [.FRAME_ arity inner body]

/-- Values to the left and pending instructions to the right of the redex. -/
def instrContext (vs : List val) (after : List admininstr) : config → config
  | .mk_config z body => .mk_config z (vals vs ++ (body ++ after))

/-- Lift an execution through any context preserving steps and well-formedness. -/
theorem stepsH_map {wrap : config → config}
    (hw : ∀ c, wf_config c → wf_config (wrap c))
    (hs : ∀ c es c', StepH c es c' → StepH (wrap c) es (wrap c'))
    {c c' : config} {es : List HostEvent} (h : StepsH c es c') :
    StepsH (wrap c) es (wrap c') := by
  induction h with
  | refl h => exact .refl (hw _ h)
  | cons h _ ih => exact .cons (hs _ _ _ h) ih

theorem stepH_label {c c' : config} {es : List HostEvent}
    (h : StepH c es c') (arity : Nat) (cont : List instr) (hc : Forall wf_instr cont) :
    StepH (labelContext arity cont c) es (labelContext arity cont c') := by
  cases c with | mk_config z body =>
    cases c' with | mk_config z' body' =>
      obtain ⟨hw, hw'⟩ := stepH_wf h
      exact .ctxt_label h (wf_config_label arity hw hc) (wf_config_label arity hw' hc) hw hw'

theorem stepH_frame {c c' : config} {es : List HostEvent}
    (h : StepH c es c') (arity : Nat) (outer : frame) (hf : wf_frame outer) :
    StepH (frameContext arity outer c) es (frameContext arity outer c') := by
  cases c with | mk_config z body =>
    cases z
    cases c' with | mk_config z' body' =>
      cases z'
      obtain ⟨hw, hw'⟩ := stepH_wf h
      exact .ctxt_frame h (wf_config_frame arity hw hf) (wf_config_frame arity hw' hf) hw hw'

theorem stepH_instrs {c c' : config} {es : List HostEvent}
    (h : StepH c es c') (vs : List val) (after : List admininstr)
    (hv : Forall wf_val vs) (ha : Forall wf_admininstr after) :
    StepH (instrContext vs after c) es (instrContext vs after c') := by
  cases c with | mk_config z body =>
    cases c' with | mk_config z' body' =>
      by_cases hn : vs ≠ [] ∨ after ≠ []
      · obtain ⟨hw, hw'⟩ := stepH_wf h
        exact .ctxt_instrs h hn (wf_config_instrs hw hv ha) (wf_config_instrs hw' hv ha) hw hw'
      · have hv0 : vs = [] := Decidable.byContradiction (fun hne => hn (Or.inl hne))
        have ha0 : after = [] := Decidable.byContradiction (fun hne => hn (Or.inr hne))
        subst vs
        subst after
        simpa [instrContext, vals] using h

theorem stepsH_instrs {c c' : config} {es : List HostEvent}
    (h : StepsH c es c') (vs : List val) (after : List admininstr)
    (hv : Forall wf_val vs) (ha : Forall wf_admininstr after) :
    StepsH (instrContext vs after c) es (instrContext vs after c') := by
  apply stepsH_map (wrap := instrContext vs after) ?_ (fun _ _ _ h => stepH_instrs h vs after hv ha) h
  intro c hw
  cases c
  exact wf_config_instrs hw hv ha

end Exec.Spec
