import Exec.Spec.Choices.Steps
import Exec.Spec.Choices.Selection
import Exec.Spec.Choices.NumericChoiceCoverage

/-! Every generated pure reduction has an admissible choice-indexed witness.
This is source coverage; it does not identify a concrete interpreter policy. -/

namespace Exec.Spec

private noncomputable def numericPolicies (policy : NumericChoices) : SourceChoices :=
  {defaultSourceChoices with numeric := policy}

private theorem numericPolicies_admissible {policy : NumericChoices} (allowed : policy.Admissible) :
    (numericPolicies policy).Admissible :=
  ⟨defaultSourceChoices_admissible.host,allowed,defaultSourceChoices_admissible.vector,
    defaultSourceChoices_admissible.memory,defaultSourceChoices_admissible.table⟩

private noncomputable def vectorPolicies (policy : VectorChoices) : SourceChoices :=
  {defaultSourceChoices with vector := policy}

private theorem vectorPolicies_admissible {policy : VectorChoices} (allowed : policy.Admissible) :
    (vectorPolicies policy).Admissible :=
  ⟨defaultSourceChoices_admissible.host,defaultSourceChoices_admissible.numeric,allowed,
    defaultSourceChoices_admissible.memory,defaultSourceChoices_admissible.table⟩

private theorem some_reply_allowed {results : List num_} {value : num_} (member : value ∈ results) :
    NumericReplyAllowed results (some value) := by
  constructor
  · constructor
    · intro impossible; cases impossible
    · intro empty; rw [empty] at member; simp at member
  · intro other same; cases same; exact member

private theorem none_reply_allowed : NumericReplyAllowed [] none := by constructor <;> simp

private theorem selectable_numeric_step (occurrence : Nat) {request : NumericRequest} {results : List num_}
    {reply : Option num_} (source : request.Allowed results) (permitted : NumericReplyAllowed results reply)
    (z : state) (inputWf : wf_config ⟨z,request.instructions⟩)
    (outputWf : wf_config ⟨z,numericOutput request.type reply⟩) :
    ∃ choices : SourceChoices, choices.Admissible ∧
      ChoiceStep choices occurrence ⟨z,request.instructions⟩ [] ⟨z,numericOutput request.type reply⟩ := by
  obtain ⟨policy,admissible,chosen⟩ := numeric_reply_selectable occurrence request results source reply permitted
  exact ⟨numericPolicies policy,numericPolicies_admissible admissible,.numeric chosen inputWf outputWf⟩

private theorem selectable_vector_step (occurrence : Nat) {request : VectorRequest} {reply : Option vec_}
    (permitted : VectorResultAllowed request reply) (z : state) (inputWf : wf_config ⟨z,request.instructions⟩)
    (outputWf : wf_config ⟨z,vectorOutput reply⟩) :
    ∃ choices : SourceChoices, choices.Admissible ∧
      ChoiceStep choices occurrence ⟨z,request.instructions⟩ [] ⟨z,vectorOutput reply⟩ := by
  obtain ⟨policy,admissible,chosen⟩ := vector_reply_selectable occurrence request reply permitted
  exact ⟨vectorPolicies policy,vectorPolicies_admissible admissible,.vector chosen inputWf outputWf⟩

set_option maxHeartbeats 1600000 in
theorem pure_step_choices {before after : List admininstr} (source : Step_pure before after)
    (occurrence : Nat) (z : state) (inputWf : wf_config ⟨z,before⟩) (outputWf : wf_config ⟨z,after⟩) :
    ∃ choices : SourceChoices, choices.Admissible ∧ ChoiceStep choices occurrence ⟨z,before⟩ [] ⟨z,after⟩ := by
  have original := source
  cases source
  case unop_val =>
    rename_i value results operator _ present member iw ow vw
    cases results with
    | none => contradiction
    | some results =>
      simp only [Option.get!_some,List.contains_iff_mem] at member
      have allowed := NumericRequest.Allowed.unary operator iw ow (numeric_unop_results_wf operator)
      exact selectable_numeric_step occurrence allowed (some_reply_allowed member) z inputWf outputWf
  case unop_trap =>
    rename_i results operator present empty iw ow tw
    cases results with
    | none => contradiction
    | some results =>
      simp only [Option.get!_some] at empty
      subst results
      have allowed := NumericRequest.Allowed.unary operator iw ow (numeric_unop_results_wf operator)
      exact selectable_numeric_step occurrence allowed none_reply_allowed z inputWf outputWf
  case binop_val =>
    rename_i value results operator _ present member lw rw ow vw
    cases results with
    | none => contradiction
    | some results =>
      simp only [Option.get!_some,List.contains_iff_mem] at member
      have allowed := NumericRequest.Allowed.binary operator lw rw ow (numeric_binop_results_wf operator)
      exact selectable_numeric_step occurrence allowed (some_reply_allowed member) z inputWf outputWf
  case binop_trap =>
    rename_i results operator present empty lw rw ow tw
    cases results with
    | none => contradiction
    | some results =>
      simp only [Option.get!_some] at empty
      subst results
      have allowed := NumericRequest.Allowed.binary operator lw rw ow (numeric_binop_results_wf operator)
      exact selectable_numeric_step occurrence allowed none_reply_allowed z inputWf outputWf
  case cvtop_val =>
    rename_i value results operator _ present member iw ow vw
    cases results with
    | none => contradiction
    | some results =>
      simp only [Option.get!_some,List.contains_iff_mem] at member
      have allowed := NumericRequest.Allowed.convert operator iw ow (numeric_cvtop_results_wf operator)
      exact selectable_numeric_step occurrence allowed (some_reply_allowed member) z inputWf outputWf
  case cvtop_trap =>
    rename_i results operator present empty iw ow tw
    cases results with
    | none => contradiction
    | some results =>
      simp only [Option.get!_some] at empty
      subst results
      have allowed := NumericRequest.Allowed.convert operator iw ow (numeric_cvtop_results_wf operator)
      exact selectable_numeric_step occurrence allowed none_reply_allowed z inputWf outputWf
  case vunop =>
    rename_i value results operator _ present member iw ow vw
    cases results with
    | none => contradiction
    | some results =>
      simp only [Option.get!_some,List.contains_iff_mem] at member
      exact selectable_vector_step occurrence (.unary operator member iw ow vw) z inputWf outputWf
  case vunop_trap =>
    rename_i results operator present empty iw ow tw
    cases results with
    | none => contradiction
    | some results =>
      simp only [Option.get!_some] at empty
      subst results
      exact selectable_vector_step occurrence (.unary_trap operator iw ow) z inputWf outputWf
  case vbinop_val =>
    rename_i value results operator _ present member lw rw ow vw
    cases results with
    | none => contradiction
    | some results =>
      simp only [Option.get!_some,List.contains_iff_mem] at member
      exact selectable_vector_step occurrence (.binary operator member lw rw ow vw) z inputWf outputWf
  case vbinop_trap =>
    rename_i results operator present empty lw rw ow tw
    cases results with
    | none => contradiction
    | some results =>
      simp only [Option.get!_some] at empty
      subst results
      exact selectable_vector_step occurrence (.binary_trap operator lw rw ow) z inputWf outputWf
  case vcvtop =>
    rename_i value results operator present selected iw ow vw
    cases results with
    | none => contradiction
    | some result =>
      simp only [Option.get!_some] at selected
      cases selected
      exact selectable_vector_step occurrence (.convert operator iw ow vw) z inputWf outputWf
  all_goals refine ⟨defaultSourceChoices,defaultSourceChoices_admissible,.ordinary_pure original ?_ inputWf outputWf⟩
  all_goals first | rfl | skip
  case trap_vals =>
    simpa only [SpecExt.vals,Map,List.append_assoc] using trap_redex_choice_free _ _
  all_goals casesm* val, ref <;> rfl

end Exec.Spec

