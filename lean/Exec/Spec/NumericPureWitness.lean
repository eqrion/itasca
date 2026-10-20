import Exec.Spec.Choices.ForcedNumericRequest
import Exec.Spec.Choices.NumericChoiceCoverage
import Exec.Spec.Choices.TerminalSyntax
namespace Exec.Spec

private theorem firstOperation_ref (value : ref) (tail : List admininstr) :
    firstOperation (admininstr_ref value::tail)=firstOperation tail := by cases value <;> rfl

private theorem permitted_some {results : List num_} {value : num_} (member : value∈results) :
    NumericReplyAllowed results (some value) := by
  constructor
  · constructor
    · intro impossible; cases impossible
    · intro empty; rw [empty] at member; simp at member
  · intro other same; cases same; exact member

set_option maxHeartbeats 2000000 in
theorem numeric_pure_reply_witness {before after : List admininstr} (source : Step_pure before after)
    (request : NumericRequest) (reply : Option num_) (input : before=request.instructions)
    (output : after=numericOutput request.type reply) :
    ∃ results, request.Allowed results ∧ NumericReplyAllowed results reply := by
  have opcode := congrArg firstOperation input
  cases request
  all_goals cases reply
  all_goals cases source
  all_goals try { simp [NumericRequest.instructions,firstOperation,firstOperation_value,firstOperation_map,
    firstOperation_ref,admininstr.ctorIdx] at opcode }
  all_goals simp only [NumericRequest.instructions,NumericRequest.type,numericOutput] at input output
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try (with_reducible contradiction)
  all_goals casesm* Option (List num_)
  all_goals try (with_reducible contradiction)
  all_goals try simp only [Option.get!_some,List.contains_iff_mem] at *
  all_goals try injections
  all_goals subst_vars
  all_goals first
    | exact ⟨_,NumericRequest.Allowed.unary (by assumption) (by assumption) (by assumption)
        (numeric_unop_results_wf (by assumption)),permitted_some (by assumption)⟩
    | exact ⟨_,NumericRequest.Allowed.binary (by assumption) (by assumption) (by assumption) (by assumption)
        (numeric_binop_results_wf (by assumption)),permitted_some (by assumption)⟩
    | exact ⟨_,NumericRequest.Allowed.convert (by assumption) (by assumption) (by assumption)
        (numeric_cvtop_results_wf (by assumption)),permitted_some (by assumption)⟩
    | exact ⟨[],NumericRequest.Allowed.unary (by assumption) (by assumption) (by assumption)
        (numeric_unop_results_wf (by assumption)),by simp [NumericReplyAllowed]⟩
    | exact ⟨[],NumericRequest.Allowed.binary (by assumption) (by assumption) (by assumption) (by assumption)
        (numeric_binop_results_wf (by assumption)),by simp [NumericReplyAllowed]⟩
    | exact ⟨[],NumericRequest.Allowed.convert (by assumption) (by assumption) (by assumption)
        (numeric_cvtop_results_wf (by assumption)),by simp [NumericReplyAllowed]⟩

/-- A deterministic request consumes the same reply under every admissible
policy. The reply is recovered from the generated source rule, not postulated. -/
theorem chosen_numeric_of_forced_pure {choices : NumericChoices} (admissible : choices.Admissible)
    (occurrence : Nat) {before after : List admininstr} (source : Step_pure before after)
    (request : NumericRequest) (reply : Option num_) (input : before=request.instructions)
    (output : after=numericOutput request.type reply) (forced : request.Forced) :
    ChosenNumeric choices occurrence request reply := by
  obtain ⟨results,allowed,permitted⟩ := numeric_pure_reply_witness source request reply input output
  exact chosen_numeric_of_forced_reply admissible occurrence allowed (forced results allowed) permitted
end Exec.Spec
