import Exec.Spec.Choices.VectorChoices
import Exec.Spec.Choices.TerminalSyntax
namespace Exec.Spec
private theorem firstOperation_ref (value : ref) (tail : List admininstr) :
    firstOperation (admininstr_ref value::tail)=firstOperation tail := by cases value <;> rfl

set_option maxHeartbeats 2000000 in
theorem vector_pure_reply_witness {before after : List admininstr} (source : Step_pure before after)
    (request : VectorRequest) (reply : Option vec_) (input : before=request.instructions)
    (output : after=vectorOutput reply) : VectorResultAllowed request reply := by
  have opcode := congrArg firstOperation input
  cases request
  all_goals cases reply
  all_goals cases source
  all_goals try { simp [VectorRequest.instructions,firstOperation,firstOperation_value,firstOperation_map,
    firstOperation_ref,admininstr.ctorIdx] at opcode }
  all_goals simp only [VectorRequest.instructions,vectorOutput] at input output
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try (with_reducible contradiction)
  all_goals try casesm* Option (List vec_)
  all_goals try casesm* Option vec_
  all_goals try (with_reducible contradiction)
  all_goals try simp only [Option.get!_some,List.contains_iff_mem] at *
  all_goals try injections
  all_goals subst_vars
  all_goals first
    | exact VectorResultAllowed.unary (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    | exact VectorResultAllowed.binary (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    | exact VectorResultAllowed.convert (by assumption) (by assumption) (by assumption) (by assumption)
    | exact VectorResultAllowed.unary_trap (by assumption) (by assumption) (by assumption)
    | exact VectorResultAllowed.binary_trap (by assumption) (by assumption) (by assumption) (by assumption)
end Exec.Spec
