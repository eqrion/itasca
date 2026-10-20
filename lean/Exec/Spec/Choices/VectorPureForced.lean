import Exec.Spec.Choices.VectorPureWitness
import Exec.Spec.Choices.VectorForced
import Exec.Spec.Choices.ChosenPure
namespace Exec.Spec

/-- Existing generated integer SIMD reductions retain the fixed vector policy;
this adapter recovers its primitive witness from the reduction itself. -/
theorem chosen_vector_nonfloat_pure (occurrence : Nat) {before after : List admininstr}
    (source : Step_pure before after) (request : VectorRequest) (reply : Option vec_)
    (input : before=request.instructions) (output : after=vectorOutput reply)
    (integer : match request with
      | .unary _ op _ => vectorUnaryFloat op = false
      | .binary _ op _ _ => vectorBinaryFloat op = false
      | .convert _ _ _ _ => False) :
    ChosenVector firstVectorChoice occurrence request reply := by
  have allowed := vector_pure_reply_witness source request reply input output
  apply chosen_vector_from_first occurrence allowed
  cases request <;> exact first_vector_reply_nonfloat allowed integer
end Exec.Spec
