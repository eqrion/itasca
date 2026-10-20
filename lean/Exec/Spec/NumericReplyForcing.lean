import Exec.Spec.Choices.Selection
import Exec.Spec.Choices.IntegerAlternatives
namespace Exec.Spec

theorem numeric_reply_forced {results : List num_} {left right : Option num_}
    (short : results.length≤1) (first : NumericReplyAllowed results left) (second : NumericReplyAllowed results right) :
    left=right := by
  cases results with
  | nil => exact (first.1.mpr rfl).trans (second.1.mpr rfl).symm
  | cons value rest =>
    have empty : rest=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at short; omega)
    cases empty
    cases left <;> cases right <;> simp_all [NumericReplyAllowed]

theorem chosen_numeric_of_forced_reply {choices : NumericChoices} (admissible : choices.Admissible)
    (occurrence : Nat) {request : NumericRequest} {results : List num_} {reply : Option num_}
    (source : request.Allowed results) (short : results.length≤1) (permitted : NumericReplyAllowed results reply) :
    ChosenNumeric choices occurrence request reply := by
  have chosen : ChosenNumeric choices occurrence request (choices occurrence request results) := .selected results source
  have same := numeric_reply_forced short (admissible occurrence request results source) permitted
  rw [same] at chosen
  exact chosen

theorem integer_unary_reply_forced {type : Inn} {op : unop_Inn} {input : uN} {results : List num_}
    {left right : Option num_}
    (source : fun_unop_ (numtype_Inn type) (.mk_unop__0 type op) (.mk_num__0 type input) (some results))
    (first : NumericReplyAllowed results left) (second : NumericReplyAllowed results right) : left=right :=
  numeric_reply_forced (by rw [integer_unop_one_result source]) first second

theorem integer_binary_reply_forced {type : Inn} {op : binop_Inn} {leftInput rightInput : uN}
    {results : List num_} {left right : Option num_}
    (source : fun_binop_ (numtype_Inn type) (.mk_binop__0 type op)
      (.mk_num__0 type leftInput) (.mk_num__0 type rightInput) (some results))
    (first : NumericReplyAllowed results left) (second : NumericReplyAllowed results right) : left=right :=
  numeric_reply_forced (integer_binop_at_most_one source) first second
end Exec.Spec
