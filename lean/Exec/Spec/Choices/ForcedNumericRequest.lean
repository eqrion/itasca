import Exec.Spec.NumericReplyForcing
namespace Exec.Spec

/-- A source request with at most one permitted value, allowing its specified
empty-list trap. This is independent of any implementation or selected reply. -/
def NumericRequest.Forced (request : NumericRequest) : Prop :=
  ∀ results, request.Allowed results → results.length≤1

theorem integer_unary_request_forced (type : Inn) (op : unop_Inn) (input : uN) :
    (NumericRequest.unary (numtype_Inn type) (.mk_unop__0 type op) (.mk_num__0 type input)).Forced := by
  intro results source
  cases source
  have count := integer_unop_one_result (by assumption)
  omega

theorem integer_binary_request_forced (type : Inn) (op : binop_Inn) (left right : uN) :
    (NumericRequest.binary (numtype_Inn type) (.mk_binop__0 type op) (.mk_num__0 type left) (.mk_num__0 type right)).Forced := by
  intro results source
  cases source
  exact integer_binop_at_most_one (by assumption)

def scalarFormatResize : cvtop__ → Bool
  | .mk_cvtop___3 _ _ _ => true
  | _ => false

theorem numeric_conversion_at_most_one {source target : numtype} {op : cvtop__} {input : num_} {results : List num_}
    (relation : fun_cvtop__ source target op input (some results)) (nonresize : scalarFormatResize op=false) :
    results.length≤1 := by
  cases relation
  all_goals try { simp [scalarFormatResize] at nonresize }
  all_goals try casesm* Option _
  all_goals simp [list_,OMap]
  all_goals split <;> simp

theorem conversion_request_forced (source target : numtype) (op : cvtop__) (input : num_)
    (nonresize : scalarFormatResize op=false) : (NumericRequest.convert source target op input).Forced := by
  intro results allowed
  cases allowed
  exact numeric_conversion_at_most_one (by assumption) nonresize

theorem float_sign_unary_request_forced (type : Fnn) (op : unop_Fnn) (input : fN)
    (sign : op=.ABS ∨ op=.NEG) :
    (NumericRequest.unary (numtype_Fnn type) (.mk_unop__1 type op) (.mk_num__1 type input)).Forced := by
  intro results source
  cases source
  cases type <;> rcases sign with rfl | rfl
  all_goals cases_type fun_unop_
  all_goals rfl

theorem float_copysign_request_forced (type : Fnn) (left right : fN) :
    (NumericRequest.binary (numtype_Fnn type) (.mk_binop__1 type .COPYSIGN) (.mk_num__1 type left) (.mk_num__1 type right)).Forced := by
  intro results source
  cases source
  cases type
  all_goals cases_type fun_binop_
  all_goals rfl
end Exec.Spec
