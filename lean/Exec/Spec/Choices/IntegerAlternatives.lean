import Exec.Spec.Choices.NumericDeterminism

/-! Integer alternatives are specified traps or unique values, rather than
floating-point result choices. These are general guard facts, not examples. -/
namespace Exec.Spec

theorem integer_unop_one_result {type : Inn} {op : unop_Inn} {input : uN} {results : List num_}
    (source : fun_unop_ (numtype_Inn type) (.mk_unop__0 type op) (.mk_num__0 type input) (some results)) :
    results.length = 1 := by
  cases type <;> cases source <;> rfl

/-- Division and remainder may trap (empty results); every other integer
binary operation also has at most one permitted value. -/
theorem integer_binop_at_most_one {type : Inn} {op : binop_Inn} {left right : uN} {results : List num_}
    (source : fun_binop_ (numtype_Inn type) (.mk_binop__0 type op)
      (.mk_num__0 type left) (.mk_num__0 type right) (some results)) : results.length ≤ 1 := by
  cases type <;> cases source
  all_goals try casesm* Option _
  all_goals simp [list_,OMap]

/-- The independent guarded quotient relation cannot both return and trap. -/
theorem integer_division_success_excludes_trap {width : Nat} {sign : sx} {left right value : uN}
    (success : fun_idiv_ width sign left right (some value)) :
    ¬ fun_idiv_ width sign left right none := by
  intro trapped
  cases idiv_deterministic success trapped

theorem integer_remainder_success_excludes_trap {width : Nat} {sign : sx} {left right value : uN}
    (success : fun_irem_ width sign left right (some value)) :
    ¬ fun_irem_ width sign left right none := by
  intro trapped
  cases irem_deterministic success trapped

end Exec.Spec
